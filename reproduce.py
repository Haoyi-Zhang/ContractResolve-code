#!/usr/bin/env python3
"""Bounded four-core reproduction with exact semantic comparisons.

Run from any working directory. Only the Python standard library and bundled
inputs are used. Each experiment itself is single-worker; the runner schedules
at most four independent children concurrently. Resource timings are
observations and are never exact-match tests. The output directory must not
already exist; no published result is overwritten.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parent
VOLATILE = {"peak_rss_kib"}
MAX_WORKERS = 4
PER_CHILD_TIMEOUT_SECONDS = 180


def stable(obj: Any) -> Any:
    if isinstance(obj, dict):
        return {
            key: stable(value)
            for key, value in obj.items()
            if key not in VOLATILE and not key.endswith("_seconds")
        }
    if isinstance(obj, list):
        return [stable(value) for value in obj]
    return obj


def run_child(
    name: str,
    arguments: list[str],
    out: Path,
    env: dict[str, str],
) -> dict[str, Any]:
    started = time.perf_counter()
    stdout_path = out / "logs" / f"{name}.stdout.txt"
    stderr_path = out / "logs" / f"{name}.stderr.txt"
    with stdout_path.open("w") as stdout, stderr_path.open("w") as stderr:
        try:
            result = subprocess.run(
                [sys.executable, *arguments],
                cwd=ROOT,
                env=env,
                stdout=stdout,
                stderr=stderr,
                timeout=PER_CHILD_TIMEOUT_SECONDS,
                check=False,
            )
            code = result.returncode
        except subprocess.TimeoutExpired:
            code = 124
    return {
        "name": name,
        "arguments": arguments,
        "exit_code": code,
        "wall_seconds": time.perf_counter() - started,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("reproduced-results"))
    parser.add_argument(
        "--no-compare",
        action="store_true",
        help="generate only; do not compare bundled scientific results",
    )
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists():
        parser.error("output already exists; choose a fresh directory")
    out.mkdir(parents=True)
    (out / "logs").mkdir()

    env = {
        **os.environ,
        "PYTHONPATH": str(ROOT / "src"),
        "OMP_NUM_THREADS": "1",
        "OPENBLAS_NUM_THREADS": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    parallel_commands: list[tuple[str, list[str]]] = [
        ("tests", ["-m", "unittest", "discover", "-s", "tests", "-v"]),
        (
            "example",
            [
                "src/check.py",
                "--source",
                "inputs/example-source.json",
                "--certificate",
                "inputs/example-proof.json",
                "--target",
                "inputs/example-target.json",
            ],
        ),
        ("horn", ["src/horn_probe.py", "--out", str(out / "horn")]),
        (
            "exhaustive",
            ["src/pilot.py", "--out", str(out / "exhaustive"), "--start", "0", "--stop", "512"],
        ),
        ("rat", ["src/rat_probe.py", "--out", str(out / "rat")]),
        ("selectors", ["src/activation_probe.py", "--out", str(out / "selectors")]),
        (
            "contracts",
            [
                "src/contract_probe.py",
                "--inputs",
                "inputs/contract-cases.json",
                "--out",
                str(out / "contracts"),
            ],
        ),
        ("survival", ["src/survival_probe.py", "--out", str(out / "survival")]),
        ("all-subsets", ["src/all_subset_probe.py", "--out", str(out / "all-subsets")]),
        ("threevar", ["src/three_var_probe.py", "--out", str(out / "threevar")]),
        ("compactness", ["src/compactness_probe.py", "--out", str(out / "compactness")]),
        ("depth", ["src/depth_probe.py", "--out", str(out / "depth")]),
        (
            "survival-contracts",
            [
                "src/survival_contract_probe.py",
                "--inputs",
                "inputs/survival-contract-cases.json",
                "--out",
                str(out / "survival-contracts"),
            ],
        ),
    ]
    claim_command = (
        "claim-audit",
        ["src/result_audit.py", "--results", str(out), "--out", str(out / "claim-audit")],
    )

    order = [name for name, _ in parallel_commands] + [claim_command[0]]
    begun = time.perf_counter()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    run_by_name: dict[str, dict[str, Any]] = {}

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {
            executor.submit(run_child, name, arguments, out, env): name
            for name, arguments in parallel_commands
        }
        for future in as_completed(futures):
            run = future.result()
            run_by_name[run["name"]] = run

    failed = [run for run in run_by_name.values() if run["exit_code"] != 0]
    if not failed:
        name, arguments = claim_command
        run_by_name[name] = run_child(name, arguments, out, env)
        if run_by_name[name]["exit_code"] != 0:
            failed.append(run_by_name[name])

    runs = [run_by_name[name] for name in order if name in run_by_name]
    if failed:
        report = {
            "success": False,
            "workers": MAX_WORKERS,
            "per_child_timeout_seconds": PER_CHILD_TIMEOUT_SECONDS,
            "runs": runs,
        }
        (out / "reproduction.json").write_text(json.dumps(report, indent=2) + "\n")
        print("one or more children failed; inspect output logs", file=sys.stderr)
        return 1

    compared: list[str] = []
    if not args.no_compare:
        for family in (
            "exhaustive",
            "rat",
            "selectors",
            "contracts",
            "survival",
            "all-subsets",
            "threevar",
            "compactness",
            "depth",
            "survival-contracts",
            "horn",
            "claim-audit",
        ):
            expected_root = ROOT / "results" / family
            expected = sorted(
                path.relative_to(expected_root)
                for path in expected_root.rglob("*")
                if path.is_file()
            )
            actual = sorted(
                path.relative_to(out / family)
                for path in (out / family).rglob("*")
                if path.is_file()
            )
            if not expected or expected != actual:
                raise RuntimeError(f"{family}: file-set mismatch")
            for relative in expected:
                bundled = expected_root / relative
                reproduced = out / family / relative
                if bundled.suffix == ".json":
                    same = stable(json.loads(bundled.read_text())) == stable(
                        json.loads(reproduced.read_text())
                    )
                else:
                    same = bundled.read_bytes() == reproduced.read_bytes()
                if not same:
                    raise RuntimeError(f"{family}/{relative}: scientific result changed")
                compared.append(f"{family}/{relative}")

    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    child_cpu = (
        usage_after.ru_utime
        + usage_after.ru_stime
        - usage_before.ru_utime
        - usage_before.ru_stime
    )
    for run in runs:
        run["arguments"] = [item.replace(str(out), "<output>") for item in run["arguments"]]
    summary = {
        "success": True,
        "workers": MAX_WORKERS,
        "per_child_timeout_seconds": PER_CHILD_TIMEOUT_SECONDS,
        "scientific_results_match": None if args.no_compare else True,
        "compared_files": compared,
        "runs": runs,
        "wall_seconds": time.perf_counter() - begun,
        "child_cpu_seconds": child_cpu,
        "boundary": "Reproducibility is not a machine-checked general proof, independent peer review, or a novelty result.",
    }
    (out / "reproduction.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
