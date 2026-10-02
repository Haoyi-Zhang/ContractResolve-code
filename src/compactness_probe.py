"""Structured family showing exponential proof supports in a polynomial circuit."""
from __future__ import annotations

import argparse
import itertools
import json
import resource
import time
from pathlib import Path

from certificates import verify
from survival import compile_survival
from survival_producer import duplicate_unit_chain


def one_choice_target(source: dict[str, list[int]], choices: tuple[str, ...]) -> dict[str, list[int]]:
    target = {"bad": source["bad"]}
    for i, which in enumerate(choices, 1):
        sid = f"{which}{i:03d}"
        target[sid] = source[sid]
    return target


def run(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    rows = []
    total_witnesses = 0
    total_negative_checks = 0
    for k in (2, 4, 8, 12, 16, 24, 32, 48, 64):
        source, cert = duplicate_unit_chain(k)
        circuit = compile_survival(source, cert)
        all_x = one_choice_target(source, tuple("x" for _ in range(k)))
        base_eval = circuit.evaluate(all_x)
        if not circuit.survives(base_eval):
            raise AssertionError("baseline chain does not survive")
        verify(all_x, circuit.reconstruct(base_eval)); total_witnesses += 1

        checks = []
        if k <= 12:
            checks.extend(itertools.product(("x", "y"), repeat=k))
        else:
            checks.extend([
                tuple("y" for _ in range(k)),
                tuple("x" if i % 2 == 0 else "y" for i in range(k)),
                tuple("y" if i % 3 == 0 else "x" for i in range(k)),
            ])
            for i in range(min(k, 32)):
                c = ["x"] * k; c[i] = "y"; checks.append(tuple(c))
        seen = set()
        for choices in checks:
            if choices in seen:
                continue
            seen.add(choices)
            target = one_choice_target(source, choices)
            ev = circuit.evaluate(target)
            if not circuit.survives(ev):
                raise AssertionError("one-of-two support unexpectedly failed")
            verify(target, circuit.reconstruct(ev)); total_witnesses += 1

        for i in range(1, min(k, 32) + 1):
            target = dict(all_x)
            target.pop(f"x{i:03d}")
            ev = circuit.evaluate(target)
            if circuit.survives(ev):
                raise AssertionError("missing both duplicate units should block proof")
            cut = circuit.blocking_cut(ev)
            if f"x{i:03d}" not in cut and f"y{i:03d}" not in cut:
                raise AssertionError("failure cut omitted missing unit alternatives")
            total_negative_checks += 1
        no_bad = {k2: v for k2, v in all_x.items() if k2 != "bad"}
        if circuit.survives(circuit.evaluate(no_bad)):
            raise AssertionError("bad-clause deletion should block proof")
        total_negative_checks += 1

        all_y = one_choice_target(source, tuple("y" for _ in range(k)))
        updated = circuit.update(base_eval, all_y)
        full = circuit.evaluate(all_y)
        if updated.values != full.values:
            raise AssertionError("incremental/full mismatch")
        stats = circuit.stats()
        rows.append({
            "k": k,
            "minimal_retained_supports": str(1 << k),
            "source_axioms": len(source),
            "schemas": stats["schemas"],
            "circuit_gates": stats["gates"],
            "max_depth": stats["max_depth"],
            "exhaustive_one_choice_assignments": (1 << k) if k <= 12 else 0,
            "selected_one_choice_assignments": len(seen),
            "all_x_to_all_y_changed_leaves": updated.changed_leaves,
            "all_x_to_all_y_recomputed_gates": updated.recomputed_gates,
        })
    summary = {
        "family": "duplicate-unit resolution chain",
        "definition": "two exact source axioms for each positive unit and one all-negative clause",
        "support_count_argument": "each of k units independently chooses one of two retained source IDs",
        "rows": rows,
        "witnesses_rechecked": total_witnesses,
        "negative_checks": total_negative_checks,
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "randomness": "none",
        "maturity": "general counting argument plus bounded implementation checks",
    }
    (out / "compactness-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.out)
