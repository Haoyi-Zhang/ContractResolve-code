"""End-to-end edit cases for single proofs, trace circuits, and closed circuits."""
from __future__ import annotations

import argparse
import json
import resource
import time
from pathlib import Path

from certificates import reusable, verify
from oracle import satisfying_masks
from producer import solve
from survival import compile_survival
from survival_producer import closure_certificate, trace_certificate


def variables(formula: dict[str, list[int]]) -> int:
    return max((abs(x) for c in formula.values() for x in c), default=0)


def run(inputs: Path, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    cases = json.loads(inputs.read_text())
    rows = []
    for case in cases:
        source, target = case["source"], case["target"]
        n = max(variables(source), variables(target))
        source_answer = solve(source, max_variables=max(n, 1))
        if source_answer["status"] != "unsat":
            raise AssertionError("source case must be UNSAT")
        single_checked = verify(source, source_answer["certificate"])
        packets = []
        for subset in case["proof_subsets"]:
            fragment_source = {k: source[k] for k in subset}
            answer = solve(fragment_source, max_variables=max(n, 1))
            if answer["status"] != "unsat":
                raise AssertionError("proof subset must be UNSAT")
            verify(source, answer["certificate"])
            packets.append(answer["certificate"])
        trace = compile_survival(source, trace_certificate(source, packets))
        closed = compile_survival(source, closure_certificate(source))
        target_unsat = not bool(satisfying_masks(target.values(), n))
        retained = {k: v for k, v in source.items() if k in target and target[k] == v}
        retained_unsat = not bool(satisfying_masks(retained.values(), n))
        trace_eval, closed_eval = trace.evaluate(target), closed.evaluate(target)
        single = reusable(single_checked, target)
        trace_accept, closed_accept = trace.survives(trace_eval), closed.survives(closed_eval)
        if closed_accept != retained_unsat:
            raise AssertionError("closed result disagrees with retained-source oracle")
        if any((single, trace_accept, closed_accept)) and not target_unsat:
            raise AssertionError("accepted case is satisfiable")
        trace_witness = trace.reconstruct(trace_eval) if trace_accept else None
        closed_witness = closed.reconstruct(closed_eval) if closed_accept else None
        if trace_witness is not None:
            verify(target, trace_witness)
        if closed_witness is not None:
            verify(target, closed_witness)
        rows.append({
            "case": case["case"],
            "variables": n,
            "source_clauses": len(source),
            "target_clauses": len(target),
            "target_status": "unsat" if target_unsat else "sat",
            "retained_source_status": "unsat" if retained_unsat else "sat",
            "single_accept": single,
            "trace_accept": trace_accept,
            "closed_accept": closed_accept,
            "single_support": single_checked.support,
            "trace_stats": trace.stats(),
            "closed_stats": closed.stats(),
            "trace_witness": trace_witness,
            "closed_witness": closed_witness,
            "trace_failure_cut": None if trace_accept else trace.blocking_cut(trace_eval),
            "closed_failure_cut": None if closed_accept else closed.blocking_cut(closed_eval),
        })
    summary = {
        "cases": rows,
        "counts": {
            "total": len(rows),
            "target_unsat": sum(x["target_status"] == "unsat" for x in rows),
            "single_accept": sum(x["single_accept"] for x in rows),
            "trace_accept": sum(x["trace_accept"] for x in rows),
            "closed_accept": sum(x["closed_accept"] for x in rows),
            "trace_repairs_over_single": sum(x["trace_accept"] and not x["single_accept"] for x in rows),
            "closed_repairs_over_trace": sum(x["closed_accept"] and not x["trace_accept"] for x in rows),
        },
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "maturity": "hand-written Boolean contract cases; not RTL or device validation",
    }
    (out / "survival-contract-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--inputs", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    run(a.inputs, a.out)
