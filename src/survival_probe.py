"""Exhaustive two-variable comparison of single proofs and survival circuits."""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import resource
import time
from pathlib import Path

from certificates import reusable, verify
from oracle import all_clauses, satisfying_masks
from producer import solve
from survival import compile_survival
from survival_producer import closure_certificate, trace_certificate


def run(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    clauses = all_clauses(2)
    ids = [f"a{i}" for i in range(len(clauses))]
    edit_masks = ([0] + [1 << i for i in range(9)] +
                  [(1 << i) | (1 << j) for i, j in itertools.combinations(range(9), 2)])
    fields = [
        "source_mask", "target_mask", "edit_distance", "target_unsat",
        "retained_source_unsat", "stale_accept", "single_accept", "trace_accept",
        "closed_accept", "trace_gain_over_single", "closed_gain_over_trace",
        "single_miss", "trace_miss", "closed_miss", "closed_recomputed_gates",
        "closed_total_gates",
    ]
    totals = {k: 0 for k in fields[3:14]}
    source_unsat = 0
    query_count = 0
    trace_witnesses = 0
    closed_witnesses = 0
    incremental_matches = 0
    circuit_stats = []
    first_trace_gain = None
    first_closed_gain = None
    first_failure_cut = None

    with (out / "survival-edits.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for sm in range(512):
            base = {ids[i]: clauses[i] for i in range(9) if sm >> i & 1}
            if satisfying_masks(base.values(), 2):
                continue
            source_unsat += 1
            solved = solve(base, max_variables=2)
            checked = verify(base, solved["certificate"])
            trace = compile_survival(base, trace_certificate(base, [solved["certificate"]]))
            closed = compile_survival(base, closure_certificate(base))
            base_closed = closed.evaluate(base)
            if not closed.survives(base_closed):
                raise AssertionError("closed source circuit rejected its own UNSAT source")
            circuit_stats.append({"source_mask": sm,
                                  "trace": trace.stats(), "closed": closed.stats()})
            for dm in edit_masks:
                tm = sm ^ dm
                target = {ids[i]: clauses[i] for i in range(9) if tm >> i & 1}
                retained = {k: v for k, v in base.items() if k in target and target[k] == v}
                target_unsat = not bool(satisfying_masks(target.values(), 2))
                retained_unsat = not bool(satisfying_masks(retained.values(), 2))
                single_accept = reusable(checked, target)
                trace_eval = trace.evaluate(target)
                closed_eval = closed.evaluate(target)
                trace_accept = trace.survives(trace_eval)
                closed_accept = closed.survives(closed_eval)
                if single_accept and not target_unsat:
                    raise AssertionError("single proof reuse was unsound")
                if trace_accept and not target_unsat:
                    raise AssertionError("trace survival was unsound")
                if closed_accept and not target_unsat:
                    raise AssertionError("closed survival was unsound")
                if closed_accept != retained_unsat:
                    raise AssertionError("closed certificate was not exact for retained source clauses")
                if trace_accept:
                    verify(target, trace.reconstruct(trace_eval))
                    trace_witnesses += 1
                if closed_accept:
                    verify(target, closed.reconstruct(closed_eval))
                    closed_witnesses += 1
                updated = closed.update(base_closed, target)
                if updated.values != closed_eval.values:
                    raise AssertionError("edit-local update disagrees with full evaluation")
                incremental_matches += 1

                row = {
                    "source_mask": sm,
                    "target_mask": tm,
                    "edit_distance": dm.bit_count(),
                    "target_unsat": int(target_unsat),
                    "retained_source_unsat": int(retained_unsat),
                    "stale_accept": 1,
                    "single_accept": int(single_accept),
                    "trace_accept": int(trace_accept),
                    "closed_accept": int(closed_accept),
                    "trace_gain_over_single": int(trace_accept and not single_accept),
                    "closed_gain_over_trace": int(closed_accept and not trace_accept),
                    "single_miss": int(retained_unsat and not single_accept),
                    "trace_miss": int(retained_unsat and not trace_accept),
                    "closed_miss": int(retained_unsat and not closed_accept),
                    "closed_recomputed_gates": updated.recomputed_gates,
                    "closed_total_gates": len(closed.gates),
                }
                for k in totals:
                    totals[k] += row[k]
                writer.writerow(row)
                query_count += 1
                if row["trace_gain_over_single"] and first_trace_gain is None:
                    first_trace_gain = {"source": base, "target": target,
                                        "single_support": checked.support,
                                        "trace_witness": trace.reconstruct(trace_eval)}
                if row["closed_gain_over_trace"] and first_closed_gain is None:
                    first_closed_gain = {"source": base, "target": target,
                                         "trace_schemas": len(trace.schemas),
                                         "closed_schemas": len(closed.schemas),
                                         "closed_witness": closed.reconstruct(closed_eval)}
                if not closed_accept and first_failure_cut is None:
                    first_failure_cut = {"source": base, "target": target,
                                         "cut": closed.blocking_cut(closed_eval)}

    gate_counts = [x["closed"]["gates"] for x in circuit_stats]
    schema_counts = [x["closed"]["schemas"] for x in circuit_stats]
    trace_gate_counts = [x["trace"]["gates"] for x in circuit_stats]
    summary = {
        "dimension": 2,
        "clause_universe": 9,
        "source_formulas": 512,
        "unsat_sources": source_unsat,
        "edit_radius": 2,
        "queries_from_unsat_sources": query_count,
        "totals": totals,
        "trace_witnesses_rechecked": trace_witnesses,
        "closed_witnesses_rechecked": closed_witnesses,
        "incremental_full_evaluation_matches": incremental_matches,
        "closed_gate_count": {"min": min(gate_counts), "max": max(gate_counts),
                              "mean": sum(gate_counts) / len(gate_counts)},
        "trace_gate_count": {"min": min(trace_gate_counts), "max": max(trace_gate_counts),
                             "mean": sum(trace_gate_counts) / len(trace_gate_counts)},
        "closed_schema_count": {"min": min(schema_counts), "max": max(schema_counts),
                                "mean": sum(schema_counts) / len(schema_counts)},
        "first_trace_gain": first_trace_gain,
        "first_closed_gain": first_closed_gain,
        "first_failure_cut": first_failure_cut,
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "randomness": "none; complete source family and all edits of Hamming radius at most two",
        "maturity": "finite check plus separately stated general proofs",
    }
    (out / "survival-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (out / "circuit-stats.json").write_text(json.dumps(circuit_stats, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.out)
