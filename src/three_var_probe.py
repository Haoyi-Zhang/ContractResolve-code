"""Complete deletion campaign for all UNSAT 3-variable CNFs of size at most four."""
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
from survival_producer import closure_certificate


def run(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    clauses = [c for c in all_clauses(3) if c]  # exclude trivial empty-clause sources
    fields = ["source_size", "source_indices", "deleted_count", "deleted_ids",
              "target_unsat", "single_accept", "closed_accept", "single_miss",
              "closed_recomputed_gates", "closed_total_gates"]
    totals = {"source_formulas": 0, "unsat_sources": 0, "queries": 0,
              "target_unsat": 0, "single_accept": 0, "closed_accept": 0,
              "single_miss": 0, "closed_miss": 0,
              "closed_witnesses_rechecked": 0,
              "incremental_full_evaluation_matches": 0}
    gates: list[int] = []
    schemas: list[int] = []
    by_deleted_count: dict[int, dict[str, int]] = {}
    first_gain = None
    with (out / "three-var-deletions.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for size in range(2, 5):
            for indices in itertools.combinations(range(len(clauses)), size):
                totals["source_formulas"] += 1
                source = {f"a{i:02d}": clauses[i] for i in indices}
                if satisfying_masks(source.values(), 3):
                    continue
                totals["unsat_sources"] += 1
                solved = solve(source, max_variables=3)
                checked = verify(source, solved["certificate"])
                closed = compile_survival(source, closure_certificate(source))
                base_eval = closed.evaluate(source)
                if not closed.survives(base_eval):
                    raise AssertionError("closed circuit rejected source")
                gates.append(len(closed.gates)); schemas.append(len(closed.schemas))
                keys = sorted(source)
                for deletion_mask in range(1 << len(keys)):
                    deleted = [sid for bit, sid in enumerate(keys)
                               if deletion_mask >> bit & 1]
                    target = {sid: body for sid, body in source.items()
                              if sid not in deleted}
                    target_unsat = not bool(satisfying_masks(target.values(), 3))
                    single = reusable(checked, target)
                    full = closed.evaluate(target)
                    accept = closed.survives(full)
                    if accept != target_unsat:
                        raise AssertionError("closed deletion criterion not exact")
                    if single and not target_unsat:
                        raise AssertionError("single proof reuse unsound")
                    if accept:
                        verify(target, closed.reconstruct(full))
                        totals["closed_witnesses_rechecked"] += 1
                    updated = closed.update(base_eval, target)
                    if updated.values != full.values:
                        raise AssertionError("incremental mismatch")
                    totals["incremental_full_evaluation_matches"] += 1
                    miss = int(target_unsat and not single)
                    row = {
                        "source_size": size,
                        "source_indices": " ".join(map(str, indices)),
                        "deleted_count": len(deleted),
                        "deleted_ids": " ".join(deleted),
                        "target_unsat": int(target_unsat),
                        "single_accept": int(single),
                        "closed_accept": int(accept),
                        "single_miss": miss,
                        "closed_recomputed_gates": updated.recomputed_gates,
                        "closed_total_gates": len(closed.gates),
                    }
                    writer.writerow(row)
                    totals["queries"] += 1
                    totals["target_unsat"] += int(target_unsat)
                    totals["single_accept"] += int(single)
                    totals["closed_accept"] += int(accept)
                    totals["single_miss"] += miss
                    totals["closed_miss"] += int(target_unsat and not accept)
                    group = by_deleted_count.setdefault(
                        len(deleted), {"queries": 0, "target_unsat": 0,
                                       "single_miss": 0, "closed_miss": 0})
                    group["queries"] += 1
                    group["target_unsat"] += int(target_unsat)
                    group["single_miss"] += miss
                    group["closed_miss"] += int(target_unsat and not accept)
                    if miss and first_gain is None:
                        first_gain = {"source": source, "target": target,
                                      "single_support": checked.support,
                                      "closed_witness": closed.reconstruct(full)}
    summary = {
        "dimension": 3,
        "nonempty_clause_universe": len(clauses),
        "source_size_range": [2, 4],
        "selection": ("all source formulas in the size range and all deletion "
                      "subsets of every UNSAT source; no sampling"),
        "totals": totals,
        "by_deleted_count": {str(k): v for k, v in sorted(by_deleted_count.items())},
        "closed_gate_count": {"min": min(gates), "max": max(gates),
                              "mean": sum(gates) / len(gates)},
        "closed_schema_count": {"min": min(schemas), "max": max(schemas),
                                "mean": sum(schemas) / len(schemas)},
        "first_gain": first_gain,
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "randomness": "none",
        "maturity": "complete finite enumeration for the stated bounded family",
    }
    (out / "three-var-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.out)
