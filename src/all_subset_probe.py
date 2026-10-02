#!/usr/bin/env python3
"""Complete two-variable closed-mode check over every source/deletion pair.

Every pair (T,S) with T a deletion subset of source S is enumerated.  Across a
nine-clause universe this is 3^9 = 19,683 pairs, including SAT and UNSAT sources.
The truth-table oracle, circuit evaluation, edit-local update, and ordinary proof
replay are checked independently at their respective interfaces.
"""
from __future__ import annotations

import argparse
import csv
import json
import resource
import time
from pathlib import Path

from certificates import verify
from oracle import all_clauses, satisfying_masks
from survival import compile_survival
from survival_producer import closure_certificate


def submasks(mask: int):
    current = mask
    while True:
        yield current
        if current == 0:
            return
        current = (current - 1) & mask


def run(out: Path) -> None:
    if out.exists():
        raise FileExistsError(f"output already exists: {out}")
    out.mkdir(parents=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    clauses = all_clauses(2)
    ids = [f"a{i}" for i in range(len(clauses))]
    fields = [
        "source_mask", "target_mask", "source_unsat", "target_unsat",
        "closed_accept", "witness_rechecked", "incremental_match",
    ]
    totals = {
        "source_formulas": 0,
        "sat_sources": 0,
        "unsat_sources": 0,
        "source_target_pairs": 0,
        "target_unsat": 0,
        "closed_accept": 0,
        "closed_mismatch": 0,
        "witnesses_rechecked": 0,
        "incremental_full_evaluation_matches": 0,
    }
    with (out / "all-subsets.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for source_mask in range(1 << len(clauses)):
            source = {ids[i]: clauses[i] for i in range(len(clauses)) if source_mask >> i & 1}
            source_unsat = not bool(satisfying_masks(source.values(), 2))
            totals["source_formulas"] += 1
            totals["unsat_sources" if source_unsat else "sat_sources"] += 1
            circuit = compile_survival(source, closure_certificate(source))
            source_evaluation = circuit.evaluate(source)
            if circuit.survives(source_evaluation) != source_unsat:
                raise AssertionError("closed source result disagrees with the truth-table oracle")
            for target_mask in submasks(source_mask):
                target = {ids[i]: clauses[i] for i in range(len(clauses)) if target_mask >> i & 1}
                target_unsat = not bool(satisfying_masks(target.values(), 2))
                full = circuit.evaluate(target)
                closed_accept = circuit.survives(full)
                mismatch = closed_accept != target_unsat
                if mismatch:
                    raise AssertionError("closed deletion result disagrees with the truth-table oracle")
                witness_rechecked = 0
                if closed_accept:
                    verify(target, circuit.reconstruct(full))
                    witness_rechecked = 1
                updated = circuit.update(source_evaluation, target)
                incremental_match = updated.values == full.values
                if not incremental_match:
                    raise AssertionError("edit-local update disagrees with full evaluation")
                writer.writerow({
                    "source_mask": source_mask,
                    "target_mask": target_mask,
                    "source_unsat": int(source_unsat),
                    "target_unsat": int(target_unsat),
                    "closed_accept": int(closed_accept),
                    "witness_rechecked": witness_rechecked,
                    "incremental_match": int(incremental_match),
                })
                totals["source_target_pairs"] += 1
                totals["target_unsat"] += int(target_unsat)
                totals["closed_accept"] += int(closed_accept)
                totals["closed_mismatch"] += int(mismatch)
                totals["witnesses_rechecked"] += witness_rechecked
                totals["incremental_full_evaluation_matches"] += int(incremental_match)
    if totals["source_target_pairs"] != 3 ** len(clauses):
        raise AssertionError("source/deletion pair count is not 3^|U|")
    summary = {
        "dimension": 2,
        "clause_universe": len(clauses),
        "selection": "all source formulas and every deletion subset of each source; no sampling",
        "totals": totals,
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "randomness": "none",
        "maturity": "complete finite enumeration for the stated source/deletion family",
    }
    (out / "all-subsets-summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    run(parser.parse_args().out)
