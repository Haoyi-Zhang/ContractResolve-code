"""Derivation-depth and edit-local cone profiles for the bounded closed circuits."""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import resource
import time
from collections import Counter, defaultdict
from pathlib import Path

from oracle import all_clauses, satisfying_masks
from producer import solve
from survival import compile_survival
from survival_producer import closure_certificate


def earliest_root_layer(circuit, evaluation) -> int:
    root_ci = circuit.clauses.index(circuit.root_clause)
    for layer, gates in enumerate(circuit.clause_gate):
        if evaluation.values[gates[root_ci]]:
            return layer
    raise AssertionError("true root absent from all layers")


def stats(values: list[float]) -> dict[str, float]:
    return {"min": min(values), "mean": sum(values) / len(values), "max": max(values)}


def two_variable() -> dict:
    clauses = all_clauses(2)
    ids = [f"a{i}" for i in range(len(clauses))]
    edit_masks = ([0] + [1 << i for i in range(9)] +
                  [(1 << i) | (1 << j) for i, j in itertools.combinations(range(9), 2)])
    hist = Counter()
    by_distance = defaultdict(lambda: {"queries": 0, "retained_unsat": 0,
                                       "recomputed": [], "fraction": []})
    for sm in range(512):
        source = {ids[i]: clauses[i] for i in range(9) if sm >> i & 1}
        if satisfying_masks(source.values(), 2):
            continue
        circuit = compile_survival(source, closure_certificate(source))
        base = circuit.evaluate(source)
        for dm in edit_masks:
            target = {ids[i]: clauses[i] for i in range(9) if (sm ^ dm) >> i & 1}
            full = circuit.evaluate(target)
            updated = circuit.update(base, target)
            distance = dm.bit_count()
            group = by_distance[distance]
            group["queries"] += 1
            group["recomputed"].append(updated.recomputed_gates)
            group["fraction"].append(updated.recomputed_gates / len(circuit.gates))
            if circuit.survives(full):
                group["retained_unsat"] += 1
                hist[earliest_root_layer(circuit, full)] += 1
    return {
        "root_depth_histogram": {str(k): hist[k] for k in sorted(hist)},
        "root_depth": stats([d for d, n in hist.items() for _ in range(n)]),
        "by_edit_distance": {
            str(k): {
                "queries": v["queries"],
                "retained_unsat": v["retained_unsat"],
                "recomputed_gates": stats(v["recomputed"]),
                "recomputed_fraction": stats(v["fraction"]),
            } for k, v in sorted(by_distance.items())
        },
    }


def three_variable() -> dict:
    clauses = [c for c in all_clauses(3) if c]
    hist = Counter()
    by_size = defaultdict(lambda: {"sources": 0, "unsat_sources": 0, "queries": 0,
                                   "target_unsat": 0, "recomputed": [], "fraction": []})
    by_deleted_count = defaultdict(lambda: {"queries": 0, "target_unsat": 0,
                                             "recomputed": [], "fraction": []})
    for size in range(2, 5):
        for indices in itertools.combinations(range(len(clauses)), size):
            group = by_size[size]
            group["sources"] += 1
            source = {f"a{i:02d}": clauses[i] for i in indices}
            if satisfying_masks(source.values(), 3):
                continue
            group["unsat_sources"] += 1
            # Keep the same admission precondition as the primary campaign.
            solve(source, max_variables=3)
            circuit = compile_survival(source, closure_certificate(source))
            base = circuit.evaluate(source)
            keys = sorted(source)
            for deletion_mask in range(1 << len(keys)):
                deleted = [sid for bit, sid in enumerate(keys)
                           if deletion_mask >> bit & 1]
                target = {sid: body for sid, body in source.items()
                          if sid not in deleted}
                full = circuit.evaluate(target)
                updated = circuit.update(base, target)
                group["queries"] += 1
                group["recomputed"].append(updated.recomputed_gates)
                fraction = updated.recomputed_gates / len(circuit.gates)
                group["fraction"].append(fraction)
                deletion_group = by_deleted_count[len(deleted)]
                deletion_group["queries"] += 1
                deletion_group["recomputed"].append(updated.recomputed_gates)
                deletion_group["fraction"].append(fraction)
                if circuit.survives(full):
                    group["target_unsat"] += 1
                    deletion_group["target_unsat"] += 1
                    hist[earliest_root_layer(circuit, full)] += 1
    return {
        "root_depth_histogram": {str(k): hist[k] for k in sorted(hist)},
        "root_depth": stats([d for d, n in hist.items() for _ in range(n)]),
        "by_source_size": {
            str(k): {
                "sources": v["sources"], "unsat_sources": v["unsat_sources"],
                "queries": v["queries"], "target_unsat": v["target_unsat"],
                "recomputed_gates": stats(v["recomputed"]),
                "recomputed_fraction": stats(v["fraction"]),
            } for k, v in sorted(by_size.items())
        },
        "by_deleted_count": {
            str(k): {
                "queries": v["queries"], "target_unsat": v["target_unsat"],
                "recomputed_gates": stats(v["recomputed"]),
                "recomputed_fraction": stats(v["fraction"]),
            } for k, v in sorted(by_deleted_count.items())
        },
    }


def run(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    summary = {
        "two_variable": two_variable(),
        "three_variable": three_variable(),
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "randomness": "none",
        "interpretation": "earliest true circuit layer and conservatively reconsidered fanout; not proof-search time",
    }
    (out / "depth-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    run(parser.parse_args().out)
