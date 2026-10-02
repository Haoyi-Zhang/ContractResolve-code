"""Complete small Horn audit and deterministic scalable contract-graph study."""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import random
import resource
import time
from pathlib import Path

from certificates import verify
from horn import compile_horn
from horn_oracle import retained_horn_unsat


def canonical(values):
    return tuple(sorted(values))


def horn_clause_universe(variables: int) -> list[tuple[int, ...]]:
    atoms = list(range(1, variables + 1))
    clauses: set[tuple[int, ...]] = set()
    for mask in range(1 << variables):
        clauses.add(canonical(-atoms[i] for i in range(variables) if mask >> i & 1))
    for head in atoms:
        others = [atom for atom in atoms if atom != head]
        for mask in range(1 << len(others)):
            clauses.add(canonical(
                [head] + [-others[i] for i in range(len(others)) if mask >> i & 1]
            ))
    return sorted(clauses)


def percentile(values: list[int], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    position = (len(ordered) - 1) * q
    low = int(position)
    high = min(low + 1, len(ordered) - 1)
    fraction = position - low
    return ordered[low] * (1.0 - fraction) + ordered[high] * fraction


def exhaustive(out: Path) -> dict:
    universe = horn_clause_universe(3)
    assert len(universe) == 20
    totals = {
        "clause_universe": len(universe),
        "source_formulas": 0,
        "source_unsat": 0,
        "source_acyclic": 0,
        "source_layered": 0,
        "source_target_pairs": 0,
        "target_unsat": 0,
        "single_proof_accept": 0,
        "horn_accept": 0,
        "horn_oracle_mismatch": 0,
        "incremental_full_mismatch": 0,
        "witnesses_rechecked": 0,
        "single_proof_misses_recovered": 0,
    }
    with (out / "horn-exhaustive.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=[
            "source_mask", "target_mask", "source_size", "strategy",
            "source_unsat", "target_unsat", "single_accept", "horn_accept",
            "gates", "edges", "changed_leaves", "recomputed_gates",
            "incremental_match",
        ])
        writer.writeheader()
        for size in range(4):
            for indices in itertools.combinations(range(len(universe)), size):
                source_mask = sum(1 << index for index in indices)
                source = {f"c{index:02d}": list(universe[index]) for index in indices}
                circuit = compile_horn(source)
                stats = circuit.stats()
                totals["source_formulas"] += 1
                totals[f"source_{circuit.strategy}"] += 1
                base = circuit.evaluate(source)
                source_unsat = circuit.survives(base)
                support = None
                if source_unsat:
                    totals["source_unsat"] += 1
                    support = verify(source, circuit.reconstruct(base))
                keys = sorted(source)
                for keep_mask in range(1 << len(keys)):
                    target = {sid: source[sid] for bit, sid in enumerate(keys)
                              if keep_mask >> bit & 1}
                    target_mask = sum(1 << int(sid[1:]) for sid in target)
                    oracle = retained_horn_unsat(source, target)
                    full = circuit.evaluate(target)
                    updated = circuit.update(base, target)
                    accepted = circuit.survives(full)
                    single = bool(
                        support is not None
                        and all(sid in target and tuple(target[sid]) == body
                                for sid, body in support.support)
                    )
                    totals["source_target_pairs"] += 1
                    totals["target_unsat"] += int(oracle)
                    totals["single_proof_accept"] += int(single)
                    totals["horn_accept"] += int(accepted)
                    totals["horn_oracle_mismatch"] += int(accepted != oracle)
                    totals["incremental_full_mismatch"] += int(updated.values != full.values)
                    if accepted:
                        verify(target, circuit.reconstruct(full))
                        totals["witnesses_rechecked"] += 1
                    if accepted and not single:
                        totals["single_proof_misses_recovered"] += 1
                    writer.writerow({
                        "source_mask": source_mask,
                        "target_mask": target_mask,
                        "source_size": size,
                        "strategy": circuit.strategy,
                        "source_unsat": int(source_unsat),
                        "target_unsat": int(oracle),
                        "single_accept": int(single),
                        "horn_accept": int(accepted),
                        "gates": stats["gates"],
                        "edges": stats["edges"],
                        "changed_leaves": updated.changed_leaves,
                        "recomputed_gates": updated.recomputed_gates,
                        "incremental_match": int(updated.values == full.values),
                    })
    return totals


def contract_graph(layers: int, width: int, alternatives: int) -> dict[str, list[int]]:
    if layers < 1 or width < 2 or alternatives < 1:
        raise ValueError("invalid contract graph dimensions")

    def atom(layer: int, column: int) -> int:
        return layer * width + column + 1

    source: dict[str, list[int]] = {}
    for column in range(width):
        source[f"fact-{column:04d}"] = [atom(0, column)]
    for layer in range(1, layers + 1):
        for column in range(width):
            head = atom(layer, column)
            for alternative in range(alternatives):
                left = atom(layer - 1, (column + alternative) % width)
                right = atom(layer - 1, (column + alternative + 1) % width)
                source[f"rule-{layer:04d}-{column:04d}-{alternative:02d}"] = list(
                    canonical([-left, -right, head])
                )
    constraint_columns = sorted({0, width // 3, (2 * width) // 3, width - 1})
    for index, column in enumerate(constraint_columns):
        source[f"deny-{index:02d}"] = [-atom(layers, column)]
    return source


def mutate(target: dict[str, list[int]], source: dict[str, list[int]], rng: random.Random,
           step: int, fresh_base: int) -> None:
    source_ids = sorted(source)
    operation = step % 5
    if operation in {0, 1, 2}:
        sid = source_ids[rng.randrange(len(source_ids))]
        if operation == 0:
            if sid in target:
                del target[sid]
            else:
                target[sid] = source[sid]
        elif operation == 1:
            if sid in target and target[sid] != source[sid]:
                target[sid] = source[sid]
            else:
                target[sid] = [fresh_base + (step % 10_000)]
        else:
            target[sid] = source[sid]
    else:
        sid = f"new-{step % 97:03d}"
        if sid in target:
            del target[sid]
        else:
            target[sid] = [fresh_base + 20_000 + (step % 97)]


def scalable(out: Path) -> dict:
    configurations = [
        (8, 8, 2, 128),
        (16, 16, 2, 128),
        (32, 16, 3, 128),
        (64, 32, 3, 128),
        (128, 32, 4, 48),
    ]
    rows = []
    with (out / "horn-scale-queries.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=[
            "instance", "query", "target_unsat", "single_accept", "horn_accept",
            "changed_leaves", "recomputed_gates", "circuit_gates", "incremental_match",
        ])
        writer.writeheader()
        for instance_index, (layers, width, alternatives, queries) in enumerate(configurations):
            source = contract_graph(layers, width, alternatives)
            start_compile = time.perf_counter()
            circuit = compile_horn(source)
            compile_seconds = time.perf_counter() - start_compile
            stats = circuit.stats()
            if circuit.strategy != "acyclic":
                raise AssertionError("generated contract graph must be acyclic")
            base = circuit.evaluate(source)
            if not circuit.survives(base):
                raise AssertionError("generated source must be UNSAT")
            selected = verify(source, circuit.reconstruct(base))
            target = dict(source)
            previous = base
            rng = random.Random(20260920 + instance_index)
            fresh_base = (layers + 1) * width + 1
            exact_positive = single_positive = 0
            mismatches = update_mismatches = 0
            replayed = max_witness_nodes = 0
            recomputed: list[int] = []
            changed: list[int] = []
            update_seconds = full_seconds = oracle_seconds = replay_seconds = 0.0
            for query in range(queries):
                mutate(target, source, rng, query, fresh_base)
                start = time.perf_counter()
                updated = circuit.update(previous, target)
                update_seconds += time.perf_counter() - start
                start = time.perf_counter()
                full = circuit.evaluate(target)
                full_seconds += time.perf_counter() - start
                start = time.perf_counter()
                oracle = retained_horn_unsat(source, target)
                oracle_seconds += time.perf_counter() - start
                accepted = circuit.survives(updated)
                single = all(sid in target and tuple(target[sid]) == body
                             for sid, body in selected.support)
                mismatches += int(accepted != oracle)
                update_mismatches += int(updated.values != full.values)
                exact_positive += int(accepted)
                single_positive += int(single)
                recomputed.append(updated.recomputed_gates)
                changed.append(updated.changed_leaves)
                if accepted and (query == 0 or query == queries - 1):
                    start = time.perf_counter()
                    packet = circuit.reconstruct(updated)
                    verify(target, packet)
                    replay_seconds += time.perf_counter() - start
                    replayed += 1
                    max_witness_nodes = max(max_witness_nodes, len(packet["nodes"]))
                writer.writerow({
                    "instance": instance_index,
                    "query": query,
                    "target_unsat": int(oracle),
                    "single_accept": int(single),
                    "horn_accept": int(accepted),
                    "changed_leaves": updated.changed_leaves,
                    "recomputed_gates": updated.recomputed_gates,
                    "circuit_gates": stats["gates"],
                    "incremental_match": int(updated.values == full.values),
                })
                previous = updated
            rows.append({
                "instance": instance_index,
                "layers": layers,
                "width": width,
                "alternatives": alternatives,
                "variables": stats["variables"],
                "source_clauses": len(source),
                "gates": stats["gates"],
                "edges": stats["edges"],
                "queries": queries,
                "target_unsat": exact_positive,
                "single_proof_accept": single_positive,
                "single_proof_misses_recovered": exact_positive - single_positive,
                "oracle_mismatches": mismatches,
                "incremental_full_mismatches": update_mismatches,
                "witnesses_replayed": replayed,
                "max_witness_nodes": max_witness_nodes,
                "mean_changed_leaves": sum(changed) / len(changed),
                "mean_recomputed_gates": sum(recomputed) / len(recomputed),
                "p50_recomputed_gates": percentile(recomputed, 0.50),
                "p95_recomputed_gates": percentile(recomputed, 0.95),
                "max_recomputed_gates": max(recomputed),
                "mean_recomputed_fraction": sum(recomputed) / (len(recomputed) * stats["gates"]),
                "p95_recomputed_fraction": percentile(recomputed, 0.95) / stats["gates"],
                "compile_wall_seconds": compile_seconds,
                "update_wall_seconds": update_seconds,
                "full_wall_seconds": full_seconds,
                "oracle_wall_seconds": oracle_seconds,
                "replay_wall_seconds": replay_seconds,
            })
    return {
        "selection": "five deterministic acyclic conjunctive-Horn contract graphs; fixed edit stream; no sampling of query outcomes",
        "instances": rows,
        "totals": {
            "instances": len(rows),
            "variables": sum(row["variables"] for row in rows),
            "source_clauses": sum(row["source_clauses"] for row in rows),
            "queries": sum(row["queries"] for row in rows),
            "target_unsat": sum(row["target_unsat"] for row in rows),
            "single_proof_accept": sum(row["single_proof_accept"] for row in rows),
            "single_proof_misses_recovered": sum(row["single_proof_misses_recovered"] for row in rows),
            "oracle_mismatches": sum(row["oracle_mismatches"] for row in rows),
            "incremental_full_mismatches": sum(row["incremental_full_mismatches"] for row in rows),
            "witnesses_replayed": sum(row["witnesses_replayed"] for row in rows),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        parser.error("output directory already exists")
    args.out.mkdir(parents=True)
    cpu0, wall0 = time.process_time(), time.perf_counter()
    small = exhaustive(args.out)
    scale = scalable(args.out)
    summary = {
        "small_complete_family": {
            "dimension": 3,
            "source_size_limit": 3,
            "selection": "every Horn source of size zero through three over the complete 20-clause universe, with every deletion subset",
            "totals": small,
        },
        "scalable_contract_graphs": scale,
        "cpu_seconds": time.process_time() - cpu0,
        "wall_seconds": time.perf_counter() - wall0,
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "workers": 1,
        "randomness": "fixed Python PRNG seeds listed in source; no outcome-dependent selection",
        "maturity": "complete finite validation for the small family plus deterministic generated contract-graph scaling evidence",
        "boundary": "generated Horn contracts are not RTL, firmware, devices, or industrial SAT benchmarks",
    }
    (args.out / "horn-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
