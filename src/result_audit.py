#!/usr/bin/env python3
"""Independently recompute claim-critical aggregates from row-level results.

This module intentionally does not import the experiment producers, the SAT
oracle, or the survival checker. It treats their emitted CSV/JSON files as data,
recomputes the principal paper counts with separate code, and fails closed on
any mismatch or violated row invariant.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any, Iterable


class AuditError(RuntimeError):
    """Raised when retained scientific evidence is internally inconsistent."""


def _json(path: Path) -> Any:
    return json.loads(path.read_text())


def _rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def _integer(row: dict[str, str], key: str) -> int:
    try:
        return int(row[key])
    except (KeyError, ValueError) as exc:
        raise AuditError(f"{key}: expected an integer field") from exc


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def _equal(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise AuditError(f"{label}: expected {expected!r}, found {actual!r}")


def _close(actual: float, expected: float, label: str, tolerance: float = 1e-12) -> None:
    if not math.isclose(actual, expected, rel_tol=tolerance, abs_tol=tolerance):
        raise AuditError(f"{label}: expected {expected!r}, found {actual!r}")


def _summary(values: Iterable[int]) -> dict[str, float | int]:
    data = list(values)
    _assert(bool(data), "cannot summarize an empty sequence")
    return {"min": min(data), "mean": sum(data) / len(data), "max": max(data)}


def _percentile(values: Iterable[int], q: float) -> float:
    data = sorted(values)
    _assert(bool(data), "cannot take a percentile of an empty sequence")
    position = (len(data) - 1) * q
    low = int(position)
    high = min(low + 1, len(data) - 1)
    fraction = position - low
    return data[low] * (1.0 - fraction) + data[high] * fraction


def _check_summary(actual: dict[str, Any], expected: dict[str, Any], label: str) -> None:
    _equal(actual["min"], expected["min"], f"{label}.min")
    _close(float(actual["mean"]), float(expected["mean"]), f"{label}.mean")
    _equal(actual["max"], expected["max"], f"{label}.max")


def _audit_circuit_stats(stats: dict[str, Any], label: str) -> None:
    n = int(stats["leaf_gates"])
    m = int(stats["clauses"])
    s = int(stats["schemas"])
    d = int(stats["max_depth"])
    expected_gates = n + (d + 1) * m + d * s
    expected_edges = n + d * m + 3 * d * s
    _equal(stats["gates"], expected_gates, f"{label}.gates")
    _equal(stats["edges"], expected_edges, f"{label}.edges")
    _equal(
        stats["leaf_gates"] + stats["and_gates"] + stats["or_gates"],
        stats["gates"],
        f"{label}.gate partition",
    )
    _equal(stats["and_gates"], d * s, f"{label}.and gates")
    _equal(stats["or_gates"], (d + 1) * m, f"{label}.or gates")


def audit(results: Path) -> dict[str, Any]:
    results = results.resolve()
    checks: list[str] = []

    # Two-variable survival family.
    survival_rows = _rows(results / "survival" / "survival-edits.csv")
    survival = _json(results / "survival" / "survival-summary.json")
    _equal(len(survival_rows), survival["queries_from_unsat_sources"], "survival row count")
    boolean_columns = [
        "target_unsat", "retained_source_unsat", "stale_accept", "single_accept",
        "trace_accept", "closed_accept", "trace_gain_over_single",
        "closed_gain_over_trace", "single_miss", "trace_miss", "closed_miss",
    ]
    for index, row in enumerate(survival_rows, 2):
        values = {key: _integer(row, key) for key in boolean_columns}
        _assert(all(value in (0, 1) for value in values.values()),
                f"survival CSV row {index}: non-Boolean flag")
        _equal(values["closed_accept"], values["retained_source_unsat"],
               f"survival CSV row {index}: closed exactness")
        _equal(values["single_miss"], int(values["retained_source_unsat"] and not values["single_accept"]),
               f"survival CSV row {index}: single miss")
        _equal(values["trace_miss"], int(values["retained_source_unsat"] and not values["trace_accept"]),
               f"survival CSV row {index}: trace miss")
        _equal(values["closed_miss"], int(values["retained_source_unsat"] and not values["closed_accept"]),
               f"survival CSV row {index}: closed miss")
        _equal(values["trace_gain_over_single"], int(values["trace_accept"] and not values["single_accept"]),
               f"survival CSV row {index}: trace gain")
        _equal(values["closed_gain_over_trace"], int(values["closed_accept"] and not values["trace_accept"]),
               f"survival CSV row {index}: closed gain")
    survival_pairs: set[tuple[int, int]] = set()
    survival_targets: dict[int, set[int]] = {}
    mask_limit = 1 << 9
    for index, row in enumerate(survival_rows, 2):
        source_mask = _integer(row, "source_mask")
        target_mask = _integer(row, "target_mask")
        _assert(0 <= source_mask < mask_limit and 0 <= target_mask < mask_limit,
                f"survival CSV row {index}: mask outside the nine-clause universe")
        pair = (source_mask, target_mask)
        _assert(pair not in survival_pairs,
                f"survival CSV row {index}: duplicate source/target pair")
        survival_pairs.add(pair)
        distance = (source_mask ^ target_mask).bit_count()
        _equal(_integer(row, "edit_distance"), distance,
               f"survival CSV row {index}: edit distance")
        _assert(distance <= 2, f"survival CSV row {index}: target outside radius two")
        survival_targets.setdefault(source_mask, set()).add(target_mask)
    _equal(len(survival_targets), survival["unsat_sources"],
           "two-variable distinct UNSAT sources")
    for source_mask, observed in survival_targets.items():
        expected = {target for target in range(mask_limit)
                    if (source_mask ^ target).bit_count() <= 2}
        _equal(observed, expected,
               f"two-variable radius-two coverage for source {source_mask}")

    derived_survival = {key: sum(_integer(row, key) for row in survival_rows)
                        for key in boolean_columns}
    for key, expected in survival["totals"].items():
        if key in derived_survival:
            _equal(derived_survival[key], expected, f"survival totals.{key}")
    stale_false = sum(_integer(row, "stale_accept") and not _integer(row, "target_unsat")
                      for row in survival_rows)
    _equal(stale_false, 2323, "stale UNSAT false accepts")
    edit_hist: dict[int, int] = {}
    for row in survival_rows:
        distance = _integer(row, "edit_distance")
        edit_hist[distance] = edit_hist.get(distance, 0) + 1
    _equal(edit_hist, {0: 417, 1: 3753, 2: 15012}, "two-variable edit histogram")
    checks.append("two-variable row-level survival counts and invariants")

    circuit_rows = _json(results / "survival" / "circuit-stats.json")
    _equal(len(circuit_rows), survival["unsat_sources"], "two-variable circuit-stat rows")
    for item in circuit_rows:
        _audit_circuit_stats(item["trace"], f"trace source {item['source_mask']}")
        _audit_circuit_stats(item["closed"], f"closed source {item['source_mask']}")
    _check_summary(_summary(item["closed"]["gates"] for item in circuit_rows),
                   survival["closed_gate_count"], "closed gate summary")
    _check_summary(_summary(item["trace"]["gates"] for item in circuit_rows),
                   survival["trace_gate_count"], "trace gate summary")
    _check_summary(_summary(item["closed"]["schemas"] for item in circuit_rows),
                   survival["closed_schema_count"], "closed schema summary")
    checks.append("exact circuit gate/edge formulas and two-variable structure summaries")

    # Every two-variable source and every deletion subset, including SAT sources.
    subset_rows = _rows(results / "all-subsets" / "all-subsets.csv")
    subset = _json(results / "all-subsets" / "all-subsets-summary.json")
    subset_totals = subset["totals"]
    _equal(len(subset_rows), subset_totals["source_target_pairs"],
           "all-subsets row count")
    _equal(len(subset_rows), 3 ** int(subset["clause_universe"]),
           "all-subsets 3^|U| pair count")
    seen_pairs: set[tuple[int, int]] = set()
    derived_subset = {
        "target_unsat": 0,
        "closed_accept": 0,
        "closed_mismatch": 0,
        "witnesses_rechecked": 0,
        "incremental_full_evaluation_matches": 0,
    }
    source_status: dict[int, int] = {}
    targets_by_source: dict[int, set[int]] = {}
    subset_mask_limit = 1 << int(subset["clause_universe"])
    for index, row in enumerate(subset_rows, 2):
        source_mask = _integer(row, "source_mask")
        target_mask = _integer(row, "target_mask")
        _assert(0 <= source_mask < subset_mask_limit and 0 <= target_mask < subset_mask_limit,
                f"all-subsets CSV row {index}: mask outside declared universe")
        pair = (source_mask, target_mask)
        _assert(pair not in seen_pairs, f"all-subsets CSV row {index}: duplicate pair")
        seen_pairs.add(pair)
        targets_by_source.setdefault(source_mask, set()).add(target_mask)
        _equal(target_mask & ~source_mask, 0,
               f"all-subsets CSV row {index}: target is not a deletion subset")
        flags = {key: _integer(row, key) for key in
                 ("source_unsat", "target_unsat", "closed_accept",
                  "witness_rechecked", "incremental_match")}
        _assert(all(value in (0, 1) for value in flags.values()),
                f"all-subsets CSV row {index}: non-Boolean flag")
        if source_mask in source_status:
            _equal(flags["source_unsat"], source_status[source_mask],
                   f"all-subsets CSV row {index}: inconsistent source status")
        else:
            source_status[source_mask] = flags["source_unsat"]
        _equal(flags["closed_accept"], flags["target_unsat"],
               f"all-subsets CSV row {index}: closed exactness")
        _equal(flags["witness_rechecked"], flags["closed_accept"],
               f"all-subsets CSV row {index}: witness replay")
        _equal(flags["incremental_match"], 1,
               f"all-subsets CSV row {index}: incremental/full agreement")
        derived_subset["target_unsat"] += flags["target_unsat"]
        derived_subset["closed_accept"] += flags["closed_accept"]
        derived_subset["closed_mismatch"] += int(
            flags["closed_accept"] != flags["target_unsat"]
        )
        derived_subset["witnesses_rechecked"] += flags["witness_rechecked"]
        derived_subset["incremental_full_evaluation_matches"] += flags["incremental_match"]
    _equal(set(source_status), set(range(subset_mask_limit)),
           "all-subsets exact source-mask coverage")
    for source_mask, observed in targets_by_source.items():
        expected: set[int] = set()
        target_mask = source_mask
        while True:
            expected.add(target_mask)
            if target_mask == 0:
                break
            target_mask = (target_mask - 1) & source_mask
        _equal(observed, expected,
               f"all-subsets exact target coverage for source {source_mask}")
    _equal(len(source_status), subset_totals["source_formulas"],
           "all-subsets distinct source count")
    _equal(sum(source_status.values()), subset_totals["unsat_sources"],
           "all-subsets UNSAT source count")
    _equal(len(source_status) - sum(source_status.values()), subset_totals["sat_sources"],
           "all-subsets SAT source count")
    for key, value in derived_subset.items():
        _equal(value, subset_totals[key], f"all-subsets totals.{key}")
    _equal(subset_totals["closed_mismatch"], 0, "all-subsets closed mismatches")
    checks.append("all two-variable source/deletion pairs, including SAT sources")

    # Three-variable deletion family.
    three_rows = _rows(results / "threevar" / "three-var-deletions.csv")
    three = _json(results / "threevar" / "three-var-summary.json")
    totals = three["totals"]
    _equal(len(three_rows), totals["queries"], "three-variable row count")
    _equal(math.comb(26, 2) + math.comb(26, 3) + math.comb(26, 4),
           totals["source_formulas"], "three-variable source formula count")
    sources = {row["source_indices"] for row in three_rows}
    _equal(len(sources), totals["unsat_sources"], "three-variable UNSAT source count")
    deletions_by_source: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    for index, row in enumerate(three_rows, 2):
        try:
            source_indices = tuple(int(x) for x in row["source_indices"].split())
            deleted_indices = tuple(int(x[1:]) for x in row["deleted_ids"].split())
        except (ValueError, KeyError) as exc:
            raise AuditError(f"three-variable CSV row {index}: malformed source/deletion identifiers") from exc
        source_size = _integer(row, "source_size")
        _equal(len(source_indices), source_size,
               f"three-variable CSV row {index}: source size")
        _assert(source_indices == tuple(sorted(set(source_indices))),
                f"three-variable CSV row {index}: noncanonical source indices")
        _assert(all(0 <= value < 26 for value in source_indices),
                f"three-variable CSV row {index}: source index outside universe")
        _assert(deleted_indices == tuple(sorted(set(deleted_indices))),
                f"three-variable CSV row {index}: noncanonical deletion identifiers")
        _assert(set(deleted_indices) <= set(source_indices),
                f"three-variable CSV row {index}: deletion outside source")
        _equal(len(deleted_indices), _integer(row, "deleted_count"),
               f"three-variable CSV row {index}: deleted count")
        bucket = deletions_by_source.setdefault(source_indices, set())
        _assert(deleted_indices not in bucket,
                f"three-variable CSV row {index}: duplicate deletion subset")
        bucket.add(deleted_indices)
        target = _integer(row, "target_unsat")
        single = _integer(row, "single_accept")
        closed = _integer(row, "closed_accept")
        miss = _integer(row, "single_miss")
        _assert(all(value in (0, 1) for value in (target, single, closed, miss)),
                f"three-variable CSV row {index}: non-Boolean flag")
        _equal(closed, target, f"three-variable CSV row {index}: closed exactness")
        _equal(miss, int(target and not single), f"three-variable CSV row {index}: single miss")
    for source_indices, observed in deletions_by_source.items():
        expected = {
            tuple(source_indices[pos] for pos in range(len(source_indices)) if mask >> pos & 1)
            for mask in range(1 << len(source_indices))
        }
        _equal(observed, expected,
               f"three-variable exact deletion coverage for source {source_indices}")

    derived_three = {
        "target_unsat": sum(_integer(row, "target_unsat") for row in three_rows),
        "single_accept": sum(_integer(row, "single_accept") for row in three_rows),
        "closed_accept": sum(_integer(row, "closed_accept") for row in three_rows),
        "single_miss": sum(_integer(row, "single_miss") for row in three_rows),
    }
    for key, value in derived_three.items():
        _equal(value, totals[key], f"three-variable totals.{key}")
    _equal(totals["closed_miss"], 0, "three-variable closed misses")
    by_deleted: dict[int, dict[str, int]] = {}
    for row in three_rows:
        deleted = _integer(row, "deleted_count")
        bucket = by_deleted.setdefault(deleted, {"queries": 0, "target_unsat": 0,
                                                 "single_miss": 0, "closed_miss": 0})
        bucket["queries"] += 1
        bucket["target_unsat"] += _integer(row, "target_unsat")
        bucket["single_miss"] += _integer(row, "single_miss")
        bucket["closed_miss"] += int(_integer(row, "target_unsat") and not _integer(row, "closed_accept"))
    _equal({str(k): v for k, v in sorted(by_deleted.items())}, three["by_deleted_count"],
           "three-variable deleted-count summary")
    checks.append("three-variable all-deletion counts and closed-mode exactness")

    # Original fragment/safe-reuse exhaustive probe.
    exhaustive_rows = _rows(results / "exhaustive" / "edits-0-512.csv")
    exhaustive = _json(results / "exhaustive" / "pilot-0-512.json")
    _equal(len(exhaustive_rows), exhaustive["queries"], "exhaustive probe rows")
    for key, expected in exhaustive["totals"].items():
        _equal(sum(_integer(row, key) for row in exhaustive_rows), expected,
               f"exhaustive totals.{key}")
    _equal(exhaustive["totals"]["false_accepts"], 0, "safe fragment false accepts")
    checks.append("independent aggregation of the original exhaustive fragment probe")

    # RAT transport negative control.
    rat_rows = _rows(results / "rat" / "rat-extensions.csv")
    rat = _json(results / "rat" / "rat-summary.json")
    _equal(len(rat_rows), rat["totals"]["extensions_checked"], "RAT extension rows")
    _equal(sum(_integer(row, "unsafe_import") for row in rat_rows),
           rat["totals"]["unsafe_imports"], "RAT unsafe imports")
    _equal(sum(_integer(row, "polarity_safe") for row in rat_rows),
           rat["totals"]["polarity_safe_extensions"], "RAT polarity-safe extensions")
    _equal(sum(_integer(row, "unsafe_import") and _integer(row, "polarity_safe")
               for row in rat_rows), rat["totals"]["polarity_rule_failures"],
           "RAT polarity rule failures")
    checks.append("RAT-transport negative-control counts")

    # Selector arithmetic and reported result.
    selectors = _json(results / "selectors" / "selector-summary.json")
    expected_assignments = selectors["formulas"] * (1 << selectors["encoded_variables"])
    _equal(selectors["assignments_checked"], expected_assignments, "selector assignment count")
    _equal(selectors["projected_equivalence_failures"], 0, "selector projection failures")
    checks.append("selector assignment arithmetic and zero-failure result")

    # Compactness family and exact generic circuit formula.
    compact = _json(results / "compactness" / "compactness-summary.json")
    witness_total = 0
    for row in compact["rows"]:
        k = int(row["k"])
        _equal(int(row["minimal_retained_supports"]), 1 << k, f"compactness k={k}: support count")
        _equal(row["source_axioms"], 2 * k + 1, f"compactness k={k}: source axioms")
        _equal(row["schemas"], k, f"compactness k={k}: schemas")
        _equal(row["max_depth"], 2 * k + 1, f"compactness k={k}: depth")
        m = 2 * k + 1  # k units, k+1 suffix clauses including the empty root
        d = row["max_depth"]
        n = row["source_axioms"]
        s = row["schemas"]
        _equal(row["circuit_gates"], n + (d + 1) * m + d * s,
               f"compactness k={k}: gate count")
        witness_total += row["selected_one_choice_assignments"]
    _equal(witness_total + len(compact["rows"]), compact["witnesses_rechecked"], "compactness witness total")
    checks.append("duplicate-unit support and circuit-size formulas")

    # Depth histograms must account for every accepted closed root.
    depth = _json(results / "depth" / "depth-summary.json")
    two_hist = {int(k): int(v) for k, v in depth["two_variable"]["root_depth_histogram"].items()}
    three_hist = {int(k): int(v) for k, v in depth["three_variable"]["root_depth_histogram"].items()}
    _equal(sum(two_hist.values()), survival["totals"]["closed_accept"], "two-variable depth total")
    _equal(sum(three_hist.values()), totals["closed_accept"], "three-variable depth total")
    _check_summary(_summary(layer for layer, count in two_hist.items() for _ in range(count)),
                   depth["two_variable"]["root_depth"], "two-variable root depth")
    _check_summary(_summary(layer for layer, count in three_hist.items() for _ in range(count)),
                   depth["three_variable"]["root_depth"], "three-variable root depth")
    checks.append("accepted-root depth histograms")

    # Contract cases: semantic table and circuit structural formulas.
    contracts = _json(results / "contracts" / "contract-summary.json")
    _equal(len(contracts["cases"]), 6, "legacy contract case count")
    _equal({case["variables"] for case in contracts["cases"]}, {2, 3, 4, 5},
           "legacy contract variable range")
    survival_contracts = _json(results / "survival-contracts" / "survival-contract-summary.json")
    _equal(len(survival_contracts["cases"]), 8, "survival contract case count")
    _equal({case["variables"] for case in survival_contracts["cases"]}, {1, 2, 3},
           "survival contract variable range")
    for case in survival_contracts["cases"]:
        _audit_circuit_stats(case["trace_stats"], f"{case['case']}.trace")
        _audit_circuit_stats(case["closed_stats"], f"{case['case']}.closed")
        _equal(case["closed_accept"], case["retained_source_status"] == "unsat",
               f"{case['case']}: closed result")
        _assert(not case["trace_accept"] or case["closed_accept"],
                f"{case['case']}: trace positive absent from closed mode")
        _equal(case["trace_witness"] is not None, bool(case["trace_accept"]),
               f"{case['case']}: trace replay presence")
        _equal(case["closed_witness"] is not None, bool(case["closed_accept"]),
               f"{case['case']}: closed replay presence")
        for label in ("trace_witness", "closed_witness"):
            witness = case[label]
            if witness is not None:
                _assert(isinstance(witness.get("nodes"), list) and witness.get("root"),
                        f"{case['case']}: malformed stored {label}")
    counts = survival_contracts["counts"]
    _equal(counts["total"], 8, "survival contract count summary")
    _equal(counts["single_accept"], sum(case["single_accept"] for case in survival_contracts["cases"]),
           "contract single accepts")
    _equal(counts["trace_accept"], sum(case["trace_accept"] for case in survival_contracts["cases"]),
           "contract trace accepts")
    _equal(counts["closed_accept"], sum(case["closed_accept"] for case in survival_contracts["cases"]),
           "contract closed accepts")
    _equal(counts["trace_repairs_over_single"], 4,
           "survival contract trace repairs over one selected proof")
    checks.append("contract-table semantics and circuit structural formulas")

    # Exact Horn specialization: complete small family and deterministic scale study.
    horn = _json(results / "horn" / "horn-summary.json")
    horn_rows = _rows(results / "horn" / "horn-exhaustive.csv")
    horn_small = horn["small_complete_family"]
    horn_totals = horn_small["totals"]
    horn_universe = int(horn_totals["clause_universe"])
    horn_limit = int(horn_small["source_size_limit"])
    horn_mask_limit = 1 << horn_universe
    expected_sources = sum(math.comb(horn_universe, size)
                           for size in range(horn_limit + 1))
    expected_pairs = sum(math.comb(horn_universe, size) * (1 << size)
                         for size in range(horn_limit + 1))
    _equal(horn_totals["source_formulas"], expected_sources,
           "Horn exhaustive source count")
    _equal(len(horn_rows), expected_pairs, "Horn exhaustive source/target pair count")
    _equal(horn_totals["source_target_pairs"], expected_pairs,
           "Horn exhaustive summary pair count")
    horn_seen: set[tuple[int, int]] = set()
    horn_derived = {key: 0 for key in (
        "target_unsat", "single_proof_accept", "horn_accept",
        "horn_oracle_mismatch", "incremental_full_mismatch",
        "witnesses_rechecked", "single_proof_misses_recovered",
    )}
    horn_source_status: dict[int, int] = {}
    horn_sources: set[int] = set()
    horn_targets_by_source: dict[int, set[int]] = {}
    for index, row in enumerate(horn_rows, 2):
        source_mask = _integer(row, "source_mask")
        target_mask = _integer(row, "target_mask")
        _assert(0 <= source_mask < horn_mask_limit and 0 <= target_mask < horn_mask_limit,
                f"Horn exhaustive CSV row {index}: mask outside the 20-clause universe")
        pair = (source_mask, target_mask)
        _assert(pair not in horn_seen, f"Horn exhaustive CSV row {index}: duplicate pair")
        horn_seen.add(pair)
        horn_sources.add(source_mask)
        horn_targets_by_source.setdefault(source_mask, set()).add(target_mask)
        _equal(target_mask & ~source_mask, 0,
               f"Horn exhaustive CSV row {index}: target is not a deletion subset")
        _equal(_integer(row, "source_size"), source_mask.bit_count(),
               f"Horn exhaustive CSV row {index}: source size")
        _assert(source_mask.bit_count() <= horn_limit,
                f"Horn exhaustive CSV row {index}: source exceeds declared size limit")
        flags = {key: _integer(row, key) for key in
                 ("source_unsat", "target_unsat", "single_accept",
                  "horn_accept", "incremental_match")}
        _assert(all(value in (0, 1) for value in flags.values()),
                f"Horn exhaustive CSV row {index}: non-Boolean flag")
        _equal(flags["horn_accept"], flags["target_unsat"],
               f"Horn exhaustive CSV row {index}: exactness")
        _assert(not flags["single_accept"] or flags["horn_accept"],
                f"Horn exhaustive CSV row {index}: selected proof accepted a false Horn root")
        _equal(flags["incremental_match"], 1,
               f"Horn exhaustive CSV row {index}: incremental/full mismatch")
        if source_mask in horn_source_status:
            _equal(flags["source_unsat"], horn_source_status[source_mask],
                   f"Horn exhaustive CSV row {index}: inconsistent source status")
        else:
            horn_source_status[source_mask] = flags["source_unsat"]
        horn_derived["target_unsat"] += flags["target_unsat"]
        horn_derived["single_proof_accept"] += flags["single_accept"]
        horn_derived["horn_accept"] += flags["horn_accept"]
        horn_derived["horn_oracle_mismatch"] += int(
            flags["horn_accept"] != flags["target_unsat"])
        horn_derived["incremental_full_mismatch"] += int(
            flags["incremental_match"] != 1)
        horn_derived["witnesses_rechecked"] += flags["horn_accept"]
        horn_derived["single_proof_misses_recovered"] += int(
            flags["horn_accept"] and not flags["single_accept"])
        _assert(_integer(row, "gates") > 0 and _integer(row, "edges") >= 0,
                f"Horn exhaustive CSV row {index}: invalid circuit size")
        _assert(row["strategy"] in {"acyclic", "layered"},
                f"Horn exhaustive CSV row {index}: invalid strategy")
    expected_horn_sources = {
        mask for mask in range(horn_mask_limit) if mask.bit_count() <= horn_limit
    }
    _equal(horn_sources, expected_horn_sources, "Horn exhaustive exact source-mask coverage")
    for source_mask, observed in horn_targets_by_source.items():
        expected_targets: set[int] = set()
        target_mask = source_mask
        while True:
            expected_targets.add(target_mask)
            if target_mask == 0:
                break
            target_mask = (target_mask - 1) & source_mask
        _equal(observed, expected_targets,
               f"Horn exhaustive exact deletion coverage for source {source_mask}")
    _equal(len(horn_sources), expected_sources, "Horn exhaustive distinct sources")
    _equal(sum(horn_source_status.values()), horn_totals["source_unsat"],
           "Horn exhaustive UNSAT source count")
    for key, value in horn_derived.items():
        _equal(value, horn_totals[key], f"Horn exhaustive totals.{key}")
    _equal(horn_totals["source_acyclic"] + horn_totals["source_layered"],
           horn_totals["source_formulas"], "Horn source strategy partition")
    checks.append("complete three-variable Horn deletion family and replay exactness")

    horn_scale_rows = _rows(results / "horn" / "horn-scale-queries.csv")
    horn_scale = horn["scalable_contract_graphs"]
    scale_totals = horn_scale["totals"]
    _equal(len(horn_scale_rows), scale_totals["queries"], "Horn scale row count")
    scale_items: dict[int, dict[str, Any]] = {}
    for item in horn_scale["instances"]:
        instance = int(item["instance"])
        _assert(instance not in scale_items,
                f"Horn scale summary: duplicate instance {instance}")
        scale_items[instance] = item
    expected_instance_ids = set(range(int(scale_totals["instances"])))
    _equal(set(scale_items), expected_instance_ids,
           "Horn scale exact instance identifier set")

    scale_by_instance: dict[int, dict[str, Any]] = {}
    seen_scale_queries: set[tuple[int, int]] = set()
    for index, row in enumerate(horn_scale_rows, 2):
        instance = _integer(row, "instance")
        query = _integer(row, "query")
        _assert(instance in scale_items,
                f"Horn scale CSV row {index}: unknown instance {instance}")
        item = scale_items[instance]
        pair = (instance, query)
        _assert(pair not in seen_scale_queries,
                f"Horn scale CSV row {index}: duplicate query")
        seen_scale_queries.add(pair)
        flags = {key: _integer(row, key) for key in
                 ("target_unsat", "single_accept", "horn_accept", "incremental_match")}
        _assert(all(value in (0, 1) for value in flags.values()),
                f"Horn scale CSV row {index}: non-Boolean flag")
        _equal(flags["horn_accept"], flags["target_unsat"],
               f"Horn scale CSV row {index}: exactness")
        _assert(not flags["single_accept"] or flags["horn_accept"],
                f"Horn scale CSV row {index}: selected proof false accept")
        _equal(flags["incremental_match"], 1,
               f"Horn scale CSV row {index}: incremental/full mismatch")
        bucket = scale_by_instance.setdefault(instance, {
            "queries": 0, "target_unsat": 0, "single_proof_accept": 0,
            "horn_accept": 0, "incremental_full_mismatches": 0,
            "query_ids": set(), "recomputed": [], "changed": [],
        })
        bucket["query_ids"].add(query)
        bucket["queries"] += 1
        bucket["target_unsat"] += flags["target_unsat"]
        bucket["single_proof_accept"] += flags["single_accept"]
        bucket["horn_accept"] += flags["horn_accept"]
        bucket["incremental_full_mismatches"] += int(not flags["incremental_match"])
        circuit_gates = _integer(row, "circuit_gates")
        _equal(circuit_gates, int(item["gates"]),
               f"Horn scale CSV row {index}: circuit gate count for instance {instance}")
        recomputed = _integer(row, "recomputed_gates")
        changed = _integer(row, "changed_leaves")
        _assert(0 <= recomputed <= circuit_gates,
                f"Horn scale CSV row {index}: invalid recomputation count")
        _assert(0 <= changed <= int(item["source_clauses"]),
                f"Horn scale CSV row {index}: invalid changed-leaf count")
        bucket["recomputed"].append(recomputed)
        bucket["changed"].append(changed)
    _equal(len(scale_by_instance), scale_totals["instances"],
           "Horn scale instance count")
    _equal(set(scale_by_instance), expected_instance_ids,
           "Horn scale row instance identifier set")
    for instance in sorted(scale_items):
        item = scale_items[instance]
        bucket = scale_by_instance[instance]
        _equal(bucket["query_ids"], set(range(int(item["queries"]))),
               f"Horn scale instance {instance}: exact query identifier set")
        _equal(bucket["queries"], item["queries"], f"Horn scale instance {instance}: queries")
        _equal(bucket["target_unsat"], item["target_unsat"],
               f"Horn scale instance {instance}: target UNSAT")
        _equal(bucket["single_proof_accept"], item["single_proof_accept"],
               f"Horn scale instance {instance}: selected proof accepts")
        _equal(bucket["horn_accept"], item["target_unsat"],
               f"Horn scale instance {instance}: Horn accepts")
        _equal(bucket["incremental_full_mismatches"], 0,
               f"Horn scale instance {instance}: update mismatches")
        layers = int(item["layers"])
        width = int(item["width"])
        alternatives = int(item["alternatives"])
        variables = (layers + 1) * width
        rules = layers * width * alternatives
        constraints = 4
        clauses = width + rules + constraints
        expected_gates = clauses + variables + rules + constraints + 1
        expected_edges = width + 4 * rules + 3 * constraints
        _equal(item["variables"], variables,
               f"Horn scale instance {instance}: variables")
        _equal(item["source_clauses"], clauses,
               f"Horn scale instance {instance}: clauses")
        _equal(item["gates"], expected_gates,
               f"Horn scale instance {instance}: exact acyclic gate count")
        _equal(item["edges"], expected_edges,
               f"Horn scale instance {instance}: exact acyclic edge count")
        _equal(item["single_proof_misses_recovered"],
               item["target_unsat"] - item["single_proof_accept"],
               f"Horn scale instance {instance}: recovered misses")
        recomputed = bucket["recomputed"]
        changed = bucket["changed"]
        gates = int(item["gates"])
        _close(sum(changed) / len(changed), float(item["mean_changed_leaves"]),
               f"Horn scale instance {instance}: mean changed leaves")
        _close(sum(recomputed) / len(recomputed), float(item["mean_recomputed_gates"]),
               f"Horn scale instance {instance}: mean recomputed gates")
        _close(_percentile(recomputed, 0.50), float(item["p50_recomputed_gates"]),
               f"Horn scale instance {instance}: p50 recomputed gates")
        _close(_percentile(recomputed, 0.95), float(item["p95_recomputed_gates"]),
               f"Horn scale instance {instance}: p95 recomputed gates")
        _equal(max(recomputed), item["max_recomputed_gates"],
               f"Horn scale instance {instance}: maximum recomputed gates")
        _close(sum(recomputed) / (len(recomputed) * gates),
               float(item["mean_recomputed_fraction"]),
               f"Horn scale instance {instance}: mean recomputed fraction")
        _close(_percentile(recomputed, 0.95) / gates,
               float(item["p95_recomputed_fraction"]),
               f"Horn scale instance {instance}: p95 recomputed fraction")
    _equal(sum(item["queries"] for item in horn_scale["instances"]),
           scale_totals["queries"], "Horn scale total queries")
    _equal(sum(item["target_unsat"] for item in horn_scale["instances"]),
           scale_totals["target_unsat"], "Horn scale total UNSAT")
    _equal(sum(item["single_proof_accept"] for item in horn_scale["instances"]),
           scale_totals["single_proof_accept"], "Horn scale selected proof total")
    _equal(sum(item["single_proof_misses_recovered"] for item in horn_scale["instances"]),
           scale_totals["single_proof_misses_recovered"], "Horn scale recovered total")
    _equal(scale_totals["oracle_mismatches"], 0, "Horn scale oracle mismatches")
    _equal(scale_totals["incremental_full_mismatches"], 0,
           "Horn scale incremental/full mismatches")
    checks.append("scalable acyclic Horn contract graphs, size formulas, and edit-local updates")

    key_claims = {
        "references_not_audited_here": "Bibliographic audit is maintained separately; this script audits experiment evidence.",
        "two_variable_queries": len(survival_rows),
        "two_variable_all_source_deletion_pairs": len(subset_rows),
        "two_variable_all_source_deletion_mismatches": subset_totals["closed_mismatch"],
        "two_variable_retained_unsat": derived_survival["retained_source_unsat"],
        "two_variable_single_misses": derived_survival["single_miss"],
        "two_variable_closed_misses": derived_survival["closed_miss"],
        "three_variable_queries": len(three_rows),
        "three_variable_retained_unsat": derived_three["target_unsat"],
        "three_variable_single_misses": derived_three["single_miss"],
        "three_variable_closed_misses": totals["closed_miss"],
        "stale_unsat_false_accepts": stale_false,
        "rat_unsafe_imports": rat["totals"]["unsafe_imports"],
        "selector_assignments": selectors["assignments_checked"],
        "compactness_k64_supports": str(1 << 64),
        "horn_complete_pairs": len(horn_rows),
        "horn_complete_unsat_targets": horn_totals["target_unsat"],
        "horn_complete_selected_proof_misses": horn_totals["single_proof_misses_recovered"],
        "horn_scale_queries": scale_totals["queries"],
        "horn_scale_selected_proof_misses": scale_totals["single_proof_misses_recovered"],
        "horn_scale_max_variables": max(item["variables"] for item in horn_scale["instances"]),
        "horn_scale_max_clauses": max(item["source_clauses"] for item in horn_scale["instances"]),
    }
    return {
        "success": True,
        "audit_independence": (
            "Aggregates are recomputed from emitted rows without importing experiment, "
            "oracle, certificate, or circuit modules. This detects result/report drift, "
            "not a common parser/runtime defect or a general theorem error."
        ),
        "checks": checks,
        "key_claims": key_claims,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, required=True,
                        help="result root containing survival/, threevar/, and other families")
    parser.add_argument("--out", type=Path, required=True,
                        help="fresh output directory for claim-audit.json")
    args = parser.parse_args()
    if args.out.exists():
        parser.error("output already exists; choose a fresh directory")
    args.out.mkdir(parents=True)
    try:
        report = audit(args.results)
    except (AuditError, OSError, json.JSONDecodeError) as exc:
        report = {"success": False, "error": str(exc)}
        (args.out / "claim-audit.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        return 1
    (args.out / "claim-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
