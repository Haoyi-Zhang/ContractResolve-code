"""Tests for version-aware survival circuits and proof reconstruction."""
from __future__ import annotations

import sys
from pathlib import Path

SRC = Path(__file__).resolve().parents[1] / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

import copy
import itertools
import unittest
from dataclasses import replace

from certificates import Rejected, verify
from producer import solve
from survival import compile_survival
from survival_producer import closure_certificate, duplicate_unit_chain, trace_certificate


class SurvivalTests(unittest.TestCase):
    def test_single_trace_survives_irrelevant_addition(self):
        source = {"request": [1], "rule": [-1, 2], "bad": [-2]}
        packet = solve(source)["certificate"]
        circuit = compile_survival(source, trace_certificate(source, [packet]))
        target = {**source, "mode": [3]}
        ev = circuit.evaluate(target)
        self.assertTrue(circuit.survives(ev))
        verify(target, circuit.reconstruct(ev))

    def test_duplicate_axiom_repairs_deleted_chosen_support(self):
        source = {"request": [1], "rule_a": [-1, 2],
                  "rule_b": [-1, 2], "bad": [-2]}
        packet = solve(source)["certificate"]
        chosen = {n["source"] for n in packet["nodes"] if n["kind"] == "axiom"}
        removed = next(x for x in ("rule_a", "rule_b") if x in chosen)
        target = {k: v for k, v in source.items() if k != removed}
        circuit = compile_survival(source, trace_certificate(source, [packet]))
        ev = circuit.evaluate(target)
        self.assertTrue(circuit.survives(ev))
        checked = verify(target, circuit.reconstruct(ev))
        self.assertEqual(checked.conclusion, ())
        self.assertNotIn(removed, {k for k, _ in checked.support})

    def test_closed_certificate_exact_for_every_subset(self):
        source = {"a": [1], "b": [-1], "c": [2]}
        circuit = compile_survival(source, closure_certificate(source))
        keys = sorted(source)
        for mask in range(1 << len(keys)):
            target = {k: source[k] for i, k in enumerate(keys) if mask >> i & 1}
            expected = "a" in target and "b" in target
            ev = circuit.evaluate(target)
            self.assertEqual(circuit.survives(ev), expected)
            if expected:
                verify(target, circuit.reconstruct(ev))

    def test_same_id_body_replacement_deactivates_leaf(self):
        source = {"a": [1], "b": [-1]}
        circuit = compile_survival(source, closure_certificate(source))
        ev = circuit.evaluate({"a": [2], "b": [-1]})
        self.assertFalse(circuit.survives(ev))
        self.assertIn("a", circuit.blocking_cut(ev))

    def test_incremental_update_matches_full_evaluation(self):
        source = {"a": [1], "b": [-1], "c": [2], "d": [-2]}
        circuit = compile_survival(source, closure_certificate(source))
        keys = sorted(source)
        previous = circuit.evaluate(source)
        for mask in range(1 << len(keys)):
            target = {k: source[k] for i, k in enumerate(keys) if mask >> i & 1}
            updated = circuit.update(previous, target)
            full = circuit.evaluate(target)
            self.assertEqual(updated.values, full.values)

    def test_blocking_cut_is_sufficient(self):
        source = {"a": [1], "b": [-1], "c": [2], "d": [-2]}
        circuit = compile_survival(source, closure_certificate(source))
        target = {"a": [1], "c": [2]}
        ev = circuit.evaluate(target)
        self.assertFalse(circuit.survives(ev))
        cut = set(circuit.blocking_cut(ev))
        keys = sorted(source)
        for mask in range(1 << len(keys)):
            candidate = {k: source[k] for i, k in enumerate(keys)
                         if mask >> i & 1 and k not in cut}
            self.assertFalse(circuit.survives(circuit.evaluate(candidate)))

    def test_exponential_support_family_compiles_polynomially(self):
        for k in (1, 2, 4, 8):
            source, cert = duplicate_unit_chain(k)
            circuit = compile_survival(source, cert)
            # Every one-of-two choice is a surviving proof support.
            for choices in itertools.product(("x", "y"), repeat=k):
                target = {"bad": source["bad"]}
                for i, which in enumerate(choices, 1):
                    sid = f"{which}{i:03d}"
                    target[sid] = source[sid]
                ev = circuit.evaluate(target)
                self.assertTrue(circuit.survives(ev))
                verify(target, circuit.reconstruct(ev))
            self.assertLess(circuit.stats()["gates"], 100 * k * k + 20)

    def test_closed_certificate_rejects_omitted_schema(self):
        source = {"a": [1], "b": [-1]}
        cert = closure_certificate(source)
        cert["schemas"].pop()
        with self.assertRaises(Rejected):
            compile_survival(source, cert)

    def test_schema_mutation_rejected(self):
        source = {"a": [1], "b": [-1]}
        cert = closure_certificate(source)
        bad = copy.deepcopy(cert)
        bad["schemas"][0]["clause"] = [2]
        with self.assertRaises(Rejected):
            compile_survival(source, bad)

    def test_closed_sat_source_with_explicit_empty_root_is_false(self):
        source = {"a": [1]}
        circuit = compile_survival(source, closure_certificate(source))
        evaluation = circuit.evaluate(source)
        self.assertFalse(circuit.survives(evaluation))

    def test_closed_certificate_rejects_omitted_source_axiom(self):
        source = {"a": [1], "b": [-1]}
        cert = closure_certificate(source)
        cert["axioms"].pop()
        with self.assertRaises(Rejected):
            compile_survival(source, cert)

    def test_closed_certificate_rejects_omitted_resolvent_clause(self):
        source = {"a": [1, 2], "b": [-1]}
        cert = closure_certificate(source, root=[3])
        cert["clauses"] = [c for c in cert["clauses"] if c != [2]]
        cert["schemas"] = [s for s in cert["schemas"]
                           if s["left"] != [2] and s["right"] != [2]
                           and s["clause"] != [2]]
        with self.assertRaises(Rejected):
            compile_survival(source, cert)

    def test_gate_bound_is_checked_before_allocation(self):
        source = {f"a{i:02d}": [i] for i in range(1, 22)}
        cert = {
            "mode": "trace",
            "axioms": [{"source": sid, "clause": body}
                       for sid, body in sorted(source.items())],
            "clauses": [body for _, body in sorted(source.items())],
            "schemas": [],
            "root": [1],
            "max_depth": 100_000,
        }
        with self.assertRaises(Rejected):
            compile_survival(source, cert)

    def test_malformed_evaluation_is_rejected(self):
        source = {"a": [1], "b": [-1]}
        circuit = compile_survival(source, closure_certificate(source))
        evaluation = circuit.evaluate(source)
        with self.assertRaises(Rejected):
            circuit.survives(replace(evaluation, values=evaluation.values[:-1]))
        bad_values = (1,) + evaluation.values[1:]
        with self.assertRaises(Rejected):
            circuit.update(replace(evaluation, values=bad_values), source)

    def test_cross_circuit_evaluation_is_rejected(self):
        source = {"a": [1], "b": [-1]}
        first = compile_survival(source, closure_certificate(source))
        second = compile_survival(source, closure_certificate(source))
        evaluation = first.evaluate(source)
        with self.assertRaises(Rejected):
            second.survives(evaluation)

    def test_stats_match_exact_gate_and_edge_formula(self):
        source = {"a": [1], "b": [-1], "c": [2]}
        circuit = compile_survival(source, closure_certificate(source))
        stats = circuit.stats()
        n, m, s, d = (stats["leaf_gates"], stats["clauses"],
                      stats["schemas"], stats["max_depth"])
        self.assertEqual(stats["gates"], n + (d + 1) * m + d * s)
        self.assertEqual(stats["edges"], n + d * m + 3 * d * s)
        self.assertEqual(stats["edges"], sum(len(g.parents) for g in circuit.gates))

    def test_sequential_incremental_updates_match_full_evaluation(self):
        source = {"a": [1], "b": [-1], "c": [2], "d": [-2]}
        circuit = compile_survival(source, closure_certificate(source))
        targets = [
            source,
            {"a": [1], "b": [-1], "c": [2]},
            {"a": [1], "c": [2], "d": [-2]},
            {"a": [9], "b": [-1], "d": [-2]},
            {},
            source,
        ]
        previous = circuit.evaluate(targets[0])
        for target in targets[1:]:
            previous = circuit.update(previous, target)
            self.assertEqual(previous.values, circuit.evaluate(target).values)

    def test_nonempty_root_is_reconstructed_and_rechecked(self):
        source = {"a": [1], "b": [-1, 2]}
        circuit = compile_survival(source, closure_certificate(source, root=[2]))
        evaluation = circuit.evaluate(source)
        self.assertTrue(circuit.survives(evaluation))
        checked = verify(source, circuit.reconstruct(evaluation))
        self.assertEqual(checked.conclusion, (2,))

    def test_false_root_cannot_be_reconstructed(self):
        source = {"a": [1]}
        circuit = compile_survival(source, closure_certificate(source))
        with self.assertRaises(Rejected):
            circuit.reconstruct(circuit.evaluate(source))

    def test_true_root_has_no_blocking_cut(self):
        source = {"a": [1], "b": [-1]}
        circuit = compile_survival(source, closure_certificate(source))
        with self.assertRaises(Rejected):
            circuit.blocking_cut(circuit.evaluate(source))

    def test_noncanonical_evaluation_snapshot_is_rejected(self):
        source = {"a": [1], "b": [-1]}
        circuit = compile_survival(source, closure_certificate(source))
        evaluation = circuit.evaluate(source)
        duplicate = (("a", (1,)), ("a", (1,)), ("b", (-1,)))
        with self.assertRaises(Rejected):
            circuit.survives(replace(evaluation, target=duplicate))
        unsorted = (("b", (-1,)), ("a", (1,)))
        with self.assertRaises(Rejected):
            circuit.survives(replace(evaluation, target=unsorted))

    def test_closed_certificate_rejects_short_fixed_point_depth(self):
        source = {"a": [1], "b": [-1]}
        cert = closure_certificate(source)
        cert["max_depth"] = len(cert["clauses"]) - 1
        with self.assertRaises(Rejected):
            compile_survival(source, cert)

    def test_trace_omission_is_a_false_result_not_an_admission_error(self):
        source = {"a": [1], "b": [-1]}
        cert = {
            "mode": "trace",
            "axioms": [{"source": sid, "clause": body}
                       for sid, body in sorted(source.items())],
            "clauses": [[], [-1], [1]],
            "schemas": [],
            "root": [],
            "max_depth": 3,
        }
        circuit = compile_survival(source, cert)
        self.assertFalse(circuit.survives(circuit.evaluate(source)))

    def test_trace_layer_zero_uses_only_admitted_axiom_set(self):
        source = {"a": [1]}
        cert = {
            "mode": "trace",
            "axioms": [],
            "clauses": [[1]],
            "schemas": [],
            "root": [1],
            "max_depth": 0,
        }
        circuit = compile_survival(source, cert)
        self.assertEqual(circuit.stats()["source_clauses"], 1)
        self.assertEqual(circuit.stats()["admitted_axioms"], 0)
        self.assertFalse(circuit.survives(circuit.evaluate(source)))

    def test_deep_persistence_replay_and_cut_use_iterative_traversal(self):
        source = {"e": []}
        cert = {
            "mode": "closed",
            "axioms": [{"source": "e", "clause": []}],
            "clauses": [[]],
            "schemas": [],
            "root": [],
            "max_depth": 2000,
        }
        circuit = compile_survival(source, cert)
        self.assertEqual(circuit.stats()["gates"], 2002)
        packet = circuit.reconstruct(circuit.evaluate(source))
        self.assertEqual(len(packet["nodes"]), 1)
        self.assertEqual(verify(source, packet).conclusion, ())
        self.assertEqual(circuit.blocking_cut(circuit.evaluate({})), ("e",))


if __name__ == "__main__":
    unittest.main()
