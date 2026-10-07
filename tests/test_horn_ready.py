"""File-free ordering and Horn regressions; no campaign or timing driver.

The scan reference recomputes readiness from predecessor membership, without
indegrees, a ready queue, a heap, or a historical implementation copy.
"""
from dataclasses import replace
from itertools import combinations, permutations, product
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
import horn


def scan_order(variables, clauses):
    pending = set(variables)
    edges = {(a, clause.head) for clause in clauses if clause.head is not None
             for a in clause.antecedents}
    order = []
    while pending:
        candidates = [v for v in pending if not any(b == v and a in pending for a, b in edges)]
        if not candidates:
            return None
        chosen = min(candidates)
        pending.remove(chosen)
        order.append(chosen)
    return tuple(order)


def graph_clauses(module, edges):
    return tuple(module.HornClause(f'e{i}', tuple(sorted((-a, b))), (a,), b)
                 for i, (a, b) in enumerate(edges))


def forward_graphs():
    possible = tuple(combinations((1, 2, 3, 4), 2))
    for mask in range(64):
        yield tuple(edge for i, edge in enumerate(possible) if mask >> i & 1)


def small_sources():
    return (
        {}, {'empty': []}, {'fact': [1]}, {'deny': [-1]},
        {'fact': [1], 'deny': [-1]},
        {'fact': [1], 'r12': [-1, 2], 'r23': [-2, 3], 'deny': [-3]},
        {'fact': [3], 'r31': [-3, 1], 'deny': [-1], 'isolated': [4]},
        {'a': [1], 'b': [2], 'join': [-2, -1, 3], 'tail': [-3, 4], 'deny': [-4]},
        {'fact': [1], 'first': [-1, 2], 'second': [-1, 2], 'deny': [-2]},
        {'a': [1], 'b': [1], 'rule': [-1, 2], 'deny': [-2]},
        {'a': [1], 'r12': [-1, 2], 'r34': [-3, 4], 'deny': [-2]},
        {'fact': [1], 'r12': [-1, 2], 'r21': [-2, 1], 'deny': [-2]},
        {'r12': [-1, 2], 'r21': [-2, 1], 'deny': [-2]},
        {'empty': [], 'a': [1], 'r12': [-1, 2], 'r21': [-2, 1]},
        {'fact': [1], 'rule': [-1, 2], 'unreachable': [-3]},
        {'a': [1], 'b': [2], 'deny1': [-1], 'deny2': [-2]},
        {'a': [1], 'b': [2], 'c': [3], 'join': [-3, -2, -1, 4], 'deny': [-4]},
        {'a': [1], 'b': [2], 'r14': [-1, 4], 'r24': [-2, 4], 'deny': [-4]},
        {'a': [3], 'r31': [-3, 1], 'r12': [-1, 2], 'deny': [-2]},
        {'a-empty': [], 'a': [1], 'b': [2], 'c': [3], 'a-wide': [-3, -2, -1, 4],
         'z-short': [-1, 4], 'deny': [-4], 'duplicate-b': [2]},
    )


def literal_unsat(source, target):
    active = [body for sid, body in source.items() if sid in target and target[sid] == body]
    atoms = sorted({abs(lit) for body in active for lit in body})
    for bits in product((False, True), repeat=len(atoms)):
        assignment = dict(zip(atoms, bits))
        if all(any(assignment[abs(lit)] == (lit > 0) for lit in body) for body in active):
            return False
    return True


def circuit_snapshot(circuit):
    """Owner identities differ per instance; all serialized semantics are exact."""
    return {'source': circuit.source, 'variables': circuit.variables,
            'clauses': tuple((c.source, c.body, c.antecedents, c.head) for c in circuit.clauses),
            'gates': tuple((g.kind, g.parents, g.payload) for g in circuit.gates),
            'reverse': circuit.reverse, 'root': circuit.root_gate,
            'leaves': circuit.leaf_by_source, 'stats': circuit.stats()}


def observe(circuit, target, previous, budget_error=horn.ReplayBudgetExceeded):
    full = circuit.evaluate(target)
    updated = circuit.update(previous, target)
    assert updated.values == full.values
    result = {'values': full.values, 'target': full.target,
              'changed_leaves': updated.changed_leaves,
              'recomputed_gates': updated.recomputed_gates,
              'survives': circuit.survives(full)}
    if result['survives']:
        try:
            result['node_count'] = circuit.replay_node_count(full)
            result['packet'] = circuit.reconstruct(full)
        except budget_error as exc:
            result['budget_rejection'] = (type(exc).__name__, str(exc))
    else:
        result['cut'] = circuit.blocking_cut(full)
    return result, updated


class HornReadyTests(unittest.TestCase):
    def test_all_64_forward_edge_sets(self):
        for edges in forward_graphs():
            clauses = graph_clauses(horn, edges)
            self.assertEqual(horn._topological_order((1, 2, 3, 4), clauses), scan_order((1, 2, 3, 4), clauses))

    def test_all_relabelings_keep_smallest_ready_not_fifo(self):
        count = 0
        for labels in permutations((1, 2, 3, 4)):
            mapping = dict(zip((1, 2, 3, 4), labels))
            for edges in forward_graphs():
                clauses = graph_clauses(horn, [(mapping[a], mapping[b]) for a, b in edges])
                self.assertEqual(horn._topological_order((1, 2, 3, 4), clauses), scan_order((1, 2, 3, 4), clauses))
                count += 1
        self.assertEqual(count, 1536)
        self.assertEqual(horn._topological_order((1, 2, 3, 4), graph_clauses(horn, [(3, 1)])), (2, 3, 1, 4))

    def test_cycles_duplicates_isolates_and_nonrule_clauses(self):
        cases = (((), ()), ((1, 2, 3, 4), ()), ((1,), ((1, 1),)),
                 ((1, 2), ((1, 2), (2, 1))),
                 ((1, 2, 3, 4), ((1, 2), (2, 1), (3, 4))),
                 ((1, 2, 3), ((1, 2), (1, 2), (2, 3))))
        for variables, edges in cases:
            clauses = graph_clauses(horn, edges)
            self.assertEqual(horn._topological_order(variables, clauses), scan_order(variables, clauses))
        extra = (horn.HornClause('fact', (3,), (), 3), horn.HornClause('deny', (-3, -1), (1, 3), None))
        clauses = graph_clauses(horn, [(3, 1), (3, 1)]) + extra
        self.assertEqual(horn._topological_order((1, 2, 3, 4), clauses), (2, 3, 1, 4))

    def test_compiler_deletions_match_scan_and_literal_truth(self):
        for source in small_sources():
            variables, clauses = horn._parse_horn(horn.formula(source))
            strategies = ('auto', 'layered') + (('acyclic',) if scan_order(variables, clauses) is not None else ())
            for strategy in strategies:
                current = horn.compile_horn(source, strategy=strategy)
                with patch.object(horn, '_topological_order', scan_order):
                    reference = horn.compile_horn(source, strategy=strategy)
                self.assertEqual(circuit_snapshot(current), circuit_snapshot(reference))
                keys = sorted(source)
                previous = current.evaluate(source)
                expected_previous = reference.evaluate(source)
                for mask in range(1 << len(keys)):
                    target = {sid: source[sid] for i, sid in enumerate(keys) if mask >> i & 1}
                    actual, previous = observe(current, target, previous)
                    expected, expected_previous = observe(reference, target, expected_previous)
                    self.assertEqual(actual, expected)
                    self.assertEqual(actual['survives'], literal_unsat(source, target))
                    if actual['survives']:
                        self.assertEqual(horn.verify(target, actual['packet']).conclusion, ())

    def test_budget_boundary_and_restoration_selection(self):
        source = small_sources()[-1]
        circuit = horn.compile_horn(source, replay_node_limit=5)
        short = {sid: body for sid, body in source.items() if sid not in {'a-empty', 'b', 'duplicate-b'}}
        before = circuit.evaluate(short)
        self.assertEqual(circuit.replay_node_count(before), 5)
        self.assertEqual(horn.verify(short, circuit.reconstruct(before)).conclusion, ())
        restored = {**short, 'b': source['b']}
        after = circuit.update(before, restored)
        self.assertTrue(circuit.survives(after))
        with self.assertRaisesRegex(horn.ReplayBudgetExceeded, 'requires 9 ordinary proof nodes; admitted limit is 5'):
            circuit.reconstruct(after)
        for limit in (8, 9):
            with patch.object(horn, '_topological_order', scan_order):
                if limit == 8:
                    with self.assertRaises(horn.ReplayBudgetExceeded):
                        horn.compile_horn(restored, replay_node_limit=limit)
                else:
                    exact = horn.compile_horn(restored, replay_node_limit=limit)
                    self.assertEqual(exact.replay_node_count(exact.evaluate(restored)), 9)

    def test_ownership_and_admission_controls(self):
        source = small_sources()[4]
        first, second = horn.compile_horn(source), horn.compile_horn(source)
        evaluation = first.evaluate(source)
        self.assertIsNot(first.owner_token, second.owner_token)
        with self.assertRaisesRegex(horn.Rejected, 'different Horn circuit'):
            second.survives(evaluation)
        with self.assertRaisesRegex(horn.Rejected, 'Booleans'):
            first.survives(replace(evaluation, values=(1,) + evaluation.values[1:]))
        for bad in ({'bad': [True]}, {'bad': [1, 2]}, {'bad': [1, 1]}, {'bad': [-1, 1]}):
            with self.assertRaises(horn.Rejected):
                horn.compile_horn(bad)
        with self.assertRaises(horn.Rejected):
            horn.compile_horn(small_sources()[11], strategy='acyclic')
        with self.assertRaises(horn.Rejected):
            horn.compile_horn(source, replay_node_limit=True)


if __name__ == '__main__':
    unittest.main()
