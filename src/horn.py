"""Exact version-bound certificates for retained Horn contracts.

The source is a versioned Horn CNF: each clause has at most one positive literal.
Leaves are active only when the target retains the same identifier and canonical
body. The compiler builds a monotone derivability circuit, reconstructs an
ordinary resolution refutation for every positive result, and checks that proof
with the independent ordinary checker.

Acyclic implication dependencies use one derivation layer. Cyclic Horn sources
use the standard least-fixed-point unrolling for at most the number of atoms.
The module is a reference checker, not a SAT solver or an RTL front end.
"""
from __future__ import annotations

from dataclasses import dataclass
from heapq import heapify, heappop, heappush
from typing import Any, Mapping, Optional

from certificates import MAX_NODES, Rejected, ReplayBudgetExceeded, formula, verify
from survival import Evaluation, Gate, MAX_GATES

Clause = tuple[int, ...]


@dataclass(frozen=True)
class HornClause:
    source: str
    body: Clause
    antecedents: tuple[int, ...]
    head: Optional[int]


@dataclass(frozen=True)
class VerifiedHorn:
    source: tuple[tuple[str, Clause], ...]
    variables: tuple[int, ...]
    strategy: str
    clauses: tuple[HornClause, ...]
    gates: tuple[Gate, ...]
    root_gate: int
    reverse: tuple[tuple[int, ...], ...]
    leaf_by_source: tuple[tuple[str, int], ...]
    owner_token: object
    depth: int
    replay_node_limit: int
    exact_gate_bound: int
    exact_edge_bound: int

    def _target_map(self, target: Mapping[str, Any]) -> dict[str, Clause]:
        return formula(target)

    def _validate_evaluation(self, evaluation: Evaluation) -> None:
        if not isinstance(evaluation, Evaluation):
            raise Rejected("expected an Evaluation produced by this circuit")
        if evaluation.owner_token is not self.owner_token:
            raise Rejected("evaluation belongs to a different Horn circuit")
        if len(evaluation.values) != len(self.gates):
            raise Rejected("evaluation gate vector has the wrong length")
        if any(type(value) is not bool for value in evaluation.values):
            raise Rejected("evaluation gate vector must contain Booleans")
        try:
            current = dict(evaluation.target)
        except (TypeError, ValueError) as exc:
            raise Rejected("evaluation target snapshot is malformed") from exc
        if len(current) != len(evaluation.target):
            raise Rejected("evaluation target snapshot has duplicate identifiers")
        checked = tuple(sorted(formula(current).items()))
        if checked != evaluation.target:
            raise Rejected("evaluation target snapshot is not canonical")

    def evaluate(self, target: Mapping[str, Any]) -> Evaluation:
        current = self._target_map(target)
        values: list[bool] = []
        for gate in self.gates:
            if gate.kind == "leaf":
                sid, body = gate.payload
                values.append(sid in current and current[sid] == body)
            elif gate.kind == "and":
                values.append(all(values[parent] for parent in gate.parents))
            elif gate.kind == "or":
                values.append(any(values[parent] for parent in gate.parents))
            else:  # pragma: no cover
                raise AssertionError("unknown gate kind")
        return Evaluation(tuple(values), tuple(sorted(current.items())), self.owner_token)

    def update(self, previous: Evaluation, target: Mapping[str, Any]) -> Evaluation:
        """Recompute gate logic in the conservative fanout of changed leaves.

        The immutable reference implementation also validates the complete prior
        snapshot, canonicalizes the complete new target, copies all ``N`` gate
        values, scans every source leaf, and sorts marked gate indices.  The
        ``recomputed_gates`` field therefore measures only Boolean gate logic in
        the marked cone, not total update cost or an end-to-end speedup.
        """
        self._validate_evaluation(previous)
        current = self._target_map(target)
        values = list(previous.values)
        changed: list[int] = []
        for sid, gate_index in self.leaf_by_source:
            body = self.gates[gate_index].payload[1]
            new_value = sid in current and current[sid] == body
            if new_value != values[gate_index]:
                values[gate_index] = new_value
                changed.append(gate_index)
        affected: set[int] = set()
        stack = changed[:]
        while stack:
            gate_index = stack.pop()
            for child in self.reverse[gate_index]:
                if child not in affected:
                    affected.add(child)
                    stack.append(child)
        recomputed = 0
        for gate_index in sorted(affected):
            gate = self.gates[gate_index]
            if gate.kind == "and":
                values[gate_index] = all(values[parent] for parent in gate.parents)
            elif gate.kind == "or":
                values[gate_index] = any(values[parent] for parent in gate.parents)
            else:
                continue
            recomputed += 1
        return Evaluation(tuple(values), tuple(sorted(current.items())), self.owner_token,
                          changed_leaves=len(changed), recomputed_gates=recomputed)

    def survives(self, evaluation: Evaluation) -> bool:
        self._validate_evaluation(evaluation)
        return evaluation.values[self.root_gate]

    def _replay_plan(
        self, evaluation: Evaluation
    ) -> tuple[tuple[int, ...], dict[int, int], int]:
        """Select one true Horn proof sub-DAG iteratively and check its budget."""
        if not self.survives(evaluation):
            raise Rejected("Horn survival root is false")
        required: set[int] = set()
        chosen_parent: dict[int, int] = {}
        stack = [self.root_gate]
        while stack:
            gate_index = stack.pop()
            if gate_index in required:
                continue
            if not evaluation.values[gate_index]:
                raise AssertionError("false gate selected for Horn witness")
            required.add(gate_index)
            gate = self.gates[gate_index]
            if gate.kind == "or":
                try:
                    chosen = next(parent for parent in gate.parents
                                  if evaluation.values[parent])
                except StopIteration as exc:  # pragma: no cover - evaluator invariant
                    raise AssertionError("true Horn OR has no true parent") from exc
                chosen_parent[gate_index] = chosen
                stack.append(chosen)
            elif gate.kind == "and":
                stack.extend(gate.parents)
            elif gate.kind != "leaf":  # pragma: no cover
                raise AssertionError("unknown gate kind")

        ordered = tuple(sorted(required))
        node_count = 0
        for gate_index in ordered:
            gate = self.gates[gate_index]
            if gate.kind == "leaf":
                node_count += 1
            elif gate.kind == "and":
                tag, _, _, antecedents, _ = gate.payload
                if tag not in {"derive", "conflict"}:  # pragma: no cover
                    raise AssertionError("unknown Horn gate payload")
                node_count += len(antecedents)
        if node_count > self.replay_node_limit:
            raise ReplayBudgetExceeded(
                f"replay requires {node_count} ordinary proof nodes; "
                f"admitted limit is {self.replay_node_limit}"
            )
        return ordered, chosen_parent, node_count

    def replay_node_count(self, evaluation: Evaluation) -> int:
        """Return the exact selected ordinary-proof size or reject on budget."""
        return self._replay_plan(evaluation)[2]

    def _reconstruct_packet(self, evaluation: Evaluation, *, recheck: bool) -> dict[str, Any]:
        ordered, chosen_parent, node_count = self._replay_plan(evaluation)
        current = dict(evaluation.target)
        nodes: list[dict[str, Any]] = []
        proof_id: dict[int, str] = {}
        for gate_index in ordered:
            gate = self.gates[gate_index]
            if gate.kind == "leaf":
                sid, body = gate.payload
                ident = f"n{len(nodes)}"
                nodes.append({"id": ident, "kind": "axiom", "source": sid,
                              "clause": list(body)})
                proof_id[gate_index] = ident
                continue
            if gate.kind == "or":
                proof_id[gate_index] = proof_id[chosen_parent[gate_index]]
                continue
            if gate.kind != "and":  # pragma: no cover
                raise AssertionError("unknown gate kind")
            tag, _, body, antecedents, head = gate.payload
            if tag not in {"derive", "conflict"}:  # pragma: no cover
                raise AssertionError("unknown Horn gate payload")
            current_id = proof_id[gate.parents[0]]
            current_clause = set(body)
            for atom, parent in zip(antecedents, gate.parents[1:]):
                unit_id = proof_id[parent]
                if -atom not in current_clause:
                    raise AssertionError("Horn antecedent absent from current clause")
                current_clause.remove(-atom)
                out = tuple(sorted(current_clause))
                ident = f"n{len(nodes)}"
                nodes.append({"id": ident, "kind": "resolve",
                              "left": unit_id, "right": current_id,
                              "pivot": atom, "clause": list(out)})
                current_id = ident
            expected = () if head is None else (head,)
            if tuple(sorted(current_clause)) != expected:
                raise AssertionError("Horn reconstruction conclusion mismatch")
            proof_id[gate_index] = current_id
        if len(nodes) != node_count:  # pragma: no cover - internal accounting
            raise AssertionError("Horn replay node accounting mismatch")
        root = proof_id[self.root_gate]
        packet = {"nodes": nodes, "root": root}
        if recheck:
            checked = verify(current, packet)
            if checked.conclusion != ():
                raise AssertionError("Horn witness is not a refutation")
        return packet

    def reconstruct(self, evaluation: Evaluation) -> dict[str, Any]:
        """Reconstruct and recheck one ordinary resolution refutation."""
        return self._reconstruct_packet(evaluation, recheck=True)

    def blocking_cut(self, evaluation: Evaluation) -> tuple[str, ...]:
        """Return a deterministic sufficient, not necessarily minimum, leaf cut."""
        if self.survives(evaluation):
            raise Rejected("Horn survival root is true")
        required: set[int] = set()
        stack = [self.root_gate]
        while stack:
            gate_index = stack.pop()
            if gate_index in required:
                continue
            if evaluation.values[gate_index]:
                raise AssertionError("blocking cut requested for true gate")
            required.add(gate_index)
            gate = self.gates[gate_index]
            if gate.kind == "or":
                stack.extend(gate.parents)
            elif gate.kind == "and":
                stack.extend(parent for parent in gate.parents
                             if not evaluation.values[parent])
            elif gate.kind != "leaf":  # pragma: no cover
                raise AssertionError("unknown gate kind")

        memo: dict[int, frozenset[str]] = {}
        for gate_index in sorted(required):
            gate = self.gates[gate_index]
            if gate.kind == "leaf":
                result = frozenset([gate.payload[0]])
            elif gate.kind == "or":
                result = frozenset().union(*(memo[parent] for parent in gate.parents))
            elif gate.kind == "and":
                choices = [memo[parent] for parent in gate.parents
                           if not evaluation.values[parent]]
                result = min(choices, key=lambda item: (len(item), tuple(sorted(item))))
            else:  # pragma: no cover
                raise AssertionError("unknown gate kind")
            memo[gate_index] = result
        return tuple(sorted(memo[self.root_gate]))

    def stats(self) -> dict[str, int | str | bool]:
        edges = sum(len(gate.parents) for gate in self.gates)
        return {
            "mode": "horn",
            "strategy": self.strategy,
            "variables": len(self.variables),
            "clauses": len(self.clauses),
            "depth": self.depth,
            "replay_node_limit": self.replay_node_limit,
            "gates": len(self.gates),
            "edges": edges,
            "leaf_gates": sum(g.kind == "leaf" for g in self.gates),
            "and_gates": sum(g.kind == "and" for g in self.gates),
            "or_gates": sum(g.kind == "or" for g in self.gates),
            "exact_gate_bound": self.exact_gate_bound,
            "exact_edge_bound": self.exact_edge_bound,
            "bound_matches": len(self.gates) == self.exact_gate_bound
                             and edges == self.exact_edge_bound,
        }


def _parse_horn(base: dict[str, Clause]) -> tuple[tuple[int, ...], tuple[HornClause, ...]]:
    clauses: list[HornClause] = []
    variables: set[int] = set()
    for sid, body in sorted(base.items()):
        positives = tuple(lit for lit in body if lit > 0)
        if len(positives) > 1:
            raise Rejected("Horn mode requires at most one positive literal per clause")
        antecedents = tuple(sorted(-lit for lit in body if lit < 0))
        head = positives[0] if positives else None
        variables.update(abs(lit) for lit in body)
        clauses.append(HornClause(sid, body, antecedents, head))
    return tuple(sorted(variables)), tuple(clauses)


def _topological_order(variables: tuple[int, ...], clauses: tuple[HornClause, ...]) -> Optional[tuple[int, ...]]:
    successors = {variable: set() for variable in variables}
    indegree = {variable: 0 for variable in variables}
    for clause in clauses:
        if clause.head is None or not clause.antecedents:
            continue
        for antecedent in clause.antecedents:
            if clause.head not in successors[antecedent]:
                successors[antecedent].add(clause.head)
                indegree[clause.head] += 1
    ready = [variable for variable in variables if indegree[variable] == 0]
    heapify(ready)
    order: list[int] = []
    while ready:
        variable = heappop(ready)
        order.append(variable)
        for successor in sorted(successors[variable]):
            indegree[successor] -= 1
            if indegree[successor] == 0:
                heappush(ready, successor)
    if len(order) != len(variables):
        return None
    return tuple(order)


def compile_horn(
    source: Mapping[str, Any],
    *,
    strategy: str = "auto",
    replay_node_limit: int = MAX_NODES,
) -> VerifiedHorn:
    """Validate, compile, and admit exact retained-source Horn UNSAT.

    The replay-node limit is shared with the ordinary proof checker.  If the
    full source is already UNSAT, admission plans its selected replay and rejects
    explicitly when that proof would exceed the limit.  Each later positive
    target is planned again because deleting a short alternative can expose a
    larger surviving derivation.
    """
    if strategy not in {"auto", "acyclic", "layered"}:
        raise Rejected("Horn strategy must be auto, acyclic, or layered")
    if type(replay_node_limit) is not int or not 1 <= replay_node_limit <= MAX_NODES:
        raise Rejected(f"replay_node_limit must be in 1..{MAX_NODES}")
    base = formula(source)
    variables, clauses = _parse_horn(base)
    order = _topological_order(variables, clauses)
    selected = "acyclic" if strategy == "auto" and order is not None else strategy
    if selected == "auto":
        selected = "layered"
    if selected == "acyclic" and order is None:
        raise Rejected("acyclic Horn strategy requires an acyclic dependency graph")

    facts_by_head: dict[int, list[HornClause]] = {v: [] for v in variables}
    rules_by_head: dict[int, list[HornClause]] = {v: [] for v in variables}
    constraints: list[HornClause] = []
    for clause in clauses:
        if clause.head is None:
            constraints.append(clause)
        elif clause.antecedents:
            rules_by_head[clause.head].append(clause)
        else:
            facts_by_head[clause.head].append(clause)

    rule_count = sum(len(items) for items in rules_by_head.values())
    fact_count = sum(len(items) for items in facts_by_head.values())
    constraint_count = len(constraints)
    rule_antecedents = sum(len(clause.antecedents)
                           for items in rules_by_head.values() for clause in items)
    constraint_antecedents = sum(len(clause.antecedents) for clause in constraints)
    depth = 0 if selected == "acyclic" else len(variables)

    if selected == "acyclic":
        gate_bound = len(clauses) + len(variables) + rule_count + constraint_count + 1
        edge_bound = (fact_count + 2 * rule_count + rule_antecedents
                      + 2 * constraint_count + constraint_antecedents)
    else:
        gate_bound = (len(clauses) + (depth + 1) * len(variables)
                      + depth * rule_count + constraint_count + 1)
        edge_bound = (fact_count
                      + depth * (len(variables) + 2 * rule_count + rule_antecedents)
                      + 2 * constraint_count + constraint_antecedents)
    if gate_bound > MAX_GATES:
        raise Rejected(f"compiled Horn circuit would require {gate_bound} gates; bound is {MAX_GATES}")
    if len(clauses) > MAX_NODES:
        raise Rejected("Horn source exceeds clause bound")

    gates: list[Gate] = []
    reverse: list[list[int]] = []

    def add(kind: str, parents: tuple[int, ...], payload: Any) -> int:
        if len(gates) >= MAX_GATES:
            raise Rejected("compiled Horn circuit exceeds gate bound")
        index = len(gates)
        gates.append(Gate(kind, parents, payload))
        reverse.append([])
        for parent in parents:
            reverse[parent].append(index)
        return index

    leaf_by_source: list[tuple[str, int]] = []
    leaf_for_source: dict[str, int] = {}
    for clause in clauses:
        gate_index = add("leaf", (), (clause.source, clause.body))
        leaf_by_source.append((clause.source, gate_index))
        leaf_for_source[clause.source] = gate_index

    if selected == "acyclic":
        assert order is not None
        atom_gate: dict[int, int] = {}
        for variable in order:
            parents = [leaf_for_source[clause.source]
                       for clause in facts_by_head[variable]]
            for clause in rules_by_head[variable]:
                rule_parents = (leaf_for_source[clause.source],) + tuple(
                    atom_gate[antecedent] for antecedent in clause.antecedents)
                parents.append(add("and", rule_parents,
                                   ("derive", clause.source, clause.body,
                                    clause.antecedents, clause.head)))
            atom_gate[variable] = add("or", tuple(parents), ("atom", variable))
    else:
        atom_layers: list[dict[int, int]] = []
        layer0: dict[int, int] = {}
        for variable in variables:
            parents = tuple(leaf_for_source[clause.source]
                            for clause in facts_by_head[variable])
            layer0[variable] = add("or", parents, ("atom", variable, 0))
        atom_layers.append(layer0)
        for layer in range(1, depth + 1):
            previous = atom_layers[-1]
            current: dict[int, int] = {}
            for variable in variables:
                parents = [previous[variable]]
                for clause in rules_by_head[variable]:
                    rule_parents = (leaf_for_source[clause.source],) + tuple(
                        previous[antecedent] for antecedent in clause.antecedents)
                    parents.append(add("and", rule_parents,
                                       ("derive", clause.source, clause.body,
                                        clause.antecedents, clause.head)))
                current[variable] = add("or", tuple(parents),
                                        ("atom", variable, layer))
            atom_layers.append(current)
        atom_gate = atom_layers[-1]

    conflict_gates: list[int] = []
    for clause in constraints:
        parents = (leaf_for_source[clause.source],) + tuple(
            atom_gate[antecedent] for antecedent in clause.antecedents)
        conflict_gates.append(add("and", parents,
                                  ("conflict", clause.source, clause.body,
                                   clause.antecedents, None)))
    root_gate = add("or", tuple(conflict_gates), ("root",))

    edges = sum(len(gate.parents) for gate in gates)
    if len(gates) != gate_bound or edges != edge_bound:
        raise AssertionError("Horn circuit size formula mismatch")

    compiled = VerifiedHorn(
        source=tuple(sorted(base.items())), variables=variables,
        strategy=selected, clauses=clauses, gates=tuple(gates),
        root_gate=root_gate, reverse=tuple(tuple(items) for items in reverse),
        leaf_by_source=tuple(leaf_by_source), owner_token=object(), depth=depth,
        replay_node_limit=replay_node_limit,
        exact_gate_bound=gate_bound, exact_edge_bound=edge_bound,
    )
    source_evaluation = compiled.evaluate(base)
    if compiled.survives(source_evaluation):
        compiled.replay_node_count(source_evaluation)
    return compiled
