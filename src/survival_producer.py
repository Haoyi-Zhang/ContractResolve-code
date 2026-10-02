"""Untrusted producers for trace and resolution-closed survival certificates."""
from __future__ import annotations

from typing import Any, Iterable


def _resolvents(left: tuple[int, ...], right: tuple[int, ...]):
    a, b = set(left), set(right)
    for pivot in sorted(x for x in a if x > 0 and -x in b):
        out = tuple(sorted((a - {pivot}) | (b - {-pivot})))
        if not any(-x in out for x in out):
            yield pivot, out


def closure_certificate(source: dict[str, list[int]], root: Iterable[int] = ()) -> dict[str, Any]:
    """Compute a finite resolution-closed universe containing source and root.

    The root is included before saturation.  Thus, for a root not derivable from
    the source, the producer returns a checked closed superset rather than the
    least closure of the source alone.  The compiler never trusts minimality.
    """
    clauses = {tuple(body) for body in source.values()}
    root_clause = tuple(root)
    clauses.add(root_clause)
    changed = True
    while changed:
        changed = False
        snapshot = sorted(clauses)
        for left in snapshot:
            for right in snapshot:
                for _, out in _resolvents(left, right):
                    if out not in clauses:
                        clauses.add(out)
                        changed = True
    ordered = sorted(clauses)
    schemas = []
    for left in ordered:
        for right in ordered:
            for pivot, out in _resolvents(left, right):
                schemas.append({"left": list(left), "right": list(right),
                                "pivot": pivot, "clause": list(out)})
    return {
        "mode": "closed",
        "axioms": [{"source": sid, "clause": list(body)}
                   for sid, body in sorted(source.items())],
        "clauses": [list(c) for c in ordered],
        "schemas": schemas,
        "root": list(root_clause),
        "max_depth": len(ordered),
    }


def trace_certificate(source: dict[str, list[int]], packets: list[dict[str, Any]],
                      root: Iterable[int] = ()) -> dict[str, Any]:
    """Extract syntactic schemas from ordinary proof fragments.

    This producer is deliberately untrusted: compile_survival independently checks
    every axiom and schema.  All source clauses are exposed as possible leaves so
    a validated schema can compose with an alternative exact source clause that
    has the same body.
    """
    clauses = {tuple(body) for body in source.values()}
    schemas: set[tuple[tuple[int, ...], tuple[int, ...], int, tuple[int, ...]]] = set()
    root_clause = tuple(root)
    clauses.add(root_clause)
    for packet in packets:
        known: dict[str, tuple[int, ...]] = {}
        for node in packet["nodes"]:
            body = tuple(node["clause"])
            known[node["id"]] = body
            clauses.add(body)
            if node["kind"] == "resolve":
                left, right = known[node["left"]], known[node["right"]]
                schemas.add((left, right, node["pivot"], body))
    ordered = sorted(clauses)
    return {
        "mode": "trace",
        "axioms": [{"source": sid, "clause": list(body)}
                   for sid, body in sorted(source.items())],
        "clauses": [list(c) for c in ordered],
        "schemas": [{"left": list(a), "right": list(b), "pivot": p, "clause": list(c)}
                    for a, b, p, c in sorted(schemas)],
        "root": list(root_clause),
        "max_depth": len(ordered),
    }


def duplicate_unit_chain(k: int) -> tuple[dict[str, list[int]], dict[str, Any]]:
    """Linear proof-schema family with 2^k minimal retained supports."""
    if not 1 <= k <= 100:
        raise ValueError("k outside bounded family")
    source: dict[str, list[int]] = {}
    for i in range(1, k + 1):
        source[f"x{i:03d}"] = [i]
        source[f"y{i:03d}"] = [i]
    source["bad"] = list(range(-k, 0))
    nodes: list[dict[str, Any]] = []
    known: dict[tuple[int, ...], str] = {}

    def axiom(sid: str, body: tuple[int, ...]) -> str:
        ident = f"n{len(nodes)}"
        nodes.append({"id": ident, "kind": "axiom", "source": sid,
                      "clause": list(body)})
        known[body] = ident
        return ident

    current = tuple(source["bad"])
    current_id = axiom("bad", current)
    for i in range(1, k + 1):
        unit = (i,)
        unit_id = axiom(f"x{i:03d}", unit)
        out = tuple(x for x in current if x != -i)
        ident = f"n{len(nodes)}"
        nodes.append({"id": ident, "kind": "resolve", "left": unit_id,
                      "right": current_id, "pivot": i, "clause": list(out)})
        current, current_id = out, ident
    packet = {"nodes": nodes, "root": current_id}
    return source, trace_certificate(source, [packet], root=())
