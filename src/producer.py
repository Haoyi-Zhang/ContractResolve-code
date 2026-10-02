"""Untrusted, deterministic, small-instance resolution producer; standard library.

Saturation is used only for the exhaustive two-variable pilot. This is not a CDCL
baseline and no production-solver speed claim is made. It shares no inference
implementation with certificates.py or oracle.py.
"""
from __future__ import annotations
from typing import Any


def saturate(base: dict[str, list[int]], max_clauses: int = 1000) -> dict[str, Any]:
    nodes: list[dict[str, Any]] = []
    clause_id: dict[tuple[int, ...], str] = {}
    queue: list[tuple[int, ...]] = []
    for sid, body in sorted(base.items()):
        c = tuple(body)
        if c not in clause_id:
            ident = f"n{len(nodes)}"
            clause_id[c] = ident
            nodes.append({"id":ident, "kind":"axiom", "source":sid, "clause":list(c)})
            queue.append(c)
    at = 0
    while at < len(queue):
        a = queue[at]
        for b in queue[:at]:
            for p in sorted(set(abs(l) for l in a)):
                if p in a and -p in b:
                    left, right = a, b
                elif p in b and -p in a:
                    left, right = b, a
                else:
                    continue
                c = tuple(sorted((set(left) - {p}) | (set(right) - {-p})))
                if any(-l in c for l in c) or c in clause_id:
                    continue
                if len(queue) >= max_clauses:
                    raise RuntimeError("explicit saturation bound exceeded")
                ident = f"n{len(nodes)}"
                clause_id[c] = ident
                nodes.append({"id":ident, "kind":"resolve", "left":clause_id[left],
                              "right":clause_id[right], "pivot":p, "clause":list(c)})
                queue.append(c)
        at += 1
    return {"nodes":nodes, "roots":clause_id}


def solve(base: dict[str, list[int]], max_variables: int = 14) -> dict[str, Any]:
    """Bounded tree search with a resolution refutation or a total model.

    No proof-checker code is imported. The caller checks all outputs independently.
    """
    variables = sorted({abs(l) for body in base.values() for l in body})
    if len(variables) > max_variables:
        raise ValueError("small-instance solver variable bound exceeded")
    nodes: list[dict[str, Any]] = []
    known: dict[tuple[int, ...], str] = {}
    source = [(sid, tuple(body)) for sid,body in sorted(base.items())]
    visited = 0

    def axiom(sid: str, clause: tuple[int, ...]) -> tuple[int, ...]:
        if clause not in known:
            ident = f"n{len(nodes)}"
            known[clause] = ident
            nodes.append({"id":ident,"kind":"axiom","source":sid,"clause":list(clause)})
        return clause

    def visit(assignment: dict[int,bool]) -> tuple[bool, Any]:
        nonlocal visited
        visited += 1
        for sid,c in source:
            if all(abs(l) in assignment and assignment[abs(l)] != (l>0) for l in c):
                return False, axiom(sid,c)
        if len(assignment) == len(variables):
            return True, {str(v):assignment[v] for v in variables}
        p = next(v for v in variables if v not in assignment)
        sat, left = visit({**assignment,p:False})
        if sat:
            return True, left
        if p not in left:
            return False, left
        sat, right = visit({**assignment,p:True})
        if sat:
            return True, right
        if -p not in right:
            return False, right
        resolvent = tuple(sorted((set(left) - {p}) | (set(right) - {-p})))
        if resolvent not in known:
            ident = f"n{len(nodes)}"
            known[resolvent] = ident
            nodes.append({"id":ident,"kind":"resolve","left":known[left],
                          "right":known[right],"pivot":p,"clause":list(resolvent)})
        return False, resolvent

    sat, result = visit({})
    if sat:
        return {"status":"sat","model":result,"search_nodes":visited}
    if result != ():
        raise RuntimeError("internal error: root conflict is nonempty")
    return {"status":"unsat","certificate":{"nodes":nodes,"root":known[()]},
            "search_nodes":visited}
