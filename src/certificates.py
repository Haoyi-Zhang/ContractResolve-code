"""Resolution certificates and conservative reuse after nonmonotone CNF edits.

This is a small research reference implementation, not a production SAT checker.
Only JSON is an untrusted boundary; Python callers and the interpreter are trusted.
The producer and truth-table oracle do not import this module.
"""
from __future__ import annotations
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

MAX_VARIABLE = 100_000
MAX_NODES = 100_000
MAX_CLAUSE = 1_000
MAX_JSON_BYTES = 32 * 1024 * 1024

class Rejected(ValueError):
    """Malformed certificate or invalid inference."""


class ReplayBudgetExceeded(Rejected):
    """A logically positive result cannot be replayed within its admitted budget."""


def _keys(d: Any, required: set[str]) -> None:
    if not isinstance(d, dict) or set(d) != required:
        raise Rejected(f"expected exactly keys {sorted(required)}")


def _name(x: Any) -> str:
    if not isinstance(x, str) or not x or len(x) > 128:
        raise Rejected("identifier must be a nonempty string of at most 128 characters")
    return x


def _clause(x: Any) -> tuple[int, ...]:
    if not isinstance(x, (list, tuple)) or len(x) > MAX_CLAUSE:
        raise Rejected("clause is not a bounded sequence")
    if any(type(l) is not int or not 0 < abs(l) <= MAX_VARIABLE for l in x):
        raise Rejected("invalid literal")
    if tuple(sorted(set(x))) != tuple(x):
        raise Rejected("clause must be sorted and duplicate-free")
    if any(-l in x for l in x):
        raise Rejected("tautological clauses are outside this certificate language")
    return tuple(x)


def formula(x: Any) -> dict[str, tuple[int, ...]]:
    if not isinstance(x, dict) or len(x) > MAX_NODES:
        raise Rejected("formula must be a bounded map")
    return {_name(k): _clause(v) for k, v in x.items()}


def _unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise Rejected(f"duplicate JSON key: {k}")
        out[k] = v
    return out


def read_json(path: str | Path) -> Any:
    p = Path(path)
    if p.stat().st_size > MAX_JSON_BYTES:
        raise Rejected("JSON input exceeds size limit")
    try:
        return json.loads(p.read_text(encoding="utf-8"), object_pairs_hook=_unique)
    except (json.JSONDecodeError, UnicodeError, RecursionError) as e:
        raise Rejected("invalid or excessively nested JSON") from e


@dataclass(frozen=True)
class VerifiedFragment:
    """In-process result of checking, never accepted from serialized cache flags.

    All fields are immutable tuples, so later input-map mutation cannot modify
    this snapshot. Construction by arbitrary Python code is outside the boundary.
    """
    conclusion: tuple[int, ...]
    support: tuple[tuple[str, tuple[int, ...]], ...]
    checked_resolution_nodes: int
    checked_nodes: int


def verify(source: Mapping[str, Any], certificate: Any) -> VerifiedFragment:
    """Validate every listed node and recompute the designated root's ancestry.

    Parent references must precede the child. This rejects cycles without relying
    on producer-supplied ranks or support summaries. A root can be any clause;
    only an empty conclusion is an UNSAT certificate.
    """
    base = formula(source)
    _keys(certificate, {"nodes", "root"})
    nodes = certificate["nodes"]
    root = _name(certificate["root"])
    if not isinstance(nodes, list) or not 1 <= len(nodes) <= MAX_NODES:
        raise Rejected("certificate must have a bounded, nonempty node list")
    clauses: dict[str, tuple[int, ...]] = {}
    supports: dict[str, frozenset[str]] = {}
    resolutions = 0
    for node in nodes:
        if not isinstance(node, dict):
            raise Rejected("node is not an object")
        if node.get("kind") == "axiom":
            _keys(node, {"id", "kind", "source", "clause"})
        elif node.get("kind") == "resolve":
            _keys(node, {"id", "kind", "left", "right", "pivot", "clause"})
        else:
            raise Rejected("unknown inference kind")
        ident = _name(node["id"])
        if ident in clauses:
            raise Rejected("duplicate node identifier")
        clause = _clause(node["clause"])
        if node["kind"] == "axiom":
            source_id = _name(node["source"])
            if source_id not in base or base[source_id] != clause:
                raise Rejected("axiom identity/body mismatch")
            support = frozenset([source_id])
        else:
            left, right = _name(node["left"]), _name(node["right"])
            if left not in clauses or right not in clauses:
                raise Rejected("parent missing, forward, or cyclic")
            p = node["pivot"]
            if type(p) is not int or not 0 < p <= MAX_VARIABLE:
                raise Rejected("invalid positive pivot")
            a, b = set(clauses[left]), set(clauses[right])
            if p not in a or -p not in b:
                raise Rejected("pivot absent or wrong orientation")
            expected = (a - {p}) | (b - {-p})
            if expected != set(clause):
                raise Rejected("not the exact binary resolvent")
            support = supports[left] | supports[right]
            resolutions += 1
        clauses[ident] = clause
        supports[ident] = support
    if root not in clauses:
        raise Rejected("root missing")
    return VerifiedFragment(clauses[root], tuple((k, base[k]) for k in sorted(supports[root])),
                            resolutions, len(nodes))


def reusable(verified: VerifiedFragment, target: Mapping[str, Any]) -> bool:
    """Return a sufficient, deliberately not necessary, entailment criterion."""
    current = formula(target)
    return all(k in current and current[k] == body for k, body in verified.support)


def check_model(target: Mapping[str, Any], model: Mapping[str, Any]) -> bool:
    """Require a total Boolean assignment on exactly the target's variables."""
    current = formula(target)
    variables = {abs(l) for c in current.values() for l in c}
    if not isinstance(model, dict) or set(model) != {str(v) for v in variables}:
        return False
    if any(type(v) is not bool for v in model.values()):
        return False
    return all(any(model[str(abs(l))] == (l > 0) for l in c) for c in current.values())
