"""Independent retained-source Horn oracle.

This module deliberately imports neither the certificate parser, Horn compiler,
ordinary proof checker, nor generic survival circuit.
"""
from __future__ import annotations

from collections import defaultdict, deque
from typing import Any, Mapping


def retained_horn_unsat(source: Mapping[str, Any], target: Mapping[str, Any]) -> bool:
    active: list[tuple[int | None, tuple[int, ...]]] = []
    for sid, raw_body in source.items():
        body = tuple(raw_body)
        if sid not in target or tuple(target[sid]) != body:
            continue
        positives = [literal for literal in body if literal > 0]
        if len(positives) > 1:
            raise ValueError("oracle input is not Horn")
        antecedents = tuple(sorted(-literal for literal in body if literal < 0))
        head = positives[0] if positives else None
        active.append((head, antecedents))

    derived: set[int] = set()
    waiting: dict[int, list[int]] = defaultdict(list)
    missing: list[int] = []
    heads: list[int | None] = []
    queue: deque[int] = deque()

    for index, (head, antecedents) in enumerate(active):
        heads.append(head)
        missing.append(len(antecedents))
        for atom in antecedents:
            waiting[atom].append(index)
        if not antecedents:
            if head is None:
                return True
            if head not in derived:
                derived.add(head)
                queue.append(head)

    while queue:
        atom = queue.popleft()
        for index in waiting.get(atom, ()):
            missing[index] -= 1
            if missing[index] != 0:
                continue
            head = heads[index]
            if head is None:
                return True
            if head not in derived:
                derived.add(head)
                queue.append(head)
    return False
