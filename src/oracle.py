"""Independent complete truth-table oracle for explicitly bounded CNF inputs.

This module deliberately does not import the producer or certificate checker.
Clause satisfaction is evaluated using bit masks rather than their set inference.
"""
from __future__ import annotations
from itertools import product
from typing import Iterable


def satisfying_masks(clauses: Iterable[Iterable[int]], n: int) -> list[int]:
    if type(n) is not int or not 0 <= n <= 16:
        raise ValueError("oracle dimension must be between zero and sixteen")
    encoded: list[tuple[int,int]] = []
    for c in clauses:
        positive = negative = 0
        for l in c:
            if type(l) is not int or not 1 <= abs(l) <= n:
                raise ValueError("literal outside oracle dimension")
            if l > 0:
                positive |= 1 << (l-1)
            else:
                negative |= 1 << (-l-1)
        encoded.append((positive,negative))
    universe = (1 << n) - 1
    return [m for m in range(1 << n)
            if all((m & p) or ((universe ^ m) & q) for p,q in encoded)]


def entails(clauses: Iterable[Iterable[int]], conclusion: Iterable[int], n: int) -> bool:
    if type(n) is not int or not 0 <= n <= 16:
        raise ValueError('oracle dimension must be between zero and sixteen')
    positives = negatives = 0
    for l in conclusion:
        if type(l) is not int or not 1 <= abs(l) <= n:
            raise ValueError('conclusion literal outside oracle dimension')
        if l > 0: positives |= 1 << (l-1)
        else: negatives |= 1 << (-l-1)
    full = (1 << n) - 1
    return all((m & positives) or ((full ^ m) & negatives)
               for m in satisfying_masks(clauses,n))


def all_clauses(n: int) -> list[list[int]]:
    """Every non-tautological clause, including empty, exactly once."""
    return [sorted((i+1)*s for i,s in enumerate(signs) if s)
            for signs in product((-1,0,1),repeat=n)]
