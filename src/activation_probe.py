"""Exact finite validation of the standard activation-literal reduction.

Permanent clauses are (-selector_i OR clause_i); each query sets selector_i true
exactly for an active clause. No solver implementation or proof-format change is
required. This program checks semantic equivalence, not LIDRUP interoperability.
"""
from __future__ import annotations
import argparse,json,time
from pathlib import Path
from itertools import product
from oracle import all_clauses,satisfying_masks


def encode(universe: list[list[int]], active: set[int], n: int) -> list[list[int]]:
    guards=[[-(n+i+1)]+c for i,c in enumerate(universe)]
    assumptions=[[(n+i+1) if i in active else -(n+i+1)] for i in range(len(universe))]
    return guards+assumptions


def run(out: Path) -> None:
    # Resource telemetry belongs to the Linux driver, not the pure encoding API.
    import resource

    out.mkdir(parents=True,exist_ok=True)
    cpu,wall=time.process_time(),time.perf_counter()
    universe=all_clauses(2)
    checks=0
    # Enumerating all 11-variable assignments includes the activation units;
    # the oracle neither assumes nor imports their intended interpretation.
    for mask in range(512):
        active={i for i in range(9) if mask>>i&1}
        original=[universe[i] for i in sorted(active)]
        actual=satisfying_masks(encode(universe,active,2),11)
        expected=satisfying_masks(original,2)
        if sorted(m&3 for m in actual)!=expected:
            raise AssertionError('activation encoding changed projected models')
        checks+=2048
    summary={'formulas':512,'public_variables':2,'selectors':9,'encoded_variables':11,
             'assignments_checked':checks,'projected_equivalence_failures':0,
             'cpu_seconds':time.process_time()-cpu,'wall_seconds':time.perf_counter()-wall,
             'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
             'workers':1,'maturity':'finite-check of a standard reduction',
             'boundary':'Boolean CNF semantics only; no native LIDRUP trace is generated'}
    (out/'selector-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    run(p.parse_args().out)
