"""Finite probe: a RAT-redundant clause is not an unrestricted reusable lemma.

Implements the mathematical RUP/RAT predicates, not a DRAT file parser. The
separate truth-table oracle checks semantic assertions. All inputs are original
complete two-variable enumerations, not traces from an external solver.
"""
from __future__ import annotations
import argparse,csv,json,resource,time
from pathlib import Path
from oracle import all_clauses,satisfying_masks,entails


def rup(base: list[list[int]], clause: list[int]) -> bool:
    assignment: dict[int,bool] = {}
    for l in clause:
        var,value=abs(l),l<0
        if var in assignment and assignment[var]!=value:
            return True  # Negation of a tautological clause is inconsistent.
        assignment[var]=value
    while True:
        changed=False
        for c in base:
            pending=[]
            satisfied=False
            for l in c:
                if abs(l) not in assignment:pending.append(l)
                elif assignment[abs(l)]==(l>0):
                    satisfied=True;break
            if satisfied:continue
            if not pending:return True
            if len(pending)==1:
                l=pending[0];assignment[abs(l)]=l>0;changed=True
        if not changed:return False


def rat(base: list[list[int]], clause: list[int], pivot: int) -> bool:
    if pivot not in clause:raise ValueError('pivot must occur in candidate clause')
    for d in base:
        if -pivot in d:
            resolvent=sorted((set(clause)-{pivot})|(set(d)-{-pivot}))
            if not rup(base,resolvent):return False
    return True


def run(out: Path) -> None:
    out.mkdir(parents=True,exist_ok=True)
    cpu,wall=time.process_time(),time.perf_counter()
    universe=all_clauses(2)
    totals={"formulas":512,"candidate_pivot_pairs":0,"rat_valid":0,
            "rat_valid_not_entailed":0,"extensions_checked":0,
            "unsafe_imports":0,"polarity_safe_extensions":0,"polarity_rule_failures":0}
    first=None
    with (out/'rat-extensions.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['formula_mask','clause_index','pivot','added_index',
            'entailed_before','rat_after','sat_target','sat_augmented','polarity_safe','unsafe_import'])
        for mask in range(512):
            base=[c for i,c in enumerate(universe) if mask>>i&1]
            sat_base=bool(satisfying_masks(base,2))
            for ci,c in enumerate(universe):
                for p in c:
                    totals['candidate_pivot_pairs']+=1
                    if not rat(base,c,p):continue
                    totals['rat_valid']+=1
                    implied=entails(base,c,2)
                    totals['rat_valid_not_entailed']+=int(not implied)
                    if bool(satisfying_masks(base+[c],2))!=sat_base:
                        raise AssertionError('RAT test failed satisfiability preservation')
                    for di,d in enumerate(universe):
                        target=base+[d]
                        before=bool(satisfying_masks(target,2))
                        after=bool(satisfying_masks(target+[c],2))
                        unsafe=before and not after
                        safe=-p not in d
                        valid_after=rat(target,c,p)
                        totals['extensions_checked']+=1
                        totals['unsafe_imports']+=int(unsafe)
                        totals['polarity_safe_extensions']+=int(safe)
                        totals['polarity_rule_failures']+=int(safe and (unsafe or not valid_after))
                        if safe and (unsafe or not valid_after):
                            raise AssertionError('polarity sufficient condition failed')
                        if unsafe and first is None:
                            first={'base':base,'candidate':c,'pivot':p,'addition':d,
                                   'target_models':satisfying_masks(target,2)}
                        writer.writerow([mask,ci,p,di,int(implied),int(valid_after),int(before),
                                         int(after),int(safe),int(unsafe)])
    summary={'totals':totals,'first_unsafe_import':first,
             'cpu_seconds':time.process_time()-cpu,'wall_seconds':time.perf_counter()-wall,
             'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
             'workers':1,'randomness':'none','maturity':'finite-check, not a new RAT theorem',
             'boundary':'single-clause additions; NOT a general incremental RAT checker'}
    (out/'rat-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    run(p.parse_args().out)
