"""End-to-end small Boolean contract queries, proof replay and regression models."""
from __future__ import annotations
import argparse,json,time,resource
from pathlib import Path
from producer import solve
from certificates import verify,reusable,check_model,read_json
from oracle import satisfying_masks


def run(inputs: Path,out: Path) -> None:
    out.mkdir(parents=True,exist_ok=True)
    cpu,wall=time.process_time(),time.perf_counter()
    rows=[]
    for case in read_json(inputs):
        old=solve(case['source']);new=solve(case['target'])
        if old['status']!='unsat':raise AssertionError('source must be UNSAT')
        checked=verify(case['source'],old['certificate'])
        reuse=reusable(checked,case['target'])
        n=max(abs(l) for cs in (case['source'],case['target']) for c in cs.values() for l in c)
        if checked.conclusion or satisfying_masks(case['source'].values(),n):
            raise AssertionError('source is not independently certified UNSAT')
        oracle_sat=bool(satisfying_masks(case['target'].values(),n))
        if (new['status']=='sat')!=oracle_sat or new['status']!=case['expected']:
            raise AssertionError('contract case status disagrees with oracle/expected')
        if new['status']=='sat':
            if not check_model(case['target'],new['model']) or reuse:
                raise AssertionError('invalid regression model or unsound reuse')
        else:
            if verify(case['target'],new['certificate']).conclusion:
                raise AssertionError('invalid target refutation')
        packet={'case':case['case'],'source_formula':case['source'],'target_formula':case['target'],
                'source_answer':old,'target_answer':new,'reuse_accepted':reuse,
                'root_support':checked.support,'oracle_model_masks':satisfying_masks(case['target'].values(),n)}
        (out/(case['case']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        rows.append({'case':case['case'],'variables':n,'source_clauses':len(case['source']),
                     'target_clauses':len(case['target']),'status':new['status'],
                     'reuse_accepted':reuse,'source_proof_nodes':len(old['certificate']['nodes']),
                     'target_search_nodes':new['search_nodes']})
    summary={'cases':rows,'cpu_seconds':time.process_time()-cpu,'wall_seconds':time.perf_counter()-wall,
             'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'workers':1,
             'maturity':'toy end-to-end checks; not deployed firmware/hardware validation'}
    (out/'contract-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--inputs',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True);a=p.parse_args();run(a.inputs,a.out)
