"""Run provided Boolean edit inputs through a native solver and checked proofs."""
from __future__ import annotations
import argparse,csv,hashlib,io,json,os,platform,sys,time
from pathlib import Path
from certificates import check_model,reusable,verify
from native_bridge import dimacs,import_bound_dimacs,solve_native
from oracle import satisfying_masks
from survival import compile_survival
from survival_producer import trace_certificate

ROOT=Path(__file__).resolve().parents[1]


def run(output: Path, compare: bool=False) -> dict:
    output=output.resolve()
    if output.exists() or output.is_relative_to(ROOT/'inputs') or output.is_relative_to(ROOT/'src'):
        raise ValueError('native-study output must be a fresh results directory')
    output.mkdir(parents=True)
    rows=[];packets=[];cpu=time.process_time();wall=time.perf_counter()
    inputs=['contract-cases.json','survival-contract-cases.json'];proof_rules=set();source_shapes=set()
    for name in inputs:
        cases=json.loads((ROOT/'inputs'/name).read_text(encoding='utf-8'))
        for case in cases:
            source,target=case['source'],case['target'];label=Path(name).stem+'/'+case['case']
            n=max((abs(v) for form in (source,target) for c in form.values() for v in c),default=0)
            source_shapes.add(json.dumps(source,sort_keys=True))
            bridge=solve_native(source)
            if bridge['status']!='unsat':raise AssertionError('provided source must be UNSAT')
            checked=verify(source,bridge['certificate']);library=[bridge['certificate']]
            native_proofs=[bridge['native_proof']]
            for subset in case.get('proof_subsets',[]):
                answer=solve_native({k:source[k] for k in subset})
                if answer['status']!='unsat':raise AssertionError('provided proof subset must be UNSAT')
                verify(source,answer['certificate']);library.append(answer['certificate']);native_proofs.append(answer['native_proof'])
            circuit=compile_survival(source,trace_certificate(source,library))
            targets=[('provided-edit',target)]+[('delete/'+sid,{k:v for k,v in source.items() if k!=sid}) for sid in sorted(source)]
            record={'case':label,'source':source,'native_version':bridge['native_version'],
                    'source_dimacs':dimacs(source),'source_packets':library,'native_proofs':native_proofs,'queries':[]}
            for kind,current in targets:
                import_bound_dimacs(dimacs(current),current)
                oracle_unsat=not bool(satisfying_masks(current.values(),n))
                answer=solve_native(current)
                if (answer['status']=='unsat')!=oracle_unsat:raise AssertionError('native status differs from truth-table oracle')
                if answer['status']=='sat':
                    if not check_model(current,answer['model']):raise AssertionError('native SAT model rejected')
                else:verify(current,answer['certificate'])
                state=circuit.evaluate(current);survives=circuit.survives(state);single=reusable(checked,current)
                replay=circuit.reconstruct(state) if survives else None
                if replay is not None:
                    verify(current,replay)
                    if not oracle_unsat:raise AssertionError('surviving proof for SAT target')
                row={'case':label,'query':kind,'source_clauses':len(source),'target_clauses':len(current),
                     'native_status':answer['status'],'single_accept':single,'trace_accept':survives,
                     'recovered_over_single':survives and not single,'native_proof_checked':answer['status']=='unsat',
                     'native_model_checked':answer['status']=='sat','trace_replay_checked':replay is not None}
                rows.append(row);record['queries'].append({'query':kind,'target':current,'native':answer,'trace_replay':replay})
            packets.append(record)
    semantic={'input_cases':len(packets),'distinct_identifier_body_sources':len(source_shapes),'queries':len(rows),
              'native_unsat':sum(r['native_status']=='unsat' for r in rows),'native_sat':sum(r['native_status']=='sat' for r in rows),
              'single_accept':sum(r['single_accept'] for r in rows),'trace_accept':sum(r['trace_accept'] for r in rows),
              'recovered_over_single':sum(r['recovered_over_single'] for r in rows),
              'trace_positive_replays':sum(r['trace_replay_checked'] for r in rows),'status_or_replay_mismatches':0,
              'provided_edit_queries':sum(r['query']=='provided-edit' for r in rows),
              'additional_single_deletion_queries':sum(r['query'].startswith('delete/') for r in rows)}
    buffer=io.StringIO(newline='');writer=csv.DictWriter(buffer,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    scientific={'summary':semantic,'rows':rows}
    if compare:
        expected=json.loads((ROOT/'results/native-bridge/scientific.json').read_text(encoding='utf-8'))
        if expected!=scientific:raise AssertionError('native-study scientific rows differ from retained output')
    report={'semantic':semantic,'cpu_seconds':time.process_time()-cpu,'wall_seconds':time.perf_counter()-wall,
      'environment':{'python':platform.python_version(),'system':platform.system(),'release':platform.release(),
        'machine':platform.machine(),'processor':platform.processor(),'logical_cpus':os.cpu_count(),'native_solver':'Z3','native_version':packets[0]['native_version'],'workers':1},
      'input_bindings':{name:hashlib.sha256((ROOT/'inputs'/name).read_bytes()).hexdigest() for name in inputs},
      'scope':'Provided Boolean/CNF contracts and all their single-clause deletions; native asserted/clause-preserving-rewrite/unit-resolution bridge, exact identifier/body map, truth-table/model checks and ordinary proof replay. Not RTL translation or general Z3 proof-format completeness.',
      'comparison_to_retained':True if compare else None}
    (output/'rows.csv').write_text(buffer.getvalue(),encoding='utf-8',newline='')
    (output/'scientific.json').write_text(json.dumps(scientific,indent=2)+'\n',encoding='utf-8')
    (output/'packets.json').write_text(json.dumps(packets,indent=2)+'\n',encoding='utf-8')
    (output/'run.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2));return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--check-retained',action='store_true');args=parser.parse_args();run(args.out,args.check_retained)
