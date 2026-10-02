"""Measured, exact two-variable edit campaign; resumable by source-formula range."""
from __future__ import annotations
import argparse,csv,itertools,json,resource,time
from pathlib import Path
from certificates import verify,reusable,check_model
from producer import saturate,solve
from oracle import all_clauses,entails,satisfying_masks


def run(out: Path, start: int, stop: int) -> None:
    out.mkdir(parents=True,exist_ok=True)
    start_cpu, start_wall = time.process_time(), time.perf_counter()
    clauses = all_clauses(2)
    ids = [f"a{i}" for i in range(len(clauses))]
    masks = [0] + [1<<i for i in range(9)] + [(1<<i)|(1<<j) for i,j in itertools.combinations(range(9),2)]
    fields = ["source_mask","target_mask","edit_distance","source_unsat","target_unsat",
              "fragments","accepted","entailed","false_accepts","conservative_rejections",
              "stale_unsat_false_accept","reused_unsat"]
    totals = {k:0 for k in fields[5:]}
    total_queries = 0
    first_missed = None
    with (out/f"edits-{start}-{stop}.csv").open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
        for sm in range(start,stop):
            base={ids[i]:clauses[i] for i in range(9) if sm>>i&1}
            generated=saturate(base)
            fragments=[]
            for node in generated["nodes"]:
                if node["kind"]=="resolve":
                    packet={"nodes":generated["nodes"],"root":node["id"]}
                    fragments.append(verify(base,packet))
            cold=solve(base,max_variables=2)
            base_unsat=not bool(satisfying_masks(base.values(),2))
            if (cold["status"]=="unsat") != base_unsat:
                raise AssertionError("producer/oracle disagreement")
            root=None
            if base_unsat:
                root=verify(base,cold["certificate"])
                if root.conclusion:raise AssertionError("nonempty refutation")
            elif not check_model(base,cold["model"]):
                raise AssertionError("invalid model")
            for dm in masks:
                tm=sm^dm
                target={ids[i]:clauses[i] for i in range(9) if tm>>i&1}
                target_unsat=not bool(satisfying_masks(target.values(),2))
                row={"source_mask":sm,"target_mask":tm,"edit_distance":dm.bit_count(),
                     "source_unsat":int(base_unsat),"target_unsat":int(target_unsat),
                     "fragments":len(fragments),"accepted":0,"entailed":0,"false_accepts":0,
                     "conservative_rejections":0,"stale_unsat_false_accept":int(base_unsat and not target_unsat),
                     "reused_unsat":int(root is not None and reusable(root,target))}
                for frag in fragments:
                    accepted=reusable(frag,target)
                    truth=entails(target.values(),frag.conclusion,2)
                    row["accepted"]+=int(accepted)
                    row["entailed"]+=int(truth)
                    row["false_accepts"]+=int(accepted and not truth)
                    row["conservative_rejections"]+=int(not accepted and truth)
                    if not accepted and truth and first_missed is None:
                        first_missed={"source":base,"target":target,"conclusion":frag.conclusion,
                                      "support":frag.support,"source_mask":sm,"target_mask":tm}
                if row["false_accepts"] or (row["reused_unsat"] and not target_unsat):
                    raise AssertionError("reuse unsound")
                for k in totals:totals[k]+=row[k]
                total_queries+=1;writer.writerow(row)
    summary={"dimension":2,"clause_universe":9,"source_range":[start,stop],
             "source_formulas":stop-start,"edit_radius":2,"queries":total_queries,
             "totals":totals,"first_conservative_rejection":first_missed,
             "cpu_seconds":time.process_time()-start_cpu,"wall_seconds":time.perf_counter()-start_wall,
             "peak_rss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
             "workers":1,"randomness":"none; exhaustive ordered enumeration",
             "maturity":"finite-check, not a machine-checked general proof"}
    (out/f"pilot-{start}-{stop}.json").write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    p.add_argument('--start',type=int,default=0);p.add_argument('--stop',type=int,default=512)
    a=p.parse_args()
    if not 0<=a.start<a.stop<=512:p.error('range must lie in [0,512)')
    run(a.out,a.start,a.stop)
