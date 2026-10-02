"""Check an explicit source/proof packet; never trust serialized cache state."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from certificates import read_json, verify, reusable, Rejected


def main() -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',required=True,type=Path,help='JSON map from axiom IDs to clauses')
    p.add_argument('--certificate',required=True,type=Path,help='JSON nodes and root')
    p.add_argument('--target',type=Path,help='optional target JSON formula map')
    args=p.parse_args()
    try:
        checked=verify(read_json(args.source),read_json(args.certificate))
        result={'certificate_valid':True,'conclusion':checked.conclusion,
                'source_unsat_certified':not checked.conclusion,
                'support':checked.support,'nodes_checked':checked.checked_nodes}
        if args.target is not None:
            accepted=reusable(checked,read_json(args.target))
            result.update(reuse_accepted=accepted,
                          target_unsat_certified=accepted and not checked.conclusion)
        print(json.dumps(result,indent=2))
        return 0
    except (Rejected,OSError,TypeError,ValueError,KeyError) as exc:
        print(json.dumps({'certificate_valid':False,'error':str(exc)}),file=sys.stderr)
        return 2

if __name__=='__main__':raise SystemExit(main())
