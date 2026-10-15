"""Optional native Boolean solver and a checked unit-resolution proof bridge.

Z3 searches; this module translates only asserted clauses, clause-preserving
rewrites and unit-resolution steps. The ordinary checker validates the emitted
packet. Other proof rules are rejected rather than trusted or recast as SAT.
"""
from __future__ import annotations
from typing import Any
from certificates import Rejected, check_model, formula, verify


def dimacs(source: dict[str, Any]) -> str:
    base=formula(source)
    n=max((abs(v) for c in base.values() for v in c),default=0)
    return f"p cnf {n} {len(base)}\n"+''.join(' '.join(map(str,base[k]))+(' ' if base[k] else '')+'0\n' for k in sorted(base))


def import_bound_dimacs(text: str, source: dict[str, Any]) -> dict[str, tuple[int,...]]:
    """Bind DIMACS positions to the explicit stable-ID/canonical-body source map."""
    base=formula(source)
    if not isinstance(text,str) or len(text)>32*1024*1024:raise Rejected('DIMACS input too large')
    header=None;clauses=[];current=[]
    for line in text.splitlines():
        line=line.strip()
        if not line or line.startswith('c'):continue
        if line.startswith('p'):
            if header is not None or clauses or current:raise Rejected('duplicate or misplaced DIMACS header')
            fields=line.split()
            if len(fields)!=4 or fields[:2]!=['p','cnf']:raise Rejected('invalid DIMACS header')
            try:header=tuple(map(int,fields[2:]))
            except ValueError as exc:raise Rejected('invalid DIMACS bounds') from exc
            if not 0<=header[0]<=100000 or not 0<=header[1]<=100000:raise Rejected('DIMACS bounds exceeded')
            continue
        if header is None:raise Rejected('DIMACS header missing')
        for token in line.split():
            try:v=int(token)
            except ValueError as exc:raise Rejected('invalid DIMACS literal') from exc
            if abs(v)>header[0]:raise Rejected('DIMACS variable out of bounds')
            if v==0:
                clauses.append(tuple(current));current=[]
                if len(clauses)>header[1]:raise Rejected('too many DIMACS clauses')
            else:
                current.append(v)
                if len(current)>1000:raise Rejected('DIMACS clause too long')
    if header is None or current or len(clauses)!=header[1]:raise Rejected('incomplete DIMACS formula')
    expected=[base[k] for k in sorted(base)]
    if clauses!=expected:raise Rejected('DIMACS identity/body manifest mismatch')
    return base


def _z3_clause(expr, variables, z3) -> tuple[int,...]:
    if z3.is_false(expr):return ()
    values=expr.children() if z3.is_or(expr) else [expr]
    literals=[]
    for value in values:
        negative=False
        while z3.is_not(value):negative=not negative;value=value.arg(0)
        if not z3.is_const(value) or not z3.is_bool(value) or value.decl().name() not in variables:
            raise Rejected('native proof conclusion is not an admitted Boolean clause')
        v=variables[value.decl().name()];literals.append(-v if negative else v)
    body=tuple(sorted(set(literals)))
    if any(-v in body for v in body):raise Rejected('tautological native clause unsupported')
    return body


def elaborate(source: dict[str, Any], proof) -> dict[str, Any]:
    import z3
    base=formula(source)
    variables={f'v_{v}':v for c in base.values() for v in map(abs,c)}
    by_body={}
    for sid,c in sorted(base.items()):by_body.setdefault(c,sid)
    nodes=[];memo={};bodies={};stack=[(proof,False)]
    while stack:
        item,ready=stack.pop();key=item.get_id()
        if key in memo:continue
        if len(memo)+len(stack)>100000:raise Rejected('native proof budget exceeded')
        kind=item.decl().kind();args=item.children()
        if kind==z3.Z3_OP_PR_ASSERTED:
            if len(args)!=1:raise Rejected('invalid asserted proof')
            body=_z3_clause(args[0],variables,z3)
            if body not in by_body:raise Rejected('native axiom missing exact source body')
            ident=f'n{len(nodes)}';nodes.append({'id':ident,'kind':'axiom','source':by_body[body],'clause':list(body)})
            memo[key]=ident;bodies[ident]=body;continue
        if kind==z3.Z3_OP_PR_MODUS_PONENS:
            if len(args)!=3:raise Rejected('invalid native rewrite proof')
            parents=[args[0]]
        elif kind==z3.Z3_OP_PR_UNIT_RESOLUTION:
            if len(args)<3:raise Rejected('invalid native unit resolution')
            parents=args[:-1]
        else:raise Rejected('unsupported native proof rule: '+str(item.decl().name()))
        if not ready:
            stack.append((item,True));stack.extend((x,False) for x in reversed(parents));continue
        expected=_z3_clause(args[-1],variables,z3)
        current=memo[parents[0].get_id()];body=bodies[current]
        if kind==z3.Z3_OP_PR_MODUS_PONENS:
            if body!=expected:raise Rejected('native rewrite changes the canonical clause')
        else:
            for parent in parents[1:]:
                unit_id=memo[parent.get_id()];unit=bodies[unit_id]
                if len(unit)!=1 or -unit[0] not in body:raise Rejected('native resolution premise is not a complementary unit')
                literal=unit[0];out=tuple(x for x in body if x!=-literal)
                left,right=(unit_id,current) if literal>0 else (current,unit_id)
                ident=f'n{len(nodes)}'
                nodes.append({'id':ident,'kind':'resolve','left':left,'right':right,'pivot':abs(literal),'clause':list(out)})
                current=ident;body=out;bodies[current]=body
            if body!=expected:raise Rejected('native resolution conclusion mismatch')
        memo[key]=current
    packet={'nodes':nodes,'root':memo[proof.get_id()]}
    checked=verify(base,packet)
    if checked.conclusion:raise Rejected('native UNSAT proof has a nonempty root')
    return packet


def solve_native(source: dict[str, Any]) -> dict[str, Any]:
    import z3
    base=import_bound_dimacs(dimacs(source),source)
    ctx=z3.Context(proof=True);solver=z3.Solver(ctx=ctx)
    solver.set(timeout=10000,random_seed=0)
    atoms={v:z3.Bool(f'v_{v}',ctx=ctx) for c in base.values() for v in map(abs,c)}
    for sid,c in sorted(base.items()):
        terms=[atoms[abs(v)] if v>0 else z3.Not(atoms[-v]) for v in c]
        solver.add(terms[0] if len(terms)==1 else z3.Or(*terms) if terms else z3.BoolVal(False,ctx=ctx))
    answer=solver.check()
    if answer==z3.sat:
        model={str(v):z3.is_true(solver.model().eval(a,model_completion=True)) for v,a in atoms.items()}
        if not check_model(base,model):raise Rejected('native SAT model fails the ordinary model checker')
        return {'status':'sat','model':model,'native_version':z3.get_version_string()}
    if answer!=z3.unsat:raise Rejected('native solver returned '+str(answer))
    proof=solver.proof();packet=elaborate(base,proof)
    return {'status':'unsat','certificate':packet,'native_proof':proof.sexpr(),'native_version':z3.get_version_string()}
