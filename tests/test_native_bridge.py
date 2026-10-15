"""Native proof and stable clause-identity bridge regressions."""
from pathlib import Path
import importlib.util,sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from certificates import Rejected,reusable,verify
from native_bridge import dimacs,import_bound_dimacs,solve_native,elaborate
from survival import compile_survival
from survival_producer import trace_certificate


class DimacsBinding(unittest.TestCase):
    def test_roundtrip_ids_and_duplicate_bodies(self):
        source={'x':[1],'copy':[1],'bad':[-1]}
        self.assertEqual(import_bound_dimacs(dimacs(source),source),{k:tuple(v) for k,v in source.items()})

    def test_changed_or_reordered_bodies_rejected(self):
        source={'a':[1],'b':[-1]}
        for text in ('p cnf 1 2\n-1 0\n1 0\n','p cnf 1 2\n1 0\n1 0\n'):
            with self.assertRaises(Rejected):import_bound_dimacs(text,source)

    def test_malformed_dimacs_rejected(self):
        for text in ('1 0\n','p cnf 1 1\n1','p cnf 1 1\n2 0\n','p cnf 1 1\np cnf 1 1\n1 0\n'):
            with self.assertRaises(Rejected):import_bound_dimacs(text,{'a':[1]})


@unittest.skipUnless(importlib.util.find_spec('z3'),'optional z3-solver dependency not installed')
class NativeProofs(unittest.TestCase):
    def test_native_unsat_replayed(self):
        source={'request':[1],'rule':[-1,2],'bad':[-2]}
        answer=solve_native(source)
        self.assertEqual(answer['status'],'unsat');self.assertEqual(verify(source,answer['certificate']).conclusion,())

    def test_native_sat_model(self):
        self.assertEqual(solve_native({'a':[1],'b':[-1,2]})['status'],'sat')

    def test_native_duplicate_alternative(self):
        source={'request':[1],'rule_a':[-1,2],'rule_b':[-1,2],'bad':[-2]}
        packet=solve_native(source)['certificate'];checked=verify(source,packet)
        selected=next(k for k,_ in checked.support if k.startswith('rule_'))
        target={k:v for k,v in source.items() if k!=selected}
        self.assertFalse(reusable(checked,target))
        circuit=compile_survival(source,trace_certificate(source,[packet]));state=circuit.evaluate(target)
        self.assertTrue(circuit.survives(state));verify(target,circuit.reconstruct(state))

    def test_changed_identity_body_cannot_replay(self):
        source={'a':[1],'b':[-1]};packet=solve_native(source)['certificate']
        with self.assertRaises(Rejected):verify({'a':[2],'b':[-1]},packet)

    def test_unadmitted_native_axiom_rejected(self):
        import z3
        ctx=z3.Context(proof=True);solver=z3.Solver(ctx=ctx);x=z3.Bool('v_1',ctx=ctx)
        solver.add(x,z3.Not(x));self.assertEqual(solver.check(),z3.unsat)
        with self.assertRaises(Rejected):elaborate({'a':[1]},solver.proof())


if __name__=='__main__':unittest.main()
