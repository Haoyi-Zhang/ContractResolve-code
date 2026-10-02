"""Malformed-input, semantic-boundary, and small-oracle regression tests."""
from __future__ import annotations

import sys
from pathlib import Path

SRC = Path(__file__).resolve().parents[1] / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))
import copy
import json
import tempfile
import unittest
from certificates import Rejected, verify, reusable, check_model, read_json, formula
from producer import solve, saturate
from oracle import satisfying_masks, entails, all_clauses
from rat_probe import rat, rup
from activation_probe import encode

BASE = {'request':[1], 'rule':[-1,2], 'bad':[-2]}

class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.packet = solve(BASE)['certificate']

    def reject(self, mutate):
        packet = copy.deepcopy(self.packet)
        mutate(packet)
        with self.assertRaises(Rejected):
            verify(BASE, packet)

    def test_valid_refutation(self):
        checked=verify(BASE,self.packet)
        self.assertEqual(checked.conclusion,())
        self.assertEqual({k for k,_ in checked.support},set(BASE))

    def test_empty_axiom(self):
        p={'nodes':[{'id':'a','kind':'axiom','source':'zero','clause':[]}], 'root':'a'}
        self.assertEqual(verify({'zero':[]},p).conclusion,())

    def test_nonempty_root_is_not_unsat(self):
        p={'nodes':[{'id':'a','kind':'axiom','source':'r','clause':[1]}], 'root':'a'}
        self.assertEqual(verify({'r':[1]},p).conclusion,(1,))

    def test_duplicate_node_identifier(self):
        self.reject(lambda p:p['nodes'].append(copy.deepcopy(p['nodes'][0])))

    def test_missing_root(self):
        self.reject(lambda p:p.update(root='absent'))

    def test_unknown_kind(self):
        self.reject(lambda p:p['nodes'][0].update(kind='trust-me'))

    def test_missing_field(self):
        self.reject(lambda p:p['nodes'][0].pop('clause'))

    def test_untrusted_cached_support(self):
        self.reject(lambda p:p.update(support=[]))

    def test_extra_accepted_flag(self):
        self.reject(lambda p:p.update(verified=True))

    def test_wrong_axiom_body(self):
        self.reject(lambda p:p['nodes'][0].update(clause=[]))

    def test_missing_axiom_id(self):
        self.reject(lambda p:p['nodes'][0].update(source='absent'))

    def test_cycle(self):
        def change(p):
            node=next(n for n in p['nodes'] if n['kind']=='resolve')
            node['left']=node['id']
        self.reject(change)

    def test_forward_reference(self):
        self.reject(lambda p:p['nodes'].reverse())

    def test_wrong_pivot(self):
        def change(p):
            next(n for n in p['nodes'] if n['kind']=='resolve')['pivot']=99
        self.reject(change)

    def test_boolean_pivot_rejected(self):
        def change(p):
            next(n for n in p['nodes'] if n['kind']=='resolve')['pivot']=True
        self.reject(change)

    def test_wrong_resolvent(self):
        self.reject(lambda p:p['nodes'][-1].update(clause=[9]))

    def test_unreachable_bad_node_rejected(self):
        self.reject(lambda p:p['nodes'].append({'id':'unused','kind':'axiom','source':'bad','clause':[]}))

    def test_bad_clauses(self):
        for c in ([0],[True],[1,1],[2,1],[-1,1],[100001],['1']):
            with self.subTest(clause=c), self.assertRaises(Rejected):
                formula({'a':c})

        for bad in ([], [['a', [1]]], None, 3):
            with self.subTest(source=bad), self.assertRaises(Rejected):
                verify(bad, self.packet)

    def test_duplicate_json_key(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'input.json';p.write_text('{"a":[],"a":[1]}')
            with self.assertRaises(Rejected):read_json(p)

    def test_malformed_json(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'input.json';p.write_text('{broken')
            with self.assertRaises(Rejected):read_json(p)

    def test_snapshot_does_not_alias_input(self):
        source=copy.deepcopy(BASE);packet=copy.deepcopy(self.packet)
        checked=verify(source,packet)
        source['rule'][:]=[-2,-1]
        packet['nodes'].clear()
        self.assertFalse(reusable(checked,source))
        self.assertTrue(reusable(checked,BASE))

    def test_replacement_same_id_is_not_retention(self):
        target={**BASE,'rule':[-2,-1]}
        self.assertFalse(reusable(verify(BASE,self.packet),target))
        self.assertTrue(satisfying_masks(target.values(),2))

    def test_irrelevant_addition(self):
        self.assertTrue(reusable(verify(BASE,self.packet),{**BASE,'mode':[3]}))

    def test_irrelevant_deletion(self):
        source={**BASE,'mode':[3]}
        p=solve(source)['certificate']
        self.assertTrue(reusable(verify(source,p),BASE))

    def test_retired_clause_hides_regression_if_not_checked(self):
        target={'request':[1],'bad':[-2]}
        self.assertFalse(reusable(verify(BASE,self.packet),target))
        self.assertTrue(check_model(target,{'1':True,'2':False}))

    def test_semantic_reuse_can_outlive_chosen_support(self):
        source={'a':[-2,-1],'b':[-1,2]}
        generated=saturate(source)
        p={'nodes':generated['nodes'],'root':generated['roots'][(-1,)]}
        checked=verify(source,p)
        target={'c':[-1],'b':[-1,2]}
        self.assertFalse(reusable(checked,target))
        self.assertTrue(entails(target.values(),[-1],2))

    def test_models_are_total_and_boolean(self):
        for model in ({},{'1':True},{'1':1,'2':False},{'1':True,'2':False,'3':True}):
            with self.subTest(model=model):
                self.assertFalse(check_model({'r':[1],'b':[-2]},model))
        self.assertTrue(check_model({},{}))
        self.assertFalse(check_model({'zero':[]},{}))

    def test_all_two_variable_formulas(self):
        clauses=all_clauses(2)
        self.assertEqual(len(clauses),9)
        for mask in range(512):
            base={f'a{i}':c for i,c in enumerate(clauses) if mask>>i&1}
            answer=solve(base,max_variables=2)
            truth=bool(satisfying_masks(base.values(),2))
            self.assertEqual(answer['status']=='sat',truth)
            if truth:self.assertTrue(check_model(base,answer['model']))
            else:self.assertEqual(verify(base,answer['certificate']).conclusion,())

    def test_rat_is_not_entailment(self):
        self.assertTrue(rat([], [1], 1))
        self.assertFalse(entails([], [1], 1))
        self.assertFalse(rat([[-1]], [1], 1))
        self.assertTrue(satisfying_masks([[-1]],1))
        self.assertFalse(satisfying_masks([[-1],[1]],1))

    def test_nonempty_rat_counterexample(self):
        base=[[1,2]]
        self.assertTrue(rat(base,[1],1))
        self.assertTrue(satisfying_masks(base+[[-1]],2))
        self.assertFalse(satisfying_masks(base+[[-1],[1]],2))

    def test_rup_and_tautology(self):
        self.assertTrue(rup([[1],[-1,2]],[2]))
        self.assertFalse(rup([[1,2]],[2]))
        self.assertTrue(rup([],[-1,1]))

    def test_activation_projection(self):
        u=[[1],[-1]]
        for active in (set(),{0},{1},{0,1}):
            actual=[m&1 for m in satisfying_masks(encode(u,active,1),3)]
            expected=satisfying_masks([u[i] for i in sorted(active)],1)
            self.assertEqual(actual,expected)

    def test_oracle_one_pass_iterables(self):
        self.assertTrue(entails([[-1]],iter([-1]),1))
        self.assertFalse(entails([],iter([-1]),1))
        self.assertTrue(entails([[1]],iter([1,1]),1))
        with self.assertRaises(ValueError):entails([],iter([True]),1)

    def test_no_standard_library_name_collision(self):
        import sys
        stdlib_names=getattr(sys,'stdlib_module_names',set())
        source=Path(__file__).resolve().parents[1]/'src'
        self.assertFalse({p.stem for p in source.glob('*.py')} & stdlib_names)

    def test_variable_bounds(self):
        with self.assertRaises(ValueError):solve({'x':[15]},max_variables=0)
        with self.assertRaises(ValueError):satisfying_masks([[3]],2)
        with self.assertRaises(ValueError):satisfying_masks([],17)

if __name__=='__main__':unittest.main(verbosity=2)
