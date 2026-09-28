#!/usr/bin/env python3
"""Bounded audit controls (external audit, 27 September 2026).

Imports reviewed code read-only with bytecode disabled. Checks constructions,
not infinite theorems. No training, solver search, or document rebuilding.
"""
import importlib.util
import itertools
import json
import random
import sys
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent


def genealogy(bit, stages):
    parents, names, tips, backbone = [], [], {}, []
    def add(name, parent):
        idx = len(parents)
        parents.append(parent)
        names.append(name)
        return idx
    for s in range(stages):
        b = add(('backbone', s), backbone[-1] if backbone else None)
        backbone.append(b)
        tips[s] = add(('side', s, 0), b)
        for k in range(s+1):
            if bit(k, s-k):
                tips[k] = add(('side', k, s-k+1), tips[k])
    return parents, names


def graph_checks():
    rng = random.Random(927)
    cases = []
    for case in range(40):
        bits = {(k,j): rng.randrange(2) for k in range(16) for j in range(16-k)}
        bit = lambda k,j: bits.get((k,j), 0)
        parent, names = genealogy(bit, 16)
        assert parent[0] is None and all(p is not None and p<v for v,p in enumerate(parent) if v)
        assert max(Counter(p for p in parent if p is not None).values()) <= 2
        ancestors = []
        for v,p in enumerate(parent):
            ancestors.append(set() if p is None else ancestors[p] | {p})
        for v,name in enumerate(names):
            if name[0]=='side':
                k=name[1]
                assert all(names[w][0]=='side' and names[w][1]==k for w in range(len(parent)) if v in ancestors[w])
            else:
                k=name[1]
                for w,nw in enumerate(names):
                    if nw[0]=='side' and nw[1]>=k:
                        assert v in ancestors[w]
                    if nw[0]=='backbone' and nw[1]>k:
                        assert v in ancestors[w]
        prefix, _ = genealogy(bit, 8)
        assert parent[:len(prefix)]==prefix
        cases.append(len(parent))
    return {'random_triangles': len(cases), 'vertices_checked': sum(cases),
            'invariants': ['one root', 'one older parent', 'outdegree <=2', 'row descendants', 'backbone descendants', 'stage-prefix consistency']}


def kahn_bias():
    # DAG a->c with b isolated. Uniform available-vertex choice is not uniform
    # over its three linear extensions.
    outcomes = {}
    def walk(order, p):
        if len(order)==3:
            outcomes[''.join(order)] = str(p)
            return
        avail = [v for v in 'abc' if v not in order and (v!='c' or 'a' in order)]
        for v in avail:
            walk(order+[v], p/len(avail))
    walk([], F(1))
    assert outcomes == {'abc':'1/4', 'acb':'1/4', 'bac':'1/2'}
    return outcomes


def information():
    def vals(rewards, probs, q):
        plain = max(r-q*(1-p) for r,p in zip(rewards,probs))
        informed = sum(p*max(r-q*(a!=c) for a,r in enumerate(rewards)) for c,p in enumerate(probs))
        copy = sum(p*r for p,r in zip(probs,rewards))
        return list(map(str,(plain,informed,copy)))
    flat = vals([F(0),F(0)],[F(1,2)]*2,F(1,4))
    separated = vals([F(1),F(0)],[F(1,2)]*2,F(1,4))
    assert flat==['-1/8','0','0'] and separated==['7/8','7/8','1/2']
    return {'order': ['plain_optimum','annotated_optimum','copy_query'],
            'flat_reward': flat, 'strict_gain_counterexample': separated,
            'shared_fair_seed_mismatch': '0', 'marginal_erased_action_floor': '1/2'}


def signed_quitting():
    rows=[]
    for r in [F(-4),F(-1),F(-1,3),F(0),F(1,4),F(1),F(7,2),F(20)]:
        if r<=0:
            pair_values=[F(1),F(-1,2)]
            m=4
        else:
            c=r+1
            K=(c.numerator+c.denominator-1)//c.denominator
            L=K+1
            pair_values=[F(1),-F(K,L)]
            m=3
            while F(1,2**m)>=F(1,4*L):m+=1
        margin=sum(pair_values)/4-F(1,2**m)
        assert margin>0
        rows.append({'r':str(r),'special_A_values':list(map(str,pair_values)),
                     'simulation_prefix_bits':m,'positive_margin_at_least':str(margin)})
    comparisons=0
    for c in [F(5,4),F(2),F(7,2),F(5)]:
        K=(c.numerator+c.denominator-1)//c.denominator
        for tape in itertools.product((-1,0,1),repeat=7):
            def run(mode, sign=1):
                total=sign*tape[0]; neg=total<=-K; out=[]
                for potential in tape[1:]:
                    act = (not neg and total<c) if mode=='quitter' else abs(total)<K
                    out.append(int(act))
                    total += sign*potential if act else 0
                    neg |= total<=-K
                return out,total
            assert run('quitter')==run('absolute')
            plus=run('absolute'); minus=run('absolute',-1)
            assert plus[0]==minus[0] and plus[1]==-minus[1]
            comparisons+=1
    return {'special_pairs':rows,'threshold_and_dual_tape_checks':comparisons,
            'scope':'Finite controls; exact cancellation for all environments is a hand proof.'}


def partition_controls():
    sys.path.insert(0,str(REPO/'08-internodon-order-robustness'))
    import order_robustness as o
    from undirforest import undirforest_jointree
    rng=random.Random(927)
    rows=[]
    for N,sex in [(6,.3),(6,1.0),(24,1.0)]:
        for g in range(3):
            n,edges,gens=o.genealogy(N,14,6,sex,rng)
            r0=o.rank_from(gens)
            l0,_=o.internodons(n,edges,undirforest_jointree(n,edges,r0),r0)
            covered=[v for v in range(n) if not isinstance(l0[v],tuple)]
            for trial in range(4):
                r1=o.rank_from(gens,rng)
                l1,_=o.internodons(n,edges,undirforest_jointree(n,edges,r1),r1)
                assert covered==[v for v in range(n) if not isinstance(l1[v],tuple)]
                def metrics(vs):
                    both=old_only=new_only=neither=0
                    for a,b in itertools.combinations(vs,2):
                        x,y=l0[a]==l0[b],l1[a]==l1[b]
                        if x and y:both+=1
                        elif x:old_only+=1
                        elif y:new_only+=1
                        else:neither+=1
                    total=both+old_only+new_only+neither
                    return {'pair_disagreement':(old_only+new_only)/total if total else None,
                            'old_same_pair_loss':old_only/(both+old_only) if both+old_only else None,
                            'positive_pair_jaccard':both/(both+old_only+new_only) if both+old_only+new_only else None,
                            'counts':[both,old_only,new_only,neither]}
                rows.append({'N':N,'sex':sex,'genealogy':g,'order':trial,'organisms':n,
                             'uncovered_by_source_internodons':n-len(covered),
                             'all_vertices':metrics(range(n)),'covered_only':metrics(covered)})
    # Minimal source-definition mismatch: no sexual descendants -> no internodons,
    # but the implementation creates two synthetic singleton labels.
    labels,nsd=o.internodons(2,[(0,1)],{0:None,1:0},[0,1])
    assert nsd==0 and all(isinstance(v,tuple) for v in labels.values())
    return {'comparisons':rows,'asexual_chain_labels':{str(k):v for k,v in labels.items()},
            'warning':'Finite controls under one model, not population-wide estimates.'}


if __name__=='__main__':
    report={'IAP_reduction':graph_checks(),'Kahn_distribution':kahn_bias(),
            'private_information':information(),'signed_quitting':signed_quitting(),
            'internodon_metrics':partition_controls()}
    (HERE/'controls.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Graph controls:',report['IAP_reduction'])
    print('Kahn distribution:',report['Kahn_distribution'])
    print('Signed tape checks:',report['signed_quitting']['threshold_and_dual_tape_checks'])
    rs=report['internodon_metrics']['comparisons']
    for key in ('pair_disagreement','old_same_pair_loss','positive_pair_jaccard'):
        vals=[r['all_vertices'][key] for r in rs if r['all_vertices'][key] is not None]
        print(key, 'range',min(vals),max(vals),'mean',sum(vals)/len(vals))
    print('No-test-organism counts:',sorted(set(r['uncovered_by_source_internodons'] for r in rs)))
