"""Finite semantic controls, not a checker for infinite theory closures."""
from itertools import product
from pathlib import Path
import json


def D(i): return ('D', i)
def L(i): return ('L', i)
def K(i, p): return ('K', i, p)
def Not(p): return ('not', p)
def Imp(p, q): return ('imp', p, q)
def And(p, q): return ('and', p, q)
def Or(p, q): return ('or', p, q)


def atoms(p):
    if p[0] in ('D', 'K'):
        return {p}
    if p[0] == 'L':
        return {K(p[1], Not(p))}
    return set().union(*(atoms(q) for q in p[1:]))


def value(p, basic):
    tag = p[0]
    if tag in ('D', 'K'):
        return basic(p)
    if tag == 'L':
        return basic(K(p[1], Not(p)))
    if tag == 'not':
        return not value(p[1], basic)
    a, b = value(p[1], basic), value(p[2], basic)
    if tag == 'imp': return not a or b
    if tag == 'and': return a and b
    if tag == 'or': return a or b
    raise ValueError(p)


def entail(premises, conclusion):
    keys = sorted(set().union(*(atoms(p) for p in premises + [conclusion])), key=repr)
    satisfying = 0
    checked = 0
    for bits in product((False, True), repeat=len(keys)):
        assignment = dict(zip(keys, bits))
        checked += 1
        if all(value(p, assignment.__getitem__) for p in premises):
            satisfying += 1
            assert value(conclusion, assignment.__getitem__), (premises, conclusion, assignment)
    return {'valuations': checked, 'satisfying_premises': satisfying}


def main():
    derivations = []
    for i in range(1, 6):
        li = L(i)
        q = Imp(K(i, Not(li)), Not(li))
        # Expanded-semantics validity; q is not known automatically.
        derivations.append(entail([], Imp(q, Not(li))))
        derivations.append(entail([q], Not(li)))
        for j in range(i + 1, 7):
            mp = Imp(K(j, Imp(q, Not(li))), Imp(K(j, q), K(j, Not(li))))
            derivations.append(entail([K(j, q), K(j, Imp(q, Not(li))), mp], K(j, Not(li))))
        own_mp = Imp(K(i, Imp(q, Not(li))), Imp(K(i, q), K(i, Not(li))))
        contradiction = entail([q, K(i, q), K(i, Imp(q, Not(li))), own_mp], And(li, Not(li)))
        assert contradiction['satisfying_premises'] == 0
        derivations.append(contradiction)

    auxiliary_instances = 0
    negative_controls = 0
    for window, horizon in ((3, 3), (4, 4), (5, 5), (3, 8)):
        basic = lambda p: p[0] == 'K' or p == D(2)
        sample = [D(j) for j in range(1, horizon + 1)] + [L(j) for j in range(1, horizon + 1)]
        sample += [Not(L(1)), K(1, D(1)), Imp(K(1, Not(L(1))), Not(L(1)))]
        assert sum(value(D(j), basic) for j in range(1, window + 1)) == 1
        assert value(And(D(2), K(2, D(3))), basic)
        assert not value(D(1), basic)
        for i in range(1, horizon + 1):
            assert value(L(i), basic) == value(K(i, Not(L(i))), basic) is True
            assert not value(Imp(K(i, Not(L(i))), Not(L(i))), basic)
            # Independently setting L_i false would violate its semantic clause.
            assert False != value(K(i, Not(L(i))), basic)
            negative_controls += 1
            if i < horizon:
                assert value(Imp(Not(D(i)), K(i + 1, Not(D(i)))), basic)
            for p in sample:
                assert value(K(i, Or(p, Not(p))), basic)
                auxiliary_instances += 1
                for q in sample:
                    assert value(Imp(K(i, Imp(p, q)), Imp(K(i, p), K(i, q))), basic)
                    auxiliary_instances += 1
                for j in range(i + 1, horizon + 1):
                    assert value(Imp(K(i, p), K(j, p)), basic)
                    assert value(K(j, Imp(K(i, p), p)), basic)
                    auxiliary_instances += 2

    output = {
        'status': 'finite controls passed; no infinite-closure or full-model certificate',
        'derivation_checks': len(derivations),
        'truth_assignments_checked': sum(x['valuations'] for x in derivations),
        'same_time_factivity_knowledge_obstructions': 5,
        'auxiliary_windows_and_horizons': [[3, 3], [4, 4], [5, 5], [3, 8]],
        'auxiliary_schema_instances': auxiliary_instances,
        'incorrect_independent_L_value_negative_controls': negative_controls,
        'proof_scope': 'countable syntax and theory closures are treated by the hand proof'
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
