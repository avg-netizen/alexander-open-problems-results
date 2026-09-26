#!/usr/bin/env python3
"""Checks for quitters.md in this folder: Proposition 20 of *Intelligence via Ultrafilters* at r <= 0, and
Question 26 under Legg-Hutter normalisation (rewards in [0,1], total <= 1).

DLHA framework (the paper's Definition 1): the environment emits (r1, o1) before any action;
a DLHA maps the reward-observation history to an action; "skip" = action 0.
Quitter A_r (Definition 19): act as A while r1 + ... + rn < r, else skip.

Part 1 (Prop. 20): electorate of copies of one environment e (any ultrafilter gives the same
verdict when all e_n are equal).  e: initial reward 1; first action non-skip -> reward 1/2; then 0.
Part 2 (Q26): a finite family of skip-respecting environments with rewards in [0,1] and total <= 1,
with RANDOM positive weights (standing in for 2^-K, whose values are not needed: every argument is
per trajectory), including e* (initial reward q >= c, then (1-q)/2 for acting once).
Writes quitters_check.json.
"""
import json
import random
from fractions import Fraction as Fr

SKIP = 0


def play(agent, env, steps=12):
    hist, acts, total = [], [], Fr(0)
    for _ in range(steps):
        r, o = env(tuple(acts))
        total += r
        hist += [r, o]
        acts.append(agent(tuple(hist)))
    return total


def quitter(agent, r):
    def q(h):
        return agent(h) if sum(h[0::2]) < r else SKIP
    return q


always1 = lambda h: 1
always_skip = lambda h: SKIP


def env_prop20(acts):
    if not acts:
        return Fr(1), 0
    if len(acts) == 1:
        return (Fr(1, 2) if acts[0] != SKIP else Fr(0)), 0
    return Fr(0), 0


def part1():
    out = {}
    for r in (Fr(-1), Fr(-1, 2), Fr(0), Fr(1, 4)):
        A, B = always1, always_skip
        tA, tB = play(A, env_prop20), play(B, env_prop20)
        tBr, tAr1 = play(quitter(B, r), env_prop20), play(quitter(A, r + 1), env_prop20)
        out[str(r)] = {"A": str(tA), "B": str(tB), "B_r": str(tBr), "A_r+1": str(tAr1),
                       "hypotheses_hold": tA > tB and tBr == tB, "conclusion_A_r+1_beats_B": tAr1 > tB}
    return out


def make_env(initial, bonus, pay_on=1):
    """Initial reward `initial`; the first time the agent plays action `pay_on`, reward `bonus`;
    skip always yields 0; everything else 0.  Total <= initial + bonus <= 1."""
    def e(acts):
        if not acts:
            return initial, 0
        if acts[-1] == pay_on and pay_on not in acts[:-1]:
            return bonus, 0
        return Fr(0), 0
    return e


def part2(trials=200, seed=26):
    rng = random.Random(seed)
    results = {"r>=0 violations": 0, "r<0 counterexamples found": 0, "r<0 cases": 0, "r>=0 cases": 0}
    for _ in range(trials):
        r = Fr(rng.choice([-7, -3, -2, -1, 0, 1, 2]), 4)
        c = r + 1
        fam = [make_env(Fr(rng.randint(0, 3), 4), Fr(rng.randint(0, 1), 4)) for _ in range(6)]
        if c < 1:
            q = max(c, Fr(0)); q = q if q < 1 else Fr(0)
            fam.append(make_env(q, (1 - q) / 2))          # e*: initial q >= c, room to gain
        w = [Fr(rng.randint(1, 50), 64) for _ in fam]
        G = lambda agent: sum(wi * play(agent, e) for wi, e in zip(w, fam))
        if r >= 0:
            # try arbitrary A, B satisfying the hypotheses: random threshold agents
            results["r>=0 cases"] += 1
            for _ in range(20):
                ta, tb = Fr(rng.randint(0, 4), 4), Fr(rng.randint(0, 4), 4)
                A = lambda h, ta=ta: 1 if h[0] >= ta else SKIP
                B = lambda h, tb=tb: 1 if h[0] >= tb else SKIP
                if G(A) > G(B) and G(quitter(B, r)) == G(B) and not G(quitter(A, r + 1)) > G(B):
                    results["r>=0 violations"] += 1
        else:
            results["r<0 cases"] += 1
            A = (lambda h: 1 if h[0] >= c else SKIP) if c > 0 else always1
            B = always_skip
            if G(A) > G(B) and G(quitter(B, r)) == G(B) and G(quitter(A, r + 1)) == G(B):
                results["r<0 counterexamples found"] += 1
    return results


if __name__ == "__main__":
    out = {"proposition_20": part1(), "question_26_LH_normalisation": part2()}
    print(json.dumps(out, indent=1))
    json.dump(out, open("quitters_check.json", "w"), indent=1)
