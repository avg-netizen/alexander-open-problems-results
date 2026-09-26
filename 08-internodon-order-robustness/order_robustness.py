#!/usr/bin/env python3
"""Order robustness of undirforests and internodons (Alexander et al. 2015, concluding conjecture).

Genealogies: sexual Wright-Fisher-type generations (each child: two distinct parents with
probability `sex`, else one), one ancestral deme of size N that splits permanently into two demes
of size N at generation `split` (no interbreeding afterwards), T generations in all.  Organisms of
one generation are mutually incomparable, so any order WITHIN generations is a valid topological
order: that is the realistic uncertainty in birth order.

For each genealogy, R random within-generation orders are compared with the reference order:
  clades      Robinson-Foulds-style: share of clades (undirdescendant sets) not shared
  parents     share of organisms whose undirparent differs
  internodons partition distance on organisms: share of organism pairs whose same/different-
              internodon status differs (pair-counting; 0 = identical partitions), and the number
              of internodons.
Internodons in the finite window (Definitions 7-9): SD = has a descendant in the window with two
parents; pre-internodons = segments of the undirforest restricted to SD organisms; each non-SD
organism joins the pre-internodon of its youngest SD ancestor.  The window truncation replaces the
paper's infinite-future split data: stated as a limit of the study.
Writes order-robustness.json.
"""
import itertools
import json
import random
import sys

import numpy as np

from undirforest import undirforest_jointree


def genealogy(N, T, split, sex, rng):
    edges, gens, idx = [], [], 0
    demes_prev = None
    for g in range(T):
        if g < split:
            demes = [list(range(idx, idx + N))]; idx += N
        else:
            demes = [list(range(idx, idx + N)), list(range(idx + N, idx + 2 * N))]; idx += 2 * N
        if demes_prev is not None:
            for d_i, deme in enumerate(demes):
                src = demes_prev[0] if len(demes_prev) == 1 else demes_prev[d_i]
                for c in deme:
                    ps = rng.sample(src, 2) if (rng.random() < sex and len(src) > 1) else [rng.choice(src)]
                    edges += [(p, c) for p in ps]
        gens.append([v for d in demes for v in d])
        demes_prev = demes
    return idx, edges, gens


def rank_from(gens, rng=None):
    order = []
    for g in gens:
        g = g[:]
        if rng is not None:
            rng.shuffle(g)
        order += g
    rank = [0] * len(order)
    for i, v in enumerate(order):
        rank[v] = i
    return rank


def clade_sets(n, parent):
    ch = {v: [] for v in range(n)}
    for v, p in parent.items():
        if p is not None:
            ch[p].append(v)
    order = sorted(range(n), key=lambda v: -len(ch[v]))
    memo = {}
    import sys as _s
    _s.setrecursionlimit(100000)
    def cl(v):
        if v not in memo:
            s = {v}
            for c in ch[v]:
                s |= cl(c)
            memo[v] = frozenset(s)
        return memo[v]
    return {cl(v) for v in range(n)}


def internodons(n, edges, parent, rank):
    ch = {v: [] for v in range(n)}; par = {v: [] for v in range(n)}
    for a, b in edges:
        ch[a].append(b); par[b].append(a)
    multi = {v for v in range(n) if len(par[v]) >= 2}
    # SD: has a descendant with >= 2 parents (descendants in the directed genealogy, window-limited)
    sd = set()
    for v in sorted(range(n), key=lambda v: -rank[v]):
        if any((c in multi) or (c in sd) for c in ch[v]):
            sd.add(v)
    # SD forest: undirparent restricted to SD organisms (Prop. 13: SD undirparent of an SD organism is SD)
    sdkids = {v: [] for v in sd}
    for v in sd:
        p = parent[v]
        if p is not None and p in sd:
            sdkids[p].append(v)
    label = {}
    lab = 0
    for v in sorted(sd, key=lambda v: rank[v]):
        p = parent[v]
        if p is not None and p in sd and len(sdkids[p]) == 1:
            label[v] = label[p]
        else:
            label[v] = lab; lab += 1
    # non-SD: youngest SD ancestor's label
    for v in sorted(set(range(n)) - sd, key=lambda v: rank[v]):
        best, stack, seen = None, list(par[v]), set()
        while stack:
            a = stack.pop()
            if a in seen:
                continue
            seen.add(a)
            if a in sd:
                if best is None or rank[a] > rank[best]:
                    best = a
            else:
                stack += par[a]
        label[v] = label[best] if best is not None else ("nosd", v)
    return label, len(sd)


def pair_distance(l1, l2, n):
    a = np.array([hash(l1[v]) for v in range(n)]); b = np.array([hash(l2[v]) for v in range(n)])
    same1 = a[:, None] == a[None, :]; same2 = b[:, None] == b[None, :]
    iu = np.triu_indices(n, 1)
    return float((same1[iu] != same2[iu]).mean())


def deme_of(gens, split, N):
    """0 = ancestral (before split), 1 / 2 = daughter demes (first / second N of each later generation)."""
    d = {}
    for g, members in enumerate(gens):
        for i, v in enumerate(members):
            d[v] = 0 if g < split else (1 + (i >= N))
    return d


def buffered(N, sex, T_eval, buffer, split, R, G, rng):
    """Evaluate only organisms born in the first T_eval generations; `buffer` further generations
    let lineages reconnect so that branchings in the evaluated part reflect lasting splits."""
    acc = {"internodon_pair_dist": [], "n_internodons": [], "deme_purity": [], "parent_diff": []}
    for g in range(G):
        n, E, gens = genealogy(N, T_eval + buffer, split, sex, rng)
        ev = [v for gg in gens[:T_eval] for v in gg]
        dm = deme_of(gens, split, N)
        r0 = rank_from(gens); f0 = undirforest_jointree(n, E, r0); l0, _ = internodons(n, E, f0, r0)
        labs = {}
        for v in ev:
            labs.setdefault(str(l0[v]), set()).add(dm[v])
        acc["n_internodons"].append(len(labs))
        acc["deme_purity"].append(sum(1 for s_ in labs.values() if len(s_ - {0}) <= 1) / len(labs))
        for _ in range(R):
            r1 = rank_from(gens, rng); f1 = undirforest_jointree(n, E, r1); l1, _ = internodons(n, E, f1, r1)
            m = len(ev)
            idx = {v: i for i, v in enumerate(ev)}
            acc["internodon_pair_dist"].append(pair_distance({idx[v]: l0[v] for v in ev}, {idx[v]: l1[v] for v in ev}, m))
            acc["parent_diff"].append(sum(f0[v] != f1[v] for v in ev) / m)
    return {k: round(float(np.mean(v)), 4) for k, v in acc.items()}


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "buffered":
        rng = random.Random(16)
        rows = []
        for N in (6, 12):
            for sex in (0.7, 1.0):
                for buffer in (0, 4, 8, 12):
                    r = {"N": N, "sex": sex, "buffer": buffer, **buffered(N, sex, 10, buffer, 4, 8, 5, rng)}
                    rows.append(r); print(r, flush=True)
        json.dump({"T_eval": 10, "split": 4, "rows": rows}, open("order-robustness-buffered.json", "w"), indent=1)
        return
    rng = random.Random(15)
    configs = [(N, sex) for N in (6, 12, 24) for sex in (0.3, 0.7, 1.0)]
    T, split, R, G = 14, 6, 12, 6
    out = []
    for N, sex in configs:
        acc = {"clade_diff": [], "parent_diff": [], "internodon_pair_dist": [], "n_internodons_ref": [],
               "n_internodons_alt": [], "sd_share": []}
        for g in range(G):
            n, E, gens = genealogy(N, T, split, sex, rng)
            r0 = rank_from(gens)
            f0 = undirforest_jointree(n, E, r0)
            c0 = clade_sets(n, f0)
            l0, nsd = internodons(n, E, f0, r0)
            for _ in range(R):
                r1 = rank_from(gens, rng)
                f1 = undirforest_jointree(n, E, r1)
                c1 = clade_sets(n, f1)
                l1, _ = internodons(n, E, f1, r1)
                acc["clade_diff"].append(len(c0 ^ c1) / (len(c0) + len(c1)))
                acc["parent_diff"].append(sum(f0[v] != f1[v] for v in range(n)) / n)
                acc["internodon_pair_dist"].append(pair_distance(l0, l1, n))
                acc["n_internodons_ref"].append(len(set(map(str, l0.values()))))
                acc["n_internodons_alt"].append(len(set(map(str, l1.values()))))
                acc["sd_share"].append(nsd / n)
        row = {"N": N, "sex": sex, "organisms": n, **{k: round(float(np.mean(v)), 4) for k, v in acc.items()}}
        out.append(row)
        print(row, flush=True)
    json.dump({"T": T, "split": split, "orders_per_genealogy": R, "genealogies": G, "rows": out},
              open("order-robustness.json", "w"), indent=1)


if __name__ == "__main__":
    main()
