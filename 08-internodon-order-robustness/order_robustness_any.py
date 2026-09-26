#!/usr/bin/env python3
"""Order robustness under ANY topological order (continuous-birthdate uncertainty), not only
within-generation reorderings.  Same genealogy model and metrics as order_robustness.py; the
alternative orders are random linear extensions of the parent DAG (random-available Kahn).
Writes order-robustness-any.json."""
import json, random
import numpy as np
from order_robustness import genealogy, rank_from, clade_sets, internodons, pair_distance
from undirforest import undirforest_jointree

def random_extension(n, edges, rng):
    indeg = [0] * n; ch = {v: [] for v in range(n)}
    for a, b in edges:
        indeg[b] += 1; ch[a].append(b)
    avail = [v for v in range(n) if indeg[v] == 0]; order = []
    while avail:
        v = avail.pop(rng.randrange(len(avail))); order.append(v)
        for c in ch[v]:
            indeg[c] -= 1
            if indeg[c] == 0:
                avail.append(c)
    rank = [0] * n
    for i, v in enumerate(order):
        rank[v] = i
    return rank

rng = random.Random(21)
rows = []
for N in (6, 12):
    for sex in (0.3, 1.0):
        acc = {"parent_diff": [], "clade_diff": [], "internodon_pair_dist": [], "mean_rank_displacement": []}
        for g in range(5):
            n, E, gens = genealogy(N, 14, 6, sex, rng)
            r0 = rank_from(gens); f0 = undirforest_jointree(n, E, r0); c0 = clade_sets(n, f0); l0, _ = internodons(n, E, f0, r0)
            for _ in range(10):
                r1 = random_extension(n, E, rng); f1 = undirforest_jointree(n, E, r1)
                c1 = clade_sets(n, f1); l1, _ = internodons(n, E, f1, r1)
                acc["parent_diff"].append(sum(f0[v] != f1[v] for v in range(n)) / n)
                acc["clade_diff"].append(len(c0 ^ c1) / (len(c0) + len(c1)))
                acc["internodon_pair_dist"].append(pair_distance(l0, l1, n))
                acc["mean_rank_displacement"].append(float(np.mean([abs(r0[v] - r1[v]) for v in range(n)])) / n)
        row = {"N": N, "sex": sex, **{k: round(float(np.mean(v)), 4) for k, v in acc.items()}}
        rows.append(row); print(row, flush=True)
json.dump({"rows": rows}, open("order-robustness-any.json", "w"), indent=1)
