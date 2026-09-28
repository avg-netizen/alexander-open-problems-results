#!/usr/bin/env python3
"""Co-membership loss under within-generation reorderings (added 27 Sep 2026, see the correction box).

The original all-pairs statistic counts every organism pair.  This check also reports, for pairs
that shared an internodon under the reference order, the share separated under the alternative
order (lost co-membership) and the Jaccard overlap of co-member pairs.  Fresh draws, seed 7;
4 genealogies x 6 reorderings per setting.  Writes comembership-check.json.
"""
import json
import random

import numpy as np

from order_robustness import genealogy, rank_from, internodons
from undirforest import undirforest_jointree


def co_pairs(label, n):
    a = [str(label[v]) for v in range(n)]
    return {(i, j) for i in range(n) for j in range(i + 1, n) if a[i] == a[j]}


rng = random.Random(7)
rows = []
for N, sex in ((6, 0.3), (6, 1.0), (12, 1.0), (24, 1.0)):
    lost, jac, allp = [], [], []
    for _ in range(4):
        n, E, gens = genealogy(N, 14, 6, sex, rng)
        r0 = rank_from(gens)
        l0, _ = internodons(n, E, undirforest_jointree(n, E, r0), r0)
        P0 = co_pairs(l0, n)
        for _ in range(6):
            r1 = rank_from(gens, rng)
            l1, _ = internodons(n, E, undirforest_jointree(n, E, r1), r1)
            P1 = co_pairs(l1, n)
            tp, fn, fp = len(P0 & P1), len(P0 - P1), len(P1 - P0)
            lost.append(fn / (tp + fn)); jac.append(tp / (tp + fn + fp)); allp.append((fn + fp) / (n * (n - 1) / 2))
    rows.append({"N": N, "sex": sex, "all_pairs_changed": round(float(np.mean(allp)), 4),
                 "co_member_pairs_lost": round(float(np.mean(lost)), 4),
                 "co_member_jaccard": round(float(np.mean(jac)), 4),
                 "worst_co_member_loss": round(float(max(lost)), 4)})
    print(rows[-1])
json.dump({"seed": 7, "genealogies": 4, "orders_per_genealogy": 6, "rows": rows},
          open("comembership-check.json", "w"), indent=1)
