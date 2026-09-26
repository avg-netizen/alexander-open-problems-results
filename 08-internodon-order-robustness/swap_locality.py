#!/usr/bin/env python3
"""Locality of the undirforest under an adjacent swap of birth order (checks the lemma in the note).

For a genealogy with topological order `rank`, and consecutive organisms u (older) and v with no
parent-child edge between them, swap their ranks.  Lemma claims:
  (a) the undirforest is unchanged iff no connected component of G[strictly younger than both]
      is adjacent to both u and v;
  (b) otherwise the family of clades (undirdescendant sets incl. the vertex) changes by exactly one
      clade removed and one added (old inner clade of the pair replaced by the new inner clade);
      every other clade is identical.
Also records the sizes of the removed/added clades (how "drastic" the one change is).
"""
import json
import random
from collections import Counter

from undirforest import random_genealogy, undirforest_jointree


def clades(n, parent):
    ch = {v: [] for v in range(n)}
    for v, p in parent.items():
        if p is not None:
            ch[p].append(v)
    memo = {}
    def cl(v):
        if v not in memo:
            s = {v}
            for c in ch[v]:
                s |= cl(c)
            memo[v] = frozenset(s)
        return memo[v]
    return Counter(cl(v) for v in range(n))


def shared_component(n, edges, rank, u, v):
    younger = {w for w in range(n) if rank[w] > max(rank[u], rank[v])}
    adj = {w: set() for w in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    seen = set()
    for s in younger:
        if s in seen:
            continue
        comp, st = {s}, [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y in younger and y not in comp:
                    comp.add(y); st.append(y)
        seen |= comp
        if any(y in comp for y in adj[u]) and any(y in comp for y in adj[v]):
            return True
    return False


def main():
    rng = random.Random(44)
    stats = Counter()
    sizes = []
    for trial in range(250):
        n, E = random_genealogy(rng.randint(3, 7), rng.randint(2, 6), rng, sexual=rng.random())
        es = set(E)
        order = list(range(n))
        # random linear extension via random within-generation shuffles is implicit; use identity + swaps
        rank = list(range(n))
        base = undirforest_jointree(n, E, rank)
        cb = clades(n, base)
        for i in range(n - 1):
            u, v = order[i], order[i + 1]
            if (u, v) in es or (v, u) in es:
                continue
            r2 = rank[:]; r2[u], r2[v] = r2[v], r2[u]
            f2 = undirforest_jointree(n, E, r2)
            c2 = clades(n, f2)
            shared = shared_component(n, E, rank, u, v)
            changed = f2 != base
            removed = cb - c2; added = c2 - cb
            stats["swaps"] += 1
            stats["shared"] += shared
            stats["lemma_a_ok"] += (changed == shared)
            if shared:
                ok = sum(removed.values()) == 1 and sum(added.values()) == 1
                stats["lemma_b_ok"] += ok
                if ok:
                    sizes.append((len(next(iter(removed))), len(next(iter(added))), n))
    out = {k: v for k, v in stats.items()}
    out["mean_changed_clade_size_share"] = round(sum((a + b) / 2 / n for a, b, n in sizes) / max(1, len(sizes)), 4)
    print(json.dumps(out, indent=1))
    json.dump(out, open("swap-locality.json", "w"), indent=1)


if __name__ == "__main__":
    main()
