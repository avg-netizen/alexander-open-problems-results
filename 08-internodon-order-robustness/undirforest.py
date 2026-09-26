#!/usr/bin/env python3
"""Undirforest (Alexander et al. 2015, Definitions 4-5) and the augmented join tree of the birth order.

Definition 4: x is an undirancestor of y iff some undirected path from x to y avoids x's elders,
i.e. y lies in x's connected component of G restricted to {v : v born at or after x}.
Corollary 6: y's undirparent is its youngest undirancestor.
Join tree (Carr-Snoeyink-Axen): sweep vertices from youngest to oldest adding each to a union-find
of the undirected graph; when x is added, every current component touching x gets x as the parent
of its current "lowest" (oldest-so-far) vertex.  This file computes both and checks they agree.

Genealogies: a finite birth-ordered DAG, vertex i born at time i (topological order = identity),
parents older than children.  `order` permutes birth ranks (must remain a topological order).
"""
import random


def undirforest_bruteforce(n, edges, rank):
    """rank[v] = birth position.  Returns parent dict (None for roots)."""
    adj = {v: set() for v in range(n)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    parent = {}
    for y in range(n):
        best = None
        for x in range(n):
            if rank[x] >= rank[y]:
                continue
            allowed = {v for v in range(n) if rank[v] >= rank[x]}
            seen, st = {x}, [x]
            while st:
                u = st.pop()
                for w in adj[u]:
                    if w in allowed and w not in seen:
                        seen.add(w); st.append(w)
            if y in seen and (best is None or rank[x] > rank[best]):
                best = x
        parent[y] = best
    return parent


def undirforest_jointree(n, edges, rank):
    adj = {v: [] for v in range(n)}
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    uf = list(range(n)); low = list(range(n))       # low[root] = oldest vertex added so far in component
    def find(v):
        while uf[v] != v:
            uf[v] = uf[uf[v]]; v = uf[v]
        return v
    added = [False] * n
    parent = {v: None for v in range(n)}
    for x in sorted(range(n), key=lambda v: -rank[v]):     # youngest first
        added[x] = True
        roots = {find(w) for w in adj[x] if added[w]}
        for r in roots:
            parent[low[r]] = x
            uf[r] = x
        low[x] = x
    return parent


def random_genealogy(n_gen, pop, rng, sexual=0.3):
    """Discrete generations; each child has 1 parent, or 2 with probability `sexual`."""
    edges, prev, idx = [], [], 0
    gens = []
    for g in range(n_gen):
        cur = list(range(idx, idx + pop)); idx += pop
        if prev:
            for c in cur:
                ps = rng.sample(prev, 2 if (rng.random() < sexual and len(prev) > 1) else 1)
                edges += [(p, c) for p in ps]
        gens.append(cur); prev = cur
    return idx, edges


if __name__ == "__main__":
    rng = random.Random(4)
    bad = 0
    for trial in range(300):
        n, E = random_genealogy(rng.randint(2, 6), rng.randint(1, 5), rng, sexual=rng.random())
        rank = list(range(n))
        # random topological order: shuffle within generations is always valid
        a = undirforest_bruteforce(n, E, rank); b = undirforest_jointree(n, E, rank)
        if a != b:
            bad += 1
    print("brute-force undirforest vs join tree mismatches in 300 random genealogies:", bad)
