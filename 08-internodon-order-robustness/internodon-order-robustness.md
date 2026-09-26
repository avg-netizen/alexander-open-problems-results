---
title: "Does the undirforest depend drastically on the birth order?"
subtitle: "On the concluding conjecture of S. A. Alexander, A. de Bruin and D. J. Kornet, *An Alternative Construction of Internodons: The Emergence of a Multi-level Tree of Life* (2015)"
date: "25 September 2026"
---

**Status.**
- The merge-tree identification (§1) and the adjacent-swap locality lemma (§2) are hand proofs,
  each also checked exhaustively on random genealogies.
- §§3 and 5 are finite measurements on one genealogy model.
- No independent review. Whether the merge-tree identification already appears in the
  phylogenetics literature was not checked.

**Source.** S. A. Alexander, A. de Bruin and D. J. Kornet, *An alternative construction of
internodons: the emergence of a multi-level tree of life*, Bulletin of Mathematical Biology, 2015.
[doi:10.1007/s11538-014-0048-2](https://doi.org/10.1007/s11538-014-0048-2). The concluding
conjecture (printed pp. 43–44) reads: the construction takes "a DAG along with distinct
birthdates and produced a forest… We suspect that in some sense, biological undirforests do not
depend drastically on which topological order is used."

**Scripts in this folder.** All are Python 3, using numpy.
- `undirforest.py`: the construction (Definitions 4–5), the join-tree sweep, and a check that the
  two agree.
- `swap_locality.py` → `swap-locality.json`: the check of the §2 lemma.
- `order_robustness.py` → `order-robustness.json`. Its buffered mode (`python3 order_robustness.py
  buffered`) → `order-robustness-buffered.json`.
- `order_robustness_any.py` → `order-robustness-any.json`: arbitrary topological orders.

**Answer in short.**
1. The undirforest **is a merge tree** (the augmented join tree of the genealogy graph, with birth
   order as height). This imports an established stability theory.
2. **Swapping two consecutive, unrelated births changes at most one clade.** It changes nothing
   when no younger component touches both. This is proved below and checked on 4,302 swaps.
3. Under realistic birth-order uncertainty (reordering within generations), the forest changes a
   great deal **at the organism level** (51–87% of undirparents change), but the **internodon
   partition barely moves** (4–10% of organism pairs change status).

So the conjecture is true "in some sense": for clades counted one swap at a time, and for species
partitions. It is false for parent pointers and for the *size* of the one clade that changes.

# 1. The undirforest is a merge tree

By Definition 4, x is an undirancestor of y iff an undirected path from x to y avoids x's elders:
**y lies in x's connected component of G restricted to organisms born no earlier than x.** By
Corollary 6, y's undirparent is its youngest undirancestor.

Now sweep through the organisms from youngest to oldest, adding each to a union-find of the
undirected genealogy. When x is added, every current component adjacent to x merges with it. The
*oldest vertex so far* of each such component receives x as parent. Then:
- that vertex lies in x's component of G[born ≥ x];
- no younger x′ has it in its component, since x′ would have merged it earlier.

So the parent assigned is the youngest undirancestor. This is exactly the **augmented join tree**
(merge tree) of the genealogy graph with height = birth rank, in the sense of Carr–Snoeyink–Axen.

*Check:* the brute-force Definition-4/5 construction and the join-tree sweep agree on 300 random
genealogies with the default order and on 400 under random topological orders
([`undirforest.py`](undirforest.py)).

*Consequence (established literature, not new):* merge trees are stable in the **interleaving
distance**, which is bounded by the sup-norm change of the height function (Morozov, Beketayev and
Weber, "Interleaving distance between merge trees", TopoInVis 2013). Changing the topological
order changes each organism's rank by at most its displacement. The undirforests of two orders
are therefore within interleaving distance **max displacement** of each other, in rank units.
That is a precise, already-proved "does not depend drastically" statement, *for a metric that
measures merge heights*. Combinatorial (edit-type) distances are a different matter. A 2025
preprint, [arXiv 2508.02352](https://arxiv.org/pdf/2508.02352), classifies merge-tree edit
distances by their stability under vertex perturbation; only its title was seen here. §2 and §3
measure what happens combinatorially in this setting.

# 2. Locality of one adjacent swap

**Lemma.** Let u and v be consecutive in the birth order (u older), with no parent–child edge
between them, so swapping them keeps a topological order. Let Y be the set of organisms younger
than both, and classify the connected components of G[Y] as:
- S: those adjacent to both u and v;
- A: adjacent to u only;
- B: adjacent to v only.

Then:
1. **If S is empty, the undirforest is unchanged.**
2. **If S is non-empty,** exactly these parent pointers change: the oldest vertex of each
   component in S (v → u); v (u → w); and u (w → v). Here w is u's former parent. In the clade
   family, **exactly one clade is replaced**: the inner clade {v} ∪ S ∪ B becomes {u} ∪ S ∪ A.
   The outer clade {u, v} ∪ S ∪ A ∪ B, and every other clade, are unchanged.

*Proof.* In the sweep, v is added immediately before u.
- *When S is empty*, u's merges and v's merges involve disjoint sets of components. u and v are
  not adjacent, and their merged components do not touch. Both orders therefore assign the same
  parents and leave the same union-find partition with the same oldest vertices. The rest of the
  sweep is identical.
- *When S is non-empty*, the original order assigns:
  - parent v to the oldest vertices of S and B;
  - then parent u to those of A;
  - and parent u to v, since the merged component touches u.

  The swapped order assigns:
  - u to the oldest vertices of S and A;
  - v to those of B;
  - v to u.

  In both orders the partition after the pair is the same; only its oldest vertex differs (u
  originally, v after the swap). So the vertex w that later receives it as a child is the same.
  All other assignments coincide. The subtrees of all other vertices contain both of u, v or
  neither, so their clades are unchanged. ∎

*Check:* on 4,302 valid adjacent swaps in random genealogies, the forest changed exactly when S
was non-empty (4,302 of 4,302), and every change replaced exactly one clade (1,637 of 1,637)
([`swap-locality.json`](swap-locality.json)).

**Corollary.** Any two topological orders are joined by a sequence of adjacent swaps of
incomparable consecutive organisms. Bubble sort does it, swapping only differently-ordered pairs,
which are incomparable. The number of swaps is the number of differently-ordered pairs. So the
clade families of the two undirforests differ by at most **2 × (number of swaps whose S is
non-empty)** clades, in the Robinson–Foulds sense.

**What stays drastic.** The replaced clade can be large: A and B may contain whole descendant
subtrees. In the random test genealogies, the changed clade averaged 58% of the population.
One swap moves at most one clade, but possibly a big one.

# 3. Measured on genealogies with a permanent split

These are sexual Wright–Fisher-type generations. One ancestral deme of size N splits permanently
into two demes at generation 6, with 14 generations in all. Each child has two parents with
probability "sex", otherwise one. Organisms of the same generation are mutually incomparable, so
*every within-generation reordering is a valid topological order*: this is the realistic birth-order
uncertainty. For each setting: 6 genealogies × 12 random reorderings, compared with a reference
order ([`order-robustness.json`](order-robustness.json)).

| N | sex | organisms | undirparents changed | clades not shared | internodon pairs changed | internodons (ref / alt) |
|---:|---:|---:|---:|---:|---:|---|
| 6 | 0.3 | 132 | 51% | 32% | 8.0% | 12.8 / 13.5 |
| 6 | 1.0 | 132 | 78% | 58% | 6.3% | 9.5 / 9.8 |
| 12 | 0.3 | 264 | 56% | 44% | 6.1% | 32.0 / 32.7 |
| 12 | 1.0 | 264 | 83% | 70% | 6.2% | 20.7 / 19.4 |
| 24 | 0.3 | 528 | 59% | 49% | 4.4% | 63.0 / 63.5 |
| 24 | 1.0 | 528 | 85% | 74% | 6.0% | 39.8 / 42.1 |

(The full table, including sex = 0.7, is in the JSON.)

**With a buffer.** The finite-window SD property counts lineages that would die out later, and
the paper's permanent splits need the infinite future. So the buffered variant evaluates only the
first 10 generations and simulates 4–12 further generations after them.

Internodons in the evaluated part fall from 11–21 to about 5–15. The pair-change rate stays at
**4–10%**, while 70–87% of undirparents change
([`order-robustness-buffered.json`](order-robustness-buffered.json)).

**Reading.** Birth-order uncertainty *within* a generation rewires most organism-level
undirparents. That is expected: the forest's chains through a generation follow birth order. Yet
it leaves species membership (internodon partition) almost intact. That is the paper's "in some
sense": robust where biology looks (the partition into internodons), not where the construction
does its bookkeeping (who is whose undirparent).

# 4. An observation about the definitions

Checking whether internodons respect a permanent deme split turned up a feature of Definitions 7–9,
not a code error.
- **How it happens.** The pre-split ancestral segment can continue unbranched into one daughter
  deme. A childless (hence non-SD) organism of the *other* daughter then joins the internodon of its
  youngest SD ancestor, which lies on that ancestral segment.
- **The result.** An internodon can contain organisms from both sides of a permanent split, through
  non-SD attachment. Whether Kornet's internodons (equivalent by Theorem 20) should allow this is a
  question about the intended treatment of non-SD organisms. It is recorded here and not resolved.
- **The finite window adds noise.** Organisms that die childless inside it are non-SD.

# Status and limits

- **Proved here:** the identification with the join tree, and the adjacent-swap locality lemma
  with its corollary. Both are hand proofs, each also checked exhaustively on random genealogies.
  Whether the merge-tree identification appears in the phylogenetics literature was not checked.
- **Imported, established:** stability of merge trees in the interleaving distance (Morozov et al.
  2013). It was not re-proved here, and its exact hypotheses (vertex-valued height on a graph) should
  be confirmed before the corollary is quoted.
- **Measured, finite:** internodon robustness on one genealogy model. The paper's infinite
  biosphere and permanent-split data are approximated by a finite window with a buffer.
- **Not done:**
  - reorderings *across* generations (for example overlapping generations with continuous
    birthdates);
  - the paper's second suggestion, extending the construction down to gene trees.

# 5. Arbitrary topological orders

[`order_robustness_any.py`](order_robustness_any.py) → `order-robustness-any.json`. Same genealogy
model; the alternative orders are uniformly random topological orders of the whole parent DAG
(the continuous-birthdate case, where uncertainty spans generations). 5 genealogies × 10 orders.

| N | sex | undirparents changed | clades not shared | internodon pairs changed | mean rank displacement (share of n) |
|---:|---:|---:|---:|---:|---:|
| 6 | 0.3 | 57% | 50% | 14.5% | 9.0% |
| 6 | 1.0 | 83% | 76% | 10.7% | 5.5% |
| 12 | 0.3 | 62% | 55% | 10.4% | 9.7% |
| 12 | 1.0 | 87% | 79% | 11.9% | 5.8% |

Internodon co-membership moves about twice as much as under within-generation reorderings (10–14%
of pairs against 4–8%), but most of it still survives. The conjecture's "in some sense" therefore
depends on how much birth-order uncertainty is admitted:
- **within generations:** robust;
- **across generations:** moderately robust.
Neither case is robust at the level of parent pointers.
