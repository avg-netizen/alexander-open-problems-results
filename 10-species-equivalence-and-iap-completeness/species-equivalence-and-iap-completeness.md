---
title: "Founding-cohort species classes, and the complexity of IAP"
subtitle: "Resolving Conjecture S1 (note 06) for infinite clusters, and Conjecture 2b (note 09)"
date: "27 September 2026"
---

**Provenance.** Produced by OpenAI Codex during an external audit of this repository (27 September 2026), and checked by Anthropic Claude before inclusion. Hand proofs; no independent human review; priority not established.

**Source.** S. A. Alexander, *Specieslike clusters based on identical ancestor points*, J.
Mathematical Biology, 2026 ([arXiv:2602.05274](https://arxiv.org/abs/2602.05274)): Definitions
1–6 and 8–10, and Theorems 6, 8, 9 and 13. The founding-cohort construction is note 06 of this
repository.

**Results.**
- *Theorem 1.* Infinite maximal founding-cohort clusters and infinite maximal common-ancestor
  clusters represent exactly the same ∼-classes. This proves Conjecture S1, restricted to infinite
  sets as the source's definition of ∼ requires.
- *Theorem 2.* Global IAP is Π⁰₃-complete, even on connected rooted binary trees. This proves
  Conjecture 2b of note 09.

# 1. Founding-cohort and common-ancestor species give the same infinite classes

Write

$$\mathcal C=\mathrm{IAP}\cap\mathrm{CONV}\cap\mathrm{CA}\cap\mathrm{REF},
\qquad
\mathcal F=\mathrm{CONN}\cap\mathrm{IAP}\cap\mathrm{CONV}\cap
\mathrm{REF}\cap\mathrm{FC}.$$

Here IAP prohibits any member from having both infinitely many descendants and
infinitely many non-descendants in the set. CONV includes a vertex whenever it
has an ancestor and a descendant in the set. REF requires any included vertex
with infinitely many descendants in the biosphere to have infinitely many in
the set. CA requires an included common ancestor; FC requires all internal
founders to precede all internal non-founders. Connectedness is undirected.

For an infinite set S, gen(S) consists of members having only finitely many
non-descendants in S. Alexander's equivalence S∼T means
gen(S)△gen(T) is finite; **the published definition is restricted to infinite
sets**. The unqualified conjecture needs that restriction.

**Theorem 1.** Every infinite inclusion-maximal member of $\mathcal F$ is
∼-equivalent to an infinite inclusion-maximal member of $\mathcal C$, and
conversely. Thus the sets of represented ∼-classes agree.

**Proof, forward direction.** Let S be an infinite maximal member of
$\mathcal F$. It has a non-founder: a connected set without any internal
edge is a singleton. All founders precede any fixed non-founder, so there are
only finitely many founders. Following internal parents terminates, since
only finitely many vertices precede any fixed birth. Every vertex is therefore
a founder or a descendant of a founder. At least one founder r has infinitely
many descendants in S.

By IAP at r, the set

$$S_r=\{r\}\cup(\operatorname{desc}_G(r)\cap S)$$

is cofinite in S. It belongs to $\mathcal C$:

- r is its common ancestor.
- IAP is inherited by subsets.
- Convexity follows from convexity of S and transitivity of ancestry.
- If x∈$S_r$ has infinitely many descendants in G, REF for S supplies infinitely
  many in S. All of these descend from r and hence lie in $S_r$. Thus REF holds.

By Alexander's upward-genericity theorem and Zorn's lemma, extend $S_r$ to an
inclusion-maximal M∈$\mathcal C$. It is infinite. Finite branching and
convexity give an infinite directed path starting at r within $S_r$. Every vertex
on this path has infinitely many descendants in both S and M. IAP makes every
one of them a generator of both sets. Consequently

$$|\operatorname{gen}(S)\cap\operatorname{gen}(M)|=\infty.$$

Both S and M are infinite specieslike clusters. Alexander's Objective Species
Theorem (Theorem 6) now gives S∼M. This is the missing comparison in S1.

**Reverse direction.** Let M be an infinite maximal member of
$\mathcal C$. CA plus CONV implies CONN and FC: the common ancestor is
the only internal founder. Thus M∈$\mathcal F$, and the founding-cohort
upward-genericity theorem extends M to a maximal S∈$\mathcal F$.
An infinite path in M again supplies infinitely many common generators of M
and S. The same Objective Species Theorem gives M∼S. ∎

The proof does not show that S and M themselves have finite symmetric
difference, that maximal representatives are unique, or that all representatives
are comparable by inclusion. The forward direction only needs maximality to
match the conjecture's requested output; the argument works for every infinite
S∈$\mathcal F$. Finite maximal clusters can exist, but ∼ is not defined
for them in the cited paper.

# 2. Global IAP is Π⁰₃-complete, even for rooted binary trees

We use a precise observation space. Vertices are numbered by birth order
0,1,2,…, with birthdate t(n)=n. The nth coordinate specifies the finite subset
of {0,…,n−1} that parents vertex n. Each coordinate has the discrete topology;
observations reveal initial coordinates. Ancestry of a fixed earlier vertex
to vertex n is decided by the first n+1 coordinates.

Let $\mathcal B$ be the subspace in which vertex 0 is the only root,
every other vertex has exactly one parent, and every vertex has at most two
children. This is a closed subspace of the coordinate product: violations have
finite witnesses. Its members are connected infinite biospheres satisfying all
four conditions of Alexander's Definition 1.

**Theorem 2.** The set of members of $\mathcal B$ satisfying global IAP
is Π⁰₃-complete under continuous reductions from Cantor space. Global IAP on
the larger birth-coded biosphere space has the same relative upper bound and
is at least this hard.

**Upper bound.** Write D(v,n) for strict ancestry. IAP says precisely

$$\forall v\;\exists (N,b)\in\mathbb N\times\{0,1\}\;
\forall n\ge N\;[D(v,n)=b].$$

The bracketed predicate is clopen. This is a Π⁰₃ definition. It asserts
eventual constancy separately for each vertex, not one common cutoff for all.

**Hardness.** Reduce

$$P_3=\{x\in 2^{\mathbb N\times\mathbb N}:
        \forall k\;\{j:x(k,j)=1\}\text{ is finite}\}.$$

Construct a permanent backbone b₀→b₁→b₂→⋯. At $b_k$ attach a side founder $a_k$.
For each 1 in row k, append one new child to the current tip of $a_k$'s side
chain. Zeros add nothing to that chain. Never join a side chain back to the
backbone or to another side chain.

To make births and continuity explicit, at stage s:

1. Create $b_s$, with parent $b_{s−1}$ when s>0.
2. Create $a_s$, with parent $b_s$.
3. For k=0,…,s in order, inspect x(k,s−k); if it is 1, extend side chain k
   by one vertex.

Assign the created vertices consecutive birth numbers. The backbone supplies
infinitely many births. Every parent is already born; each backbone vertex
has exactly two children, and every side-chain vertex has at most one.
Thus $G_x$∈$\mathcal B$. The first m output vertices depend on only finitely
many input bits (stages through m suffice), so x↦$G_x$ is continuous.

If some row k has infinitely many 1s, $a_k$ has infinitely many descendants along
its side chain and infinitely many non-descendants along the backbone. IAP
fails at $a_k$.

If every row has finitely many 1s, every side-chain vertex has only finitely
many descendants. For $b_k$, its non-descendants lie among the finitely many
earlier backbone vertices and the **finitely many finite** side chains with
indices below k, plus $b_k$ itself. Every later backbone vertex and every side
chain with index at least k descends from $b_k$. Thus $b_k$ has only finitely many
non-descendants. Every vertex satisfies IAP.

Therefore

$$G_x\in\mathrm{IAP}\iff x\in P_3.$$

This answers this repository's concern about unwanted interaction between rows:
put rows successively along a backbone. Only finitely many earlier rows can
contribute non-descendants to any one backbone vertex. ∎

**Why P₃ is complete (included to make the reduction self-contained).**
Write any Π⁰₃ subset A of Cantor space as
$\bigcap_k\bigcup_N F_{k,N}$, where the F's are closed and increasing in N.
At stage s let $m_k$(s) be the least N≤s for which the cylinder of x↾s meets
$F_{k,N}$, or s+1 if none does. For fixed k this integer sequence is
nondecreasing. It is bounded iff x∈$\bigcup_N F_{k,N}$: a surviving closed
candidate eventually bounds it, whereas every fixed candidate is eventually
excluded when x belongs to none. Output a 1 in row k exactly when $m_k$(s)
increases from its preceding value, starting with $m_k$(−1)=0. Each output bit depends on a finite input
prefix. That row is finite iff the integer sequence is bounded, giving a
continuous reduction A≤P₃. The immediate ∀k∃N∀j≥N zero-tail definition supplies
P₃'s upper bound. This is topological completeness; no effectiveness of closed
set presentations is silently assumed.

**Corollary.** Failure of uniform eventual learning persists on connected,
single-founder, outdegree-two biospheres. Moreover, even the fixed side founder
a₀ satisfies IAP iff its row has finitely many 1s. Taking all other rows zero
reduces FIN to that single-organism predicate. FIN is a countable dense Fσ
subset of Cantor space and not Gδ, hence is not guessable even by a
noncomputable finite-prefix guesser. This strengthens this repository's disconnected
two-lineage example without making a claim about learning every possible
species-valued output.

# Status and research connection

The first theorem is a short consequence of Alexander's existing objective
species theorem plus this repository's founding-cohort result. The second supplies
an explicit reduction for this repository's proposed complexity classification.
On locally finite rooted trees it is closely related to uniqueness of an
infinite end; that connection is a reason to be cautious about external
novelty, not a gap in the reduction.

No Lean check was run. The audit controls (`../audit-2026-09-27/controls.py`) check finite
instances of the construction's parent, degree, prefix, and descendant
invariants; the infinite conclusions rest on the proofs above.
