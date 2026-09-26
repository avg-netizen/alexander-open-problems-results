---
title: "Maximal specieslike clusters without a common ancestor"
subtitle: "An answer to the CA-free coverage question in S. A. Alexander, *Specieslike clusters based on identical ancestor points* (2026)"
date: "25 September 2026"
---

**Status.** A hand proof by the same method as the paper's Theorem 9(4). Not machine-checked; no
independent review. The literature was not checked for priority.

**Source.** S. A. Alexander, *Specieslike clusters based on identical ancestor points*, Journal of
Mathematical Biology, 2026. [arXiv:2602.05274](https://arxiv.org/abs/2602.05274),
[doi:10.1007/s00285-026-02361-x](https://doi.org/10.1007/s00285-026-02361-x).

**The question.** After Theorem 13 the paper writes: "We do not currently know of any
qualitatively different sets of constraints which would positively answer Informal Question 4.
We would be particularly interested in a solution not requiring the CA property."

**Result.** Replace the common-ancestor property (CA) by a **founding-cohort** property (FC):
*every member of the cluster with no parent inside it is born before every member that has one.*
- Together with connectedness, the identical ancestor point axiom (IAP), convexity (CONV) and
  reflection (REF), FC is closed under increasing unions.
- So every organism lies in a maximal such cluster.
- Maximal FC clusters need not have a common ancestor: a species founded by a *population* keeps
  its whole founding cohort.
- Any solution without CA must exclude founders who join late (Proposition 4).

# Definitions

The paper's conventions apply (Definition 1: an infinite biosphere G, with parents born before
children, finitely many organisms born before any time, and finitely many children each). For
S ⊆ G:
- a **founder** of S is a member with no parent in S; the others are **non-founders**;
- **CONN**: S is connected, as an undirected subgraph;
- **FC (founding cohort)**: every founder of S is born before every non-founder of S.

**Two facts about FC.**
- If S has a non-founder, FC gives S only finitely many founders: they all predate a fixed
  organism, and G is downward finite.
- If S ∈ CONN has no non-founder, S is a single organism: an internal edge would make its head a
  non-founder.

**Relation to CA.** Under CONV, CA implies CONN and FC. Every member other than the common ancestor
v descends from v, so by convexity its path from v lies in S. It therefore has a parent in S, and v
is the only founder. The converse fails; see the example below. Note also that "exactly one
founder" is *equivalent* to CA, since following parents inside S from any member ends at a founder.
So allowing several founders is the smallest possible departure from CA.

Let $T_{\mathrm{FC}}$ = CONN ∩ IAP ∩ CONV ∩ REF ∩ FC.

# Lemma 1. CONN ∩ FC is upward generic

Let ($C_α$) be an ascending chain in CONN ∩ FC with union C.
- **CONN.** Any two members of C lie in a common $C_α$, where they are connected.
- **FC.** Let r be a founder of C and x a non-founder of C with a parent p ∈ C. Choose γ with
  r, x, p ∈ $C_γ$. Then r is a founder of $C_γ$, since it has no parent even in the larger C. And x is
  a non-founder of $C_γ$, since p ∈ $C_γ$. FC for $C_γ$ gives t(r) < t(x). ∎

# Theorem 2. $T_{\mathrm{FC}}$ is upward generic

Let ($C_α$) be an ascending chain in $T_{\mathrm{FC}}$ with union C.
- **The easy parts.** By Lemma 1 and the paper's Theorem 9(1, 3), C ∈ CONN ∩ FC ∩ CONV ∩ REF.
- **IAP.** Suppose C ∉ IAP. Then some v ∈ C has infinitely many descendants and infinitely many
  non-descendants in C. If C had no non-founder it would be a single organism, so it has one, and
  therefore finitely many founders. Every member of C is a founder or descends from one: follow
  parents inside C, which terminates by downward finiteness. By pigeonhole, some founder w₁ has
  infinitely many descendants in C that are non-descendants of v. Then w₁ is not itself a
  descendant of v.
- **The König path, as in the paper.**
  - w₁ has finitely many children, so some child w₂ has infinitely many descendants in C that are
    non-descendants of v.
  - w₂ ∈ C by convexity (w₁ is an ancestor in C, and w₂ has descendants in C).
  - w₂ is not a descendant of v.
  - Continuing gives an infinite path Q = w₁, w₂, … in C of non-descendants of v.
- **The paper's argument now closes, word for word.** Choose α with v, w₁ ∈ $C_α$.
  - *$C_α$ is infinite.* w₁ has infinitely many descendants in G, so by REF for $C_α$ it has infinitely
    many in $C_α$.
  - *Every $w_n$ lies in $C_α$.* Take β ≥ α with $w_n$ ∈ $C_β$. By REF, $w_n$ has infinitely many descendants
    in $C_β$, so by IAP for $C_β$, $C_β$ contains only finitely many non-descendants of $w_n$. Since
    $C_α$ ⊆ $C_β$ is infinite, $C_α$ contains a descendant of $w_n$. It also contains an ancestor, w₁, so
    convexity gives $w_n$ ∈ $C_α$.
  - *The contradiction.* By REF, v has infinitely many descendants in $C_α$; it also has the
    infinitely many non-descendants w₁, w₂, … there. That contradicts IAP for $C_α$. ∎

**The only change from the paper's proof** of Theorem 9(4) is the source of w₁. The paper takes it
from a single common ancestor; here it comes from finitely many founders, by pigeonhole. FC exists
to make that pigeonhole available.

# Theorem 3. Every organism lies in a $T_{\mathrm{FC}}$-maximal set

For v ∈ G, the paper's Theorem 13 gives S ∋ v in IAP ∩ CONV ∩ CA ∩ REF. By the relation to CA
above, S ∈ $T_{\mathrm{FC}}$. By Theorem 2 and Zorn's lemma (the paper's Theorem 8), S extends to a $T_{\mathrm{FC}}$-maximal
set. Every $T_{\mathrm{FC}}$-maximal set is a specieslike cluster (CONN, IAP, CONV). ∎

# Maximal FC clusters without a common ancestor

**The example.** Let two parentless founders a (born at time 0) and b (born at time 1) be the
parents of every organism of the next generation. Every later organism has two parents in the
previous generation. Assume the whole population P = G satisfies IAP, which the paper argues is
typical of an unsplit sexual population. For a and b it is automatic: each has exactly one
non-descendant in P, the other founder.
- The CA-maximal sets must choose a single common ancestor: {a} ∪ desc(a) = G \ {b}, and
  G \ {a}. Each excludes one founder.
- P satisfies FC: its founders a, b predate everyone else.
- CONV, REF and CONN hold trivially for P = G.
So **P itself is the $T_{\mathrm{FC}}$-maximal cluster**, containing both founders, and it has no common
ancestor.

**The immigrant biosphere, where coverage fails without some constraint.** In the paper's
Fig. 3b, parentless "immigrants" wᵢ join a lineage at ever later times. FC excludes adding a late
founder, so FC behaves like CA there. More generally:

**Proposition 4.** In the Fig. 3b biosphere, any class of G-subsets that contains every
Sₐ = {v₁, v₂, …} ∪ {w₁, …, wₐ} and is contained in IAP has no maximal element containing v₁.
*Proof.*
- A member containing v₁ and infinitely many wᵢ fails IAP at v₁.
- One containing finitely many wᵢ lies inside some Sᵦ, and every Sᵦ is properly contained in
  Sᵦ₊₁. ∎

So any CA-free solution *must* exclude founders who join late, which is what FC does. REF and CONV
remain necessary, by the paper's Example 15 biospheres (a) and (c): there the chains have a single
founder and satisfy FC.

# What this leaves

- **Conjecture (S1).** Every $T_{\mathrm{FC}}$-maximal set is ∼-equivalent (the paper's Definition 6: generator
  sets with finite symmetric difference) to some CA-maximal set, and conversely. The paper's
  objective-species theorem would then be unaffected by the change.
  - *Evidence.* For a $T_{\mathrm{FC}}$-maximal S with founders R, some founder r has infinitely many descendants
    in S. The part $S_r$ = {r} ∪ (desc(r) ∩ S) is in IAP ∩ CONV ∩ CA ∩ REF and differs from S by a
    finite set. That follows from IAP at r. It remains to compare $S_r$ with the CA-maximal sets
    containing it.
- **Biological reading.** FC is a "founding population" convention in place of the paper's
  "definite starting organism": species begin with a cohort, and no organism whose parents are all
  outside the species joins it later. Whether biologists find that more natural than CA is outside
  mathematics.
