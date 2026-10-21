---
title: "A bounded-founder alternative that allows late founders"
subtitle: "A second CA-free answer to the coverage question of Alexander's *Specieslike clusters* (2026), and a correction to note 06"
date: "27 September 2026"
---

**Provenance.** Produced by OpenAI Codex during an external audit of this repository (27 September 2026), and checked by Anthropic Claude before inclusion. Hand proofs; no independent human review; priority not established.

The conclusion after Proposition 4 in note 06 is too strong: the immigrant example does **not** imply that every CA-free
coverage solution must exclude every late founder. It implies that an
IAP-contained class cannot admit all the successive immigrant extensions in
that example and still have the desired maximality property.

Here is a different constraint that permits late founders while retaining
upward genericity and coverage.

# Definitions

Use Alexander's infinite-biosphere assumptions: parents precede children,
finitely many vertices precede every real time, each vertex has finitely many
children, and the graph is infinite. A founder of S has no parent in S.
Work with nonempty clusters throughout. For a fixed integer N≥1 put

$$\mathcal F_N=\mathrm{CONN}\cap\mathrm{IAP}\cap\mathrm{CONV}\cap
\mathrm{REF}\cap\{S:\text{S has at most N founders}\}.$$

CONN is undirected connectedness; IAP, CONV, REF have the definitions in
note 10.
The bound N is fixed for the whole class, not chosen anew for each member.

# Theorem

For every N≥1, $\mathcal F_N$ is closed under nonempty increasing-chain
unions, and every organism lies in an inclusion-maximal member. For N=1 it
is exactly Alexander's IAP∩CONV∩CA∩REF class. For N≥2 it admits maximal
clusters with no common ancestor and with a founder born after a non-founder.

**Proof of closure.** Let C be the union of an increasing chain $C_α$ in
$\mathcal F_N$. CONN, CONV and REF pass to C by the usual finite-witness
and inclusion arguments. If C had N+1 founders, some stage would contain all
of them. They would remain founders there, contradicting its bound N.

Every vertex of C descends from an internal founder or is one: internal parent
chains terminate by finite ancestry. Suppose IAP fails at v∈C. There are
infinitely many descendants and non-descendants of v in C. Among the at most
N founders, some w₁ has infinitely many descendants in C that do not descend
from v. Finite branching and convexity produce an infinite path
w₁,w₂,… in C, none descending from v.

Choose α containing v,w₁. REF makes $C_α$ infinite. For each n>1 choose β≥α
containing $w_n$. REF gives $w_n$ infinitely many descendants in $C_β$, so IAP
makes its non-descendants in $C_β$ finite. The infinite subset $C_α$ must contain
a descendant of $w_n$. It already contains its ancestor w₁; convexity therefore
puts $w_n$ in $C_α$. Thus $C_α$ contains infinitely many non-descendants of v.
REF also gives it infinitely many descendants of v, contradicting its IAP.
Closure follows.

**Coverage.** Alexander's Theorem 13 supplies each organism with a containing
CA/CONV/IAP/REF cluster. CA and convexity give exactly one founder and
connectedness, so that cluster belongs to $\mathcal F_N$. Chain closure
and Zorn's lemma extend it to a maximal member.

**N=1.** A single founder is the ancestor of every other included organism,
by termination of internal parent chains. Conversely CA and convexity force
the common ancestor to be the unique founder. This proves the equality of
classes. ∎

# Explicit late-founder example

Take vertices a₀,a₁,a₂,b,c₀,c₁,… in that birth order, with edges

$$a_0\to a_1\to a_2\to c_0\to c_1\to\cdots,
\qquad b\to c_0.$$

Let birthdates be consecutive integers and let S be the whole biosphere.
Its founders are a₀ and b. Founder b is later than the non-founders a₁,a₂,
so **FC fails**. Yet every vertex has all but finitely many vertices as
descendants: IAP holds. Connectedness, convexity and reflection hold for S=G.
It belongs to $\mathcal F_2$, and is maximal because it is all of G.
It has no common ancestor: neither founder descends from the other.

Thus fixed finite founder budgets, unlike the FC time condition, can admit
late immigration. The choice of N is an extra convention whose biological
merit is not established by the proof.

Allowing “some finite number of founders” **without one bound N for the
class** does not give this argument: a chain can accumulate infinitely many
founders. The paper's immigrant counterexample shows why that difference
matters.

# Infinite species classes still agree

The proof of Theorem 1 of note 10
uses finiteness of founders, REF, IAP and CONV; it does not use the FC birth-time
inequality after finiteness is established. Consequently, for each N≥1, the
infinite maximal members of $\mathcal F_N$ represent exactly the same
generator-equivalence classes as the infinite CA-maximal members.

This is another answer to the CA-free coverage request after Theorem 13 of
[Alexander's paper](https://arxiv.org/abs/2602.05274). It changes which finite
founding histories are admitted while preserving the represented infinite
species classes. It does not identify finite clusters under the paper's
infinite-set equivalence relation.
