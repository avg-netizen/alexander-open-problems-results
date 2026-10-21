---
title: "Specieslike clusters with several founders"
subtitle: "Maximality, infinite species classes, and the complexity of the ancestor-point axiom"
date: "21 October 2026"
abstract: |
  Alexander asks for constraints that put every organism in a maximal
  specieslike cluster without requiring an included common ancestor.
  We give two such choices: a founding-cohort condition and any fixed
  finite bound on the number of founders. Both retain chain closure and
  coverage; the second also permits founders born after non-founders.
  Their infinite maximal clusters represent exactly the same
  generator-equivalence classes as Alexander's common-ancestor clusters.
  The common proof identifies the role of finitely many founders in the
  maximality argument. We then examine what can be learned from finite
  genealogical observations. Global satisfaction of the identical
  ancestor point axiom is complete at the third Borel level, already
  for connected rooted trees of outdegree at most two. This descriptive
  complexity statement concerns a yes/no property of a biosphere.
  It does not assert impossibility of every form of species classification.
---

# 1. The coverage question

A genealogical definition of species faces two different tasks. It must
say which sets of organisms qualify, and it must ensure that the
definition actually covers the organisms under consideration. A
collection of plausible local conditions need not give the second
property: an organism can belong to successively larger qualifying sets
without belonging to any maximal one.

Alexander's *Specieslike clusters based on identical ancestor points*
[A] makes this issue precise. A specieslike cluster is a connected,
ancestrally convex set satisfying the identical ancestor point axiom.
That axiom prohibits a member from having both infinitely many
descendants and infinitely many non-descendants inside the set.
Alexander proves coverage after adding reflection and a common-ancestor
condition. Following his Theorem 13, he asks for alternatives that do
not require that common ancestor.

The common ancestor must itself belong to the cluster. This distinction
matters for a population founded by several organisms: a cluster can
have a unified subsequent history without containing one organism
ancestral to all its founders. Our alternatives allow such populations.

The first condition requires every internal founder to be born before
every internal non-founder. The second fixes a finite upper bound on
the number of founders while placing no such restriction on their
birthdates. Both guarantee coverage. Their difference is visible in
the following genealogy:
\[
 a_0\longrightarrow a_1\longrightarrow a_2
       \longrightarrow c_0\longrightarrow c_1\longrightarrow\cdots,
 \qquad b\longrightarrow c_0.
\]
Take the birth order to be \(a_0,a_1,a_2,b,c_0,c_1,\ldots\).
The whole biosphere has two founders, \(a_0,b\), and no common ancestor.
Founder \(b\) arrives after two non-founders. The fixed bound of two
admits this biosphere; the founding-cohort condition excludes it.

![Two ways finite founding histories enter the argument. Left: a late founder joins an existing lineage. Right: the backbone and side chains used in the complexity proof. Arrows are parent-to-child.](figures/founders-and-backbone.pdf){width=95%}

Three results organize the paper. Section 4 proves coverage for both
alternatives through one chain argument. Section 5 shows that they
preserve the infinite species classes defined in [A]. Section 7 proves
a descriptive-complexity theorem explaining a limit of finite
observation, even when the genealogy has a single founder.

# 2. Biospheres, clusters, and founders

We use Alexander's infinite-biosphere assumptions [A, Definition 1].
The directed graph \(G\) has a real birthdate \(t(v)\) for each vertex.
Parents are born strictly before children; only finitely many vertices
are born before any fixed real time; every vertex has finitely many
children; and \(G\) is infinite. These assumptions imply finite ancestry:
following parents backwards from a fixed vertex cannot continue
indefinitely.

An ancestor or descendant is always strict: an organism is not its own
ancestor. Write \(\operatorname{Desc}(v)\) for all descendants of \(v\)
in \(G\). For a nonempty subset \(S\subseteq G\), the relevant conditions
are as follows.

- **Connectedness (CONN):** the undirected graph induced on \(S\) is connected.
- **Identical ancestor point (IAP):** for each \(v\in S\), at least one of
  \(S\cap\operatorname{Desc}(v)\) and
  \(S\setminus\operatorname{Desc}(v)\) is finite.
- **Convexity (CONV):** every vertex having both an ancestor and a
  descendant in \(S\) belongs to \(S\).
- **Reflection (REF):** if \(v\in S\) has infinitely many descendants in
  \(G\), it has infinitely many descendants in \(S\).
- **Common ancestor (CA):** some \(r\in S\) is an ancestor of every
  member of \(S\setminus\{r\}\).

IAP describes the internal distribution of descendants; REF compares
the internal genealogy with the surrounding biosphere. They do
different work. In particular, REF prevents a qualifying cluster from
discarding almost all of the future of one of its members.

A **founder of \(S\)** is a member with no parent in \(S\).
This is relative to \(S\): an organism can be a founder of a cluster
while having parents outside it. Denote the founder set by \(R(S)\).
Every member of \(S\) is a founder or descends, along a path inside
\(S\), from a founder. To see this, follow internal parents backwards;
finite ancestry makes the process stop.

Define the **founding-cohort condition** by
\[
 \mathrm{FC}(S):\qquad
 t(r)<t(x)\quad
 \text{for every }r\in R(S),\ x\in S\setminus R(S).
\]
If a connected \(S\) has more than one vertex, it has a non-founder.
Under FC, all its founders precede this one fixed organism, so there
are only finitely many founders. A connected set with no non-founder
is a singleton, and also has finitely many founders.

The families we compare are
\[
 \mathcal C=\mathrm{IAP}\cap\mathrm{CONV}\cap\mathrm{CA}\cap\mathrm{REF},
\]
\[
 \mathcal F=\mathrm{CONN}\cap\mathrm{IAP}\cap
             \mathrm{CONV}\cap\mathrm{REF}\cap\mathrm{FC},
\]
and, for a fixed integer \(N\geq1\),
\[
 \mathcal F_N=\{S\in\mathrm{CONN}\cap\mathrm{IAP}\cap
                   \mathrm{CONV}\cap\mathrm{REF}:|R(S)|\leq N\}.
\]
Only nonempty sets are included. A maximal member means maximal by
inclusion in the specified family.

Convexity and CA imply connectedness and FC. If \(r\) is the common
ancestor, paths from \(r\) to other members remain inside \(S\);
\(r\) is the unique founder. Conversely, if a set has exactly one
founder, the internal-parent argument makes that founder ancestral
to all its other members. Consequently
\[
                    \mathcal C=\mathcal F_1,
 \qquad \mathcal C\subseteq\mathcal F,\qquad
                    \mathcal C\subseteq\mathcal F_N.
\]
The connectedness and FC requirements in the first equality are
automatic on the CA side. The families \(\mathcal F\) and
\(\mathcal F_N\), \(N\geq2\), need not be nested.

# 3. Why finite founders suffice in the union argument

Alexander calls a family upward generic when it is closed under
unions of nonempty ascending chains [A, Definition 7]. Such closure
provides the upper bounds needed for Zorn's lemma. Here the difficult
condition is IAP: a union can accumulate infinitely many descendants
and non-descendants even when no single member does.

The following lemma isolates the part of Alexander's proof of
Theorem 9(4) that is needed. His common ancestor supplies one
starting vertex. Finitely many founders supply one by a pigeonhole
argument.

## Lemma 1. IAP at a chain union with finitely many founders

Let \(C\) be the union of a nonempty chain of connected sets satisfying
IAP, CONV and REF. If \(C\) has finitely many founders, then \(C\)
satisfies IAP.

**Proof.** Connectedness and convexity pass to \(C\), since each path
or pair of endpoints involved is contained in one sufficiently large
chain member. Reflection passes as well: a chain member containing
a given vertex already supplies its infinitely many descendants.

Suppose IAP fails at \(v\in C\). Infinitely many members of \(C\) are
descendants of \(v\), and infinitely many are not. Every member of \(C\)
descends internally from one of its finitely many founders, or is a
founder itself. Therefore some founder \(w_1\) has infinitely many
descendants in \(C\) that do not descend from \(v\).

Because \(w_1\) has finitely many children, one child \(w_2\) has
infinitely many of these descendants. Convexity puts \(w_2\) in \(C\).
It is not a descendant of \(v\), since otherwise all its descendants
would be descendants of \(v\). Repeating gives an infinite path
\[
                 w_1\longrightarrow w_2\longrightarrow w_3
                     \longrightarrow\cdots
\]
inside \(C\), entirely outside the descendants of \(v\).

Choose a chain member \(C_\alpha\) containing \(v,w_1\).
The infinite path shows that \(w_1\) has infinitely many descendants
in \(G\); REF makes \(C_\alpha\) infinite. Fix \(n>1\), and choose
a chain member \(C_\beta\supseteq C_\alpha\) containing \(w_n\).
Reflection and the rest of the path give infinitely many descendants
of \(w_n\) in \(C_\beta\). IAP there makes its non-descendants finite.
Thus the infinite subset \(C_\alpha\) contains a descendant of \(w_n\).
It also contains the ancestor \(w_1\), so convexity puts \(w_n\)
in \(C_\alpha\).

This holds for every \(n\). Consequently \(C_\alpha\) contains
infinitely many non-descendants of \(v\). Reflection also gives it
infinitely many descendants of \(v\), since \(v\) has infinitely many
in \(C\subseteq G\). This contradicts IAP for \(C_\alpha\).
\(\square\)

The lemma assumes finiteness of the founder set of the **union**.
Finiteness separately at each stage is insufficient: the number can
increase without bound along the chain. Each of our two constraints
supplies the missing union condition in its own way.

# 4. Two coverage theorems

## Theorem 2. Founding cohorts

The family \(\mathcal F\) is upward generic. Every organism belongs
to a maximal member of \(\mathcal F\).

**Proof.** Let \(C\) be a nonempty chain union from \(\mathcal F\).
Connectedness, convexity and reflection pass to \(C\) as in Lemma 1.
To verify FC, take a founder \(r\) of \(C\) and a non-founder \(x\)
with an internal parent \(p\). Some chain member contains \(r,x,p\).
In that member \(r\) is still a founder and \(x\) is a non-founder,
so \(t(r)<t(x)\). Thus \(C\) satisfies FC and has finitely many
founders by Section 2. Lemma 1 supplies IAP.

For coverage, Alexander's Theorem 13 supplies a member of
\(\mathcal C\) containing any specified organism. It belongs to
\(\mathcal F\). The subfamily of \(\mathcal F\) containing that
member has upper bounds for all nonempty chains; Zorn's lemma gives
a maximal member. Any larger member of \(\mathcal F\) would still
contain the specified seed, so this is maximal in the whole family.
\(\square\)

## Theorem 3. Fixed finite founder bounds

For every fixed \(N\geq1\), the family \(\mathcal F_N\) is upward
generic, and every organism belongs to a maximal member. At \(N=1\)
this is Alexander's common-ancestor family.

**Proof.** Let \(C\) be a nonempty chain union from \(\mathcal F_N\).
If \(C\) had \(N+1\) founders, one chain member would contain them
all. They would still be founders there, contradicting the bound.
Hence \(|R(C)|\leq N\). Connectedness, convexity and reflection pass
to the union, and Lemma 1 gives IAP.

The same seed from Alexander's Theorem 13 lies in
\(\mathcal C\subseteq\mathcal F_N\). Zorn's lemma gives coverage.
The equality \(\mathcal F_1=\mathcal C\) was proved in Section 2.
\(\square\)

These theorems answer the request after [A, Theorem 13] for an
alternative without CA. They use his coverage theorem to obtain
initial clusters and adapt his chain method to extend them. They
do not claim a replacement proof of that published initial-existence
theorem.

## Examples and the role of the bound

The late-founder genealogy in Section 1 satisfies IAP: every vertex
has all but finitely many vertices as descendants. The whole
biosphere is connected, convex and reflective, has two founders,
and is maximal because it is all of \(G\). It is a member of every
\(\mathcal F_N\), \(N\geq2\), but not of \(\mathcal F\).

A founding-cohort example can be completely explicit too. Take two
parentless organisms \(a,b\), both parents of \(c_0\), followed by
\(c_0\to c_1\to\cdots\). Give \(a,b\) the first two birthdates.
The whole graph satisfies FC, IAP, CONV and REF, and has no common
ancestor. It is therefore a maximal member of \(\mathcal F\).
Its two CA-maximal subsets are \(G\setminus\{a\}\) and
\(G\setminus\{b\}\). Starting at a later \(c_i\) gives smaller
qualifying sets, each contained in both of those larger ones.

The distinction between a fixed bound and an unspecified finite
number is witnessed by a different genealogy. Let
\[
 v_0\to v_1\to v_2\to\cdots,\qquad w_i\to v_{i+1}\quad(i\geq0),
\]
with birthdates \(t(v_i)=2i\), \(t(w_i)=2i+1\). For \(m\geq0\), put
\[
 S_m=\{v_i:i\geq0\}\cup\{w_i:0\leq i<m\}.
\]
Each \(S_m\) is connected, convex and reflective. It has \(m+1\)
founders and satisfies IAP: a backbone vertex misses only finitely
many earlier vertices and immigrants; every included immigrant also
misses only finitely many vertices. But the union contains infinitely
many descendants and non-descendants of \(v_0\), namely the later
backbone vertices and all the \(w_i\). Its IAP fails.

In this entire graph, any reflective IAP set containing \(v_0\) contains only
finitely many immigrants: reflection forces infinitely many backbone
descendants, and IAP then excludes infinitely many immigrants. It is therefore contained in some \(S_m\)
and can be enlarged to a larger \(S_{m+1}\). Thus the family of
connected, convex, reflective IAP sets with finitely many founders,
without one common bound, has no maximal member containing \(v_0\).
A fixed bound prevents this particular accumulation; FC prevents it
by its temporal condition. The example places no prohibition on an
individual late founder.

# 5. The infinite species classes are preserved

Different founding conventions can change the admitted finite
histories. We now ask whether they change the infinite species
classes in Alexander's sense.

For an infinite set \(S\), define
\[
 \operatorname{gen}(S)=
 \{v\in S:S\setminus\operatorname{Desc}(v)\text{ is finite}\}.
\]
These are its generators. Alexander defines \(S\sim T\) when
\[
          \operatorname{gen}(S)\mathbin{\triangle}
                   \operatorname{gen}(T)\quad\text{is finite}.
\]
The definition concerns **infinite** sets. It does not identify
finite maximal clusters.

We use Alexander's Objective Species Theorem
[A, Theorem 6]: two infinite specieslike clusters with infinitely
many common generators are equivalent under \(\sim\).

## Theorem 4. Agreement of represented infinite classes

The infinite maximal members of \(\mathcal F\), of each
\(\mathcal F_N\), and of \(\mathcal C\) represent exactly the same
\(\sim\)-classes.

**Proof.** Let \(S\) be an infinite member of either alternative.
It has finitely many founders. Some founder \(r\) has infinitely
many descendants in \(S\), and IAP at \(r\) makes
\[
             S_r=\{r\}\cup(S\cap\operatorname{Desc}(r))
\]
cofinite in \(S\).

The set \(S_r\) has common ancestor \(r\). IAP is inherited by
subsets. Convexity follows from convexity of \(S\) and transitivity
of ancestry. If \(x\in S_r\) has infinitely many descendants in
\(G\), REF for \(S\) puts infinitely many in \(S\), all descended
from \(r\), so REF holds in \(S_r\). Thus \(S_r\in\mathcal C\).

By [A, Theorem 9(4)] and Zorn's lemma, extend \(S_r\) to a maximal
\(M\in\mathcal C\). Finite branching and convexity give an infinite
directed path in \(S_r\). Every vertex on that path has infinitely
many descendants in both \(S\) and \(M\); IAP makes it a generator
of both. Their common generator set is infinite. The Objective
Species Theorem gives \(S\sim M\).

Conversely, let \(M\) be an infinite maximal member of
\(\mathcal C\). It belongs to both alternatives, and Theorems 2
and 3 extend it to a maximal member \(S\) of either one. An infinite
path in \(M\) again consists of common generators of \(M,S\).
The same published theorem gives \(M\sim S\).
\(\square\)

The first direction works even when \(S\) is not maximal. Maximality
specifies the collections of representatives being compared, rather
than supplying that direction's argument. The theorem concerns
finite symmetric difference of **generator sets**. It neither
asserts finite symmetric difference of the clusters themselves nor
makes maximal representatives unique.

# 6. What finite observations can tell us

The coverage theorems are existence statements about a whole infinite
biosphere. Their use of an infinite future is substantial. A
genealogical record can be extended tomorrow along a side lineage
that has not yet permanently died out; no finite record settles
whether that extension will happen infinitely often.

To make this observation precise, number vertices by birth order,
\(0,1,2,\ldots\), and set \(t(n)=n\). Coordinate \(n\) specifies
the subset of \(\{0,\ldots,n-1\}\) that parents \(n\). Each
coordinate has finitely many possibilities. Give the product the
topology in which an initial finite record is an observation.

Let \(\mathcal B\) be the subspace with one root, vertex \(0\),
exactly one parent for every other vertex, and at most two children
per vertex. Violations have finite witnesses, so \(\mathcal B\)
is closed. Every member is a connected infinite biosphere.

A set is \(F_\sigma\) if it is a countable union of closed sets.
A \(\boldsymbol{\Pi}^0_3\) set is a countable intersection of
\(F_\sigma\) sets. Completeness here means that every such subset
of Cantor space continuously reduces to the property in question.
A continuous reduction transforms records so that each finite
output record depends on only finitely much input. The boldface
notation denotes **Borel complexity**, not an arithmetical index
set or a uniform algorithm for arbitrary presentations.

# 7. The complexity of global IAP

## Theorem 5. Third-level Borel completeness

Global IAP is \(\boldsymbol{\Pi}^0_3\)-complete on \(\mathcal B\).
On the larger space of birth-coded biospheres it has the same
relative upper bound and is at least this hard.

**Proof: upper bound.** Let \(D(v,n)\) mean that \(v\) is a strict
ancestor of \(n\). This is determined by the first \(n+1\)
coordinates. IAP is exactly
\[
 \forall v\ \exists(N,b)\in\mathbb N\times\{0,1\}\
                   \forall n\geq N\ [D(v,n)=b].
\]
For fixed \(v,N,b\), the universal condition is closed. The
existential choice gives an \(F_\sigma\) set, and the outer
intersection gives \(\boldsymbol{\Pi}^0_3\).

**Proof: lower bound.** Consider
\[
 P_3=\{x\in2^{\mathbb N\times\mathbb N}:
                  \text{each row of }x\text{ has finitely many ones}\}.
\]
This is a complete \(\boldsymbol{\Pi}^0_3\) set; a proof is supplied
in Appendix A. We turn its rows into side chains attached
successively to a permanent backbone.

At stage \(s\), create \(b_s\), with parent \(b_{s-1}\) if \(s>0\);
create \(a_s\) with parent \(b_s\); then, for \(k=0,\ldots,s\),
inspect \(x(k,s-k)\). When it is one, append a vertex to the current
tip of the side chain starting at \(a_k\). A zero appends nothing.
Give all created vertices consecutive birth numbers.

The graph \(G_x\) has one root, every other vertex has one older
parent, and each vertex has at most two children. Its permanent
backbone makes it infinite. Each finite output record depends on
finitely many input bits, so \(x\mapsto G_x\) is continuous.

If row \(k\) has infinitely many ones, \(a_k\) has infinitely many
descendants in its side chain and infinitely many non-descendants
on the backbone. Global IAP fails.

If every row has finitely many ones, each side chain is finite.
A vertex on a side chain therefore has finitely many descendants.
For \(b_k\), the non-descendants lie in the finitely many earlier
backbone vertices and the finitely many finite side chains with
index below \(k\), together with \(b_k\) itself. Thus its
non-descendants are finite. Every vertex satisfies IAP, proving
\[
                          G_x\in\mathrm{IAP}
                             \quad\Longleftrightarrow\quad x\in P_3.
\]
This gives the required continuous reduction.
\(\square\)

The construction uses a single founder throughout. Allowing several
founders is therefore not the source of this complexity. On a
locally finite rooted tree the same issue can be viewed through
infinite rays: two rays that separate permanently provide infinitely
many descendants and non-descendants; a unique infinite ray makes
each off-ray subtree finite. This connects the calculation with the
familiar distinction between one infinite end and several.

## Corollary 6. No uniform eventual yes/no learner

There is no finite-record learner that eventually gives the correct
yes/no answer for IAP at a designated organism on every member of
\(\mathcal B\). The learner need not be computable.

**Proof.** Set all rows except row \(0\) to zero in the preceding
construction. IAP at \(a_0\) holds exactly when that row has
finitely many ones. Let FIN be this subset of Cantor space.
It is countable and dense and is not \(G_\delta\): were it a dense
countable intersection of open sets, it would be comeager as well
as meager, contradicting the Baire category theorem.

If a yes/no learner's answers \(g_s\), based on finite records,
converged to the right answer on every input, then
\[
 \mathrm{FIN}=\bigcup_N\bigcap_{s\geq N}\{g_s=1\}
\]
would be \(F_\sigma\). The same formula with zero would make its
complement \(F_\sigma\), so FIN would also be \(G_\delta\).
This is impossible. The same restricted reduction in Theorem 5
also rules out a learner deciding global IAP on these records.
\(\square\)

This conclusion is about a specified binary decision problem.
A species-valued output has different success criteria; no
impossibility theorem for all such outputs follows without defining
those criteria.

# 8. Consequences and scope

The two founder constraints change which founding histories can
occur in a maximal cluster while preserving Alexander's represented
infinite species classes. The founding-cohort condition gives a
temporal convention; the bound \(N\) gives a numerical convention
and permits late founders. Neither theorem establishes which
convention biologists should choose.

Theorem 4 is a consequence of Alexander's Objective Species Theorem
and the finite-founder constructions. Theorem 5 and Corollary 6
concern the observation space explicitly defined here. No claim of
uniform computability from arbitrary infinite graph descriptions,
or of a practical classification algorithm, is made.

All arguments are hand proofs. Alexander's published theorems are
credited where used. The explicit complexity reduction is included
for this formulation; its relation to known one-ended-tree
phenomena is relevant when assessing historical novelty. Independent
human review and priority have not been established.

# Appendix A. Why the row-finiteness set is complete

Let \(A\subseteq2^{\mathbb N}\) be any
\(\boldsymbol{\Pi}^0_3\) set. Write
\[
 A=\bigcap_k\bigcup_N F_{k,N},
 \qquad F_{k,N}\text{ closed},\quad F_{k,N}\subseteq F_{k,N+1}.
\]
For input \(z\) and stage \(s\), let \(m_k(s)\) be the least
\(N\leq s\) such that the cylinder determined by \(z\upharpoonright s\)
meets \(F_{k,N}\), and put \(m_k(s)=s+1\) if there is none.

For fixed \(k\), this integer sequence is nondecreasing. Excluded
candidates stay excluded as the cylinder shrinks, and a newly
available candidate has index larger than every previously
available one. If \(z\in F_{k,N}\), that candidate bounds the
sequence once \(s\geq N\). If \(z\) belongs to none of the
\(F_{k,N}\), closedness eventually excludes every fixed candidate,
so the sequence is unbounded.

Output one in row \(k\) exactly when \(m_k(s)\) increases, starting
with \(m_k(-1)=0\). Each output bit depends on a finite prefix of
\(z\). Its row has finitely many ones exactly when the integer
sequence is bounded. Therefore this is a continuous reduction of
\(A\) to \(P_3\). The direct zero-tail definition of row-finiteness
gives the upper bound. No effective presentation of the closed
sets is assumed in this topological argument.
\(\square\)

# References

**[A]** Samuel Allen Alexander. *Specieslike clusters based on identical
ancestor points*. Journal of Mathematical Biology (2026).
[DOI: 10.1007/s00285-026-02361-x](https://doi.org/10.1007/s00285-026-02361-x).
Source version: [arXiv:2602.05274v1](https://arxiv.org/abs/2602.05274v1),
5 February 2026. Definitions 1--6 and 8--10; Theorems 6, 9 and 13;
the request following Theorem 13.
