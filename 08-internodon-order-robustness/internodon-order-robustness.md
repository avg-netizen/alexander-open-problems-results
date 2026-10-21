---
title: "Birth-order sensitivity of undirforests and internodons"
subtitle: "An exact swap theorem and finite genealogical measurements"
date: "21 October 2026"
abstract: |
  The undirforest construction turns a birth-ordered genealogy into a
  forest on the same organisms. We identify its finite version with
  the augmented merge tree of the graph's superlevel components.
  An adjacent swap of incomparable births leaves the forest unchanged
  precisely when no younger component meets both organisms; otherwise
  it replaces exactly one clade. This gives a clade-distance bound along
  any sequence of valid swaps. The usual interleaving stability theorem
  supplies a separate bound in birth-height units. Neither bound
  controls the internodon membership of fixed organisms. Saved
  simulations illustrate the distinction: within-generation reorderings
  can change most parent pointers, while separating 18--31 percent of
  pairs that originally shared an internodon in a dedicated comparison
  sample. We define the denominators, finite-window conventions and
  sampling protocol explicitly. The results give precise partial
  answers to the robustness question, rather than a general biological
  robustness theorem.
---

# 1. One construction, several meanings of change

Alexander, de Bruin and Kornet [A] construct a forest from a
genealogical directed acyclic graph with distinct birthdates. In
their concluding discussion they ask whether biological undirforests
depend drastically on the topological order chosen for the births.
The question deliberately leaves the meaning of "drastically" open.

A forest on named organisms contains several kinds of information.
It gives each organism a parent in the derived forest. It gives a
hierarchy of clades. With an additional SD classification, it yields
internodons. A change can be small in one of these descriptions
and large in another.

The simplest example has two parents \(u,v\) and their child \(z\):
\[
                         u\longrightarrow z\longleftarrow v.
\]
Both birth orders \(u,v,z\) and \(v,u,z\) are legitimate. Their
undirforests are respectively the chains \(u\to v\to z\) and
\(v\to u\to z\). Every parent pointer changes, but the clade
families differ by just one replacement:
\(\{v,z\}\) becomes \(\{u,z\}\). The full three-organism clade
and the singleton \(\{z\}\) remain.

![The same genealogy under two valid birth orders. Left: both parents precede their child. The two derived chains replace just their inner clade.](figures/adjacent-swap.pdf){width=90%}

We first prove a general version of this local calculation. We
then distinguish its clade bound from an imported stability bound
for height-decorated merge trees. Finally we explain the
internodon measurements using a statistic that counts losses
among originally co-classified pairs. That statistic and the
all-pairs disagreement rate answer different questions.

The structural theorems concern finite birth-ordered graphs.
The experiments are finite-window approximations to the infinite
biological setting of [A]. We keep those two scopes explicit.

# 2. The undirforest as a component sweep

Let \(G=(V,E)\) be a finite genealogy and let
\(r:V\to\{0,\ldots,n-1\}\) be a topological ranking: parents have
smaller ranks than children. Write \(H\) for the underlying
undirected graph.

For distinct \(x,y\), the source defines \(x\) to be an
**undirancestor** of \(y\) when an undirected path from \(x\)
to \(y\) avoids every organism older than \(x\)
[A, Definition 4]. Equivalently,
\[
 y\text{ is in the component of }x
       \text{ in }H[\{v:r(v)\geq r(x)\}].
\]
An **undirparent** is an immediate undirancestor. By the source's
Corollary 6 it is the youngest undirancestor when one exists.
A vertex with no undirancestor is a root of the derived forest.

For a forest \(F\), let \(D_F[x]\) be the set containing \(x\)
and all its descendants in \(F\). Its clade family is
\[
                    \mathcal K(F)=\{D_F[x]:x\in V\}.
\]
Clades here retain organism labels. Every vertex supplies a
distinct clade, so this family has \(n\) members.

## Theorem 1. The component-sweep description

Process vertices from youngest to oldest. On adding \(x\), merge
the current components adjacent to \(x\). Make \(x\) the parent
of the oldest vertex of each merged component. The resulting
forest is exactly the source's undirforest.

**Proof.** Immediately before adding \(x\), the processed graph
is the graph induced by vertices younger than \(x\). Each of
its components is represented in the constructed forest by its
oldest vertex; all its other vertices already lie below that
representative. Adding \(x\) joins precisely the components
touching \(x\).

Let \(y\) be the oldest vertex in one such component. The new
connection makes \(x\) an undirancestor of \(y\). If a younger
undirancestor \(x'\), older than \(y\), existed, its witnessing
path would already lie in the processed graph. Then \(x'\)
would belong to the component containing \(y\), contrary to
\(y\) being its oldest vertex. Thus \(x\) is the youngest
undirancestor of \(y\) and is its undirparent.

Each non-root representative receives its parent on its first
connection to an older vertex. The resulting relation therefore
agrees with the source relation at every vertex. The merged
component has oldest representative \(x\), preserving the
invariant for the next step.
\(\square\)

This is the standard component-merging sweep, retaining a vertex
for every organism rather than suppressing vertices of degree
two. In this augmented sense the undirforest is a merge tree
on each connected component. The identification is useful
because it makes the construction's dependence on the ranking
visible: change the ranking and the same graph is swept in a
different order.

# 3. Exactly what one adjacent swap changes

Let \(u,v\) be consecutive in the ranking, with \(u\) older.
Assume they have no parent-child edge. Consecutiveness then
makes them incomparable in the genealogical order, so their
ranks can be swapped.

Let \(Y\) be the vertices younger than both. Partition the
components of \(H[Y]\) that touch the pair into three groups:
those meeting both \(u,v\), those meeting \(u\) only, and those
meeting \(v\) only. Write \(S,A,B\) for the respective unions
of their vertex sets.

## Theorem 2. Adjacent-swap locality

If \(S\) is empty, the undirforest is unchanged. If \(S\) is
nonempty, the clade family undergoes exactly one replacement:
\[
           \{v\}\cup S\cup B
                 \quad\longmapsto\quad
           \{u\}\cup S\cup A.
\]
The outer clade \(\{u,v\}\cup S\cup A\cup B\) and every other
clade stay unchanged.

More precisely, the oldest vertex of each shared component
changes parent from \(v\) to \(u\). If \(w\) was the original
parent of \(u\), then \(v\) changes parent from \(u\) to \(w\)
and \(u\) changes parent from \(w\) to \(v\). If \(w\) is
absent, the corresponding vertex is a root.

**Proof.** In the original reverse sweep, \(v\) is processed
just before \(u\). If no component meets both, their merges
are disjoint. They are not directly adjacent either. The
component partition and its oldest representatives are the
same after the pair in both orders; all parent assignments
are the same.

If a shared component exists, adding \(v\) first makes it
parent of the representatives of the shared components and
the \(v\)-only components. Adding \(u\) makes it parent of the
\(u\)-only representatives and of \(v\). Its clade is the outer
set, and \(v\)'s clade is \(\{v\}\cup S\cup B\).

In the swapped order, \(u\) is processed first. It becomes
parent of the shared and \(u\)-only representatives. Then
\(v\) becomes parent of \(u\) and the \(v\)-only representatives.
The outer set is unchanged, and the inner clade is
\(\{u\}\cup S\cup A\).

After processing the pair, the same vertex set forms one
component; its oldest representative is \(u\) in the first
order and \(v\) in the second. Its eventual older parent \(w\)
is therefore the same. All younger internal clades are
unchanged, and every later merge attaches the same whole
component. This proves the parent description and excludes
any other clade change. The two inner clades differ because
one contains \(v\) but not \(u\), and the other contains
\(u\) but not \(v\).
\(\square\)

The theorem bounds the **number** of changed clades, not their
sizes. Appending a long descendant chain to the shared child
in the introductory example makes both replaced clades large.
Using many separate shared components makes many individual
parent pointers change. Neither observation contradicts the
single-clade statement.

## Corollary 3. A bound between any two topological orders

Let \(K\) be the number of organism pairs ordered differently
by two topological rankings. Their undirforest clade families
have symmetric difference at most \(2K\). More precisely, along
any valid adjacent-swap route with \(m\) swaps having a shared
younger component, the bound is \(2m\).

**Proof.** Transform one order into the other by successively
moving the next required vertex leftwards. Each crossed pair
is reversed in the two orders and is therefore incomparable
in the genealogical order. This gives a valid route using
exactly \(K\) swaps. Theorem 2 changes zero clades at a swap
without a shared component and removes one and adds one
otherwise. The triangle inequality for symmetric difference
gives both bounds.
\(\square\)

The sharper count depends on the route's intermediate graphs.
It is an exact combinatorial statement, without an assumption
about a probability distribution on birth orders.

# 4. A separate stability statement in height units

For a connected \(H\), extend \(-r\) linearly over its edges.
Its sublevel components encode the superlevel component sweep
above; partial edges attach to an existing endpoint and do not
create additional connections. Retain the standard infinite
root ray in the associated continuous merge tree.

Morozov, Beketayev and Weber [MBW, Theorem 2] prove stability:
for two scalar functions on the same domain, their merge trees
satisfy \(d_I(T_f,T_g)\leq\|f-g\|_\infty\).
Applying it to two rankings on this same graph gives
\[
                       d_I(T_{-r},T_{-r'})
                              \leq\max_{v\in V}|r(v)-r'(v)|.
\]
The edgewise difference is bounded by the maximum at endpoints.
For disconnected graphs apply the statement componentwise.

This compares height-decorated trees, not fixed organism labels.
The interleaving maps may move points along the trees. They
need not preserve an organism's parent or internodon. A valid
adjacent swap therefore has height distance at most one while
still changing many parent pointers. Rank displacement is
measured in birth positions, not elapsed biological time.

# 5. From the forest to internodons

The source's additional construction uses the **sexual
descendant property**, abbreviated SD: an organism is SD if it
has a strict genealogical descendant with at least two parents
[A, Definition 7]. This property uses the original directed
genealogy, not the derived forest.

Restrict the undirforest to SD vertices. Its maximal
non-branching segments are the pre-internodons. A branching
vertex ends its own segment; each of its children begins a new
one. Equivalently, an SD child inherits its parent's segment
exactly when that parent has only one SD child. Each non-SD
organism with an SD ancestor joins the segment of its youngest
SD ancestor, its test organism. These are the source's
Definitions 8--9.

Non-SD organisms without an SD ancestor have no internodon
under that definition. The experiment code assigns each such
organism a distinct singleton label to obtain a partition of
all observed vertices. These singleton labels are a reporting
convention. They never create a positive co-member pair.
The set of uncovered vertices is fixed across rankings of the
same finite genealogy. Removing it therefore leaves co-member
loss and positive-pair Jaccard unchanged, although it changes
the denominator of the all-pairs rate.

A finite window can miss later sexual descendants and later
paths connecting older vertices. The source's infinite-future
internodons consequently need not equal the restriction of a
finite-window computation. Additional simulated generations
help examine this effect, but cannot certify the infinite
future.

# 6. What the measured percentages mean

Fix one finite genealogy and compare a reference ranking with
an alternative. Let \(P_0\) and \(P_1\) be the sets of unordered
pairs sharing an internodon label under the two rankings.
We use three distinct quantities:
\[
 \text{all-pairs disagreement}
       =\frac{|P_0\mathbin{\triangle}P_1|}{\binom n2},
 \qquad
 \text{reference co-member loss}
       =\frac{|P_0\setminus P_1|}{|P_0|},
\]
\[
 \text{positive-pair Jaccard}
       =\frac{|P_0\cap P_1|}{|P_0\cup P_1|}.
\]
The first asks how many of all possible pair decisions change.
The second asks how often a previous positive classification
is lost. The third compares the two positive-pair sets
symmetrically. The first two are disagreement rates; a larger
Jaccard value means greater agreement. None is a percentage
of individual organisms retaining a species identity.

An all-pairs rate can be small when most pairs are separated
under both rankings. For example, among \(100\) organisms,
suppose \(P_0\) has \(100\) pairs, \(30\) are lost, and \(20\)
new pairs appear. Only \(50/4950\), about one percent, of all
pair decisions change, but thirty percent of the original
co-memberships are lost. This is why both denominators matter.

## The within-generation comparison sample

The saved co-membership experiment uses four genealogies and
six alternative rankings per genealogy in each configuration,
with random seed 7. There are 14 generations. One ancestral
deme has \(N\) organisms per generation; from generation 6
there are two permanently isolated demes of size \(N\) each.
Each child has two distinct parents with probability \(p\)
and otherwise one. Parent choices are from the preceding
generation in the same deme, or from the ancestral deme at
the split. Alternative rankings independently permute births
within each generation.

The following are means of the 24 comparisons in each row,
not pooled-pair estimates or confidence intervals. They come
directly from the retained co-membership record.

| \(N\) | \(p\) | All-pairs disagreement | Reference co-member loss | Jaccard |
|---:|---:|---:|---:|---:|
| 6 | 0.3 | 6.70% | 22.41% | 0.6009 |
| 6 | 1.0 | 8.71% | 18.06% | 0.6750 |
| 12 | 1.0 | 6.99% | 22.16% | 0.6405 |
| 24 | 1.0 | 7.36% | 30.83% | 0.5171 |

![Both disagreement rates use the same saved comparisons. The larger rate conditions on a reference co-membership; the smaller rate averages over all organism pairs.](figures/co-membership-metrics.pdf){width=90%}

The largest co-member loss in an individual comparison was
60.67 percent. These measurements show appreciable
reclassification in this finite model. They do not support
a general claim that internodon membership is nearly
unchanged.

## Parent pointers and clades

A separate retained experiment uses six genealogies and twelve
alternative rankings per genealogy. Its random seed is 15.
The generation and split parameters are the same, but the draws
differ from those in the preceding table.

| \(N\) | \(p\) | Parent pointers changed | Normalized clade difference | All-pairs disagreement |
|---:|---:|---:|---:|---:|
| 6 | 0.3 | 51.00% | 32.26% | 7.96% |
| 6 | 1.0 | 77.54% | 58.19% | 6.27% |
| 12 | 0.3 | 56.43% | 44.06% | 6.07% |
| 12 | 1.0 | 82.63% | 70.30% | 6.16% |
| 24 | 0.3 | 58.69% | 48.76% | 4.44% |
| 24 | 1.0 | 84.62% | 73.86% | 6.00% |

The full record also contains \(p=0.7\). Normalized clade
difference is
\[
 \frac{|\mathcal K(F_0)\mathbin{\triangle}\mathcal K(F_1)|}
      {|\mathcal K(F_0)|+|\mathcal K(F_1)|}.
\]
The parent-pointer column compares organism-labelled parents,
including the root marker. The three columns measure different
features. The small all-pairs numbers in this table cannot be
used as substitutes for the co-member-loss numbers in the
other sample.

# 7. Window length and the distribution on orders

## Additional future generations

A buffered experiment evaluates only organisms from the first
10 generations and adds 0, 4, 8 or 12 later generations before
constructing the forest and labels. Its split is at generation
4, its seed is 16, and each configuration has five genealogies
and eight alternative rankings per genealogy.

For \(N=6,p=1\), the mean number of labels on the evaluated
vertices falls from \(11.0\) with no buffer to \(5.0\) with four
extra generations, and is \(5.4\) with twelve. For
\(N=12,p=1\), the corresponding values are \(20.6,7.6,11.0\).
The label counts include the singleton convention of Section 5.

This is evidence that a short observation window affects
classification. It is not a monotone convergence result:
different configurations use different random draws. The
buffered record contains all-pairs disagreement but no
reference co-member-loss statistic. No conclusion about that
conditional loss is inferred from it.

## Orders spanning generations

Another retained sample chooses each next vertex uniformly
from the currently available vertices in Kahn's topological
sorting algorithm. This gives valid topological orders.
It does **not** sample linear extensions uniformly.

For a graph with \(a\to c\) and an isolated \(b\), the possible
orders \(abc,acb,bac\) have probabilities \(1/4,1/4,1/2\).
The first choice is uniform between \(a,b\), but after choosing
\(b\) the rest is forced. Thus even this small graph produces
unequal extension probabilities.

With five genealogies and ten alternative orders per
configuration, seed 21, the saved all-pairs disagreement
ranges from 10.39 to 14.47 percent across the four
configurations. Parent-pointer changes range from 56.62 to
86.73 percent. These are measurements under this particular
sampling rule. They are not estimates under a uniform
distribution on all admissible birth orders or under a
biologically justified distribution of birthdate uncertainty.

# 8. What is settled, and what remains

The component sweep identifies the exact finite construction.
The swap theorem gives a sharp local clade statement, and
Corollary 3 gives a bound for an arbitrary pair of topological
orders. The established merge-tree stability theorem gives
a different bound in height units.

These are precise partial answers to the source question.
They do not yield a population-independent bound on the
internodon co-membership of fixed organisms. The finite
measurements exhibit substantial changes, with the size
depending on the statistic, observation window and order
sampler. They neither establish a general biological
robustness claim nor refute every possible formal version
of that claim.

A stronger result about internodon membership would have to
state its birthdate-error model, identify a metric on labelled
classifications, and control the finite-window approximation
to the future. Extending the construction to historical gene
trees is a separate question from [A] and is not treated here.

# Appendix. Computational records

The calculations and saved records are included with the paper.

- The direct source-definition and sweep implementations are in
  the accompanying undirforest program.
- The adjacent-swap record contains 4,302 valid swaps, of which
  1,637 have a shared younger component. All cases satisfy
  Theorem 2's tested parent-change condition, and all 1,637
  cases replace exactly one clade. The recorded mean replaced
  clade size is 58.03 percent of the observed population.
- The co-membership table and plot use the retained
  co-membership-check record, with 24 comparisons per row.
- The other tables and ranges use the separate main,
  buffered and Kahn-order records described above.

These finite checks support the implementations and the
reported finite data. The universal statements rest on the
proofs and the explicitly cited published stability theorem.
No new biological data, independent human proof review, or
historical priority assessment is claimed.

# References

**[A]** S. A. Alexander, A. de Bruin and D. J. Kornet. *An alternative construction of internodons:
the emergence of a multi-level tree of life*. Bulletin of
Mathematical Biology (2015).
[DOI: 10.1007/s11538-014-0048-2](https://doi.org/10.1007/s11538-014-0048-2).
Definitions 4--9, Corollary 6, and Section 8.

**[MBW]** Dmitriy Morozov, Kenes Beketayev and Gunther H. Weber.
*Interleaving Distance between Merge Trees*. Manuscript
presented at TopoInVis 2013. Theorem 2, pp. 6--7.
[Author manuscript](https://www.mrzv.org/publications/interleaving-distance-merge-trees/manuscript/).
