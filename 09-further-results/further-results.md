---
title: "Further results, problem statements and conjectures on S. A. Alexander's research program"
date: "25 September 2026"
---

This document collects the smaller, partial or conjectural results that accompany the eight
standalone notes in this repository. Each part states its own status. Nothing here has had
independent human review, and none of it has been checked against the literature for priority.

**Contents.**

1. Pseudo-visibility: a formal version of the better-performance conjecture, with an experiment.
2. Species identity is not learnable in the limit (a theorem), and a Π⁰₃-completeness conjecture.
3. Universality of the avoiding populations is not learnable in the limit.
4. Problem statements for two future-work directions: pattern algorithms and variadic Apply.
5. Conjectures.

# 1. Pseudo-visibility: the better-performance conjecture

**Source.** S. A. Alexander, *Pseudo-visibility: a game mechanic involving willful ignorance*,
FLAIRS-35, 2022. [doi:10.32473/flairs.v35i.130652](https://doi.org/10.32473/flairs.v35i.130652).

**Status.** P1a is proved. P1b is a theorem target with the key case computed. P1c is a
conjecture. The experiment script is `pseudovisibility/selfrefl_exp.py`, with results in
`pseudovisibility/selfrefl_exp.json`.

## The setting and the author's conjecture

- **The environment $\mu_{Y,q}$** (Definition 2). Whenever character Y is pseudo-visible, the
  environment queries the agent's own policy for the action it *would* take on the observation
  with Y erased. If the actual action differs, it subtracts a penalty q.
- **The wrapper SelfRefl(A)** (Definition 10). It annotates each observation with that
  counterfactual action, computed by running itself on the erased observation annotated with −1.
- **The conjecture.** The paper conjectures that SelfRefl(A) outperforms A, but writes: "We do not
  currently know of any way to articulate this better-performance conjecture formally". The
  difficulty it names is that "A might already engage in said self-reflection".

## Two regimes

SelfRefl with underlying policy g acts on o as h(o) = g(o, c(o)), where c(o) = g(erase(o), −1) is
its own action on the erased observation.

- **Deterministic policies** (the paper's standing assumption). Every plain policy is such an h:
  take g ignoring its annotation. So SelfRefl has no advantage in *capacity*, and any
  better-performance statement must be about **learning**.
- **Stochastic policies with an isolated random-number generator.** The paper advises, after
  Lemma 4, that the policy's generator advance only during training, so that two calls within one
  step agree.
  - The annotation then carries the *realised* counterfactual draw, which SelfRefl can match
    exactly.
  - A plain agent's action at a pseudo-visible observation is an independent draw. If the policy
    gives every action probability ≥ δ at erased observations, it mismatches with probability
    ≥ $1-\max_b P(a'=b)$ ≥ (m − 1)δ, where m is the number of actions.

  **P1a (proved).** In this regime SelfRefl has a strict capacity advantage. It gains at least
  q·(m − 1)δ in expectation per pseudo-visible step during training.

## Experiment

The environments are one-step episodes with exact optima computed by enumeration, and the
Definition 10 annotation logic is used verbatim. Each figure is a mean over 30 seeds.
- **Coupled:** a single context, rewards R₀ = (1.0, 0.9) when Y is absent and R₁ = (0, 1) when Y
  is pseudo-visible, with q = 2 and p = ½.
- **Drift:** 40 contexts, 4 actions, random base rewards, a "react" bonus under pseudo-visibility,
  and reward noise σ = 0.5.

| scenario | learner | plain | SelfRefl | optimum | best-response fixed point |
|---|---|---|---|---|---|
| coupled, greedy query | tabular | final **0.500** | final **0.500** | 0.95 | 0.50 |
| coupled, stochastic query (ε = 0.1) | tabular | training 0.422 | training **0.494** | | |
| drift, T = 2,000 | tabular | final 0.631 | final 0.652 | 0.857 | 0.844 |
| drift, T = 20,000 | tabular | final 0.801 | final 0.816 | 0.857 | 0.844 |
| drift, T = 2,000 | linear, shared features | final 0.664 | final **0.749** | 0.857 | 0.844 |
| drift, T = 20,000 | linear, shared features | final 0.831 | final 0.838 | 0.857 | 0.844 |

**What it shows.**

1. **SelfRefl does not reach the stationary optimum.**
   - In the coupled case the optimum needs the action at the *erased* observation to give up
     reward (1.0 → 0.9), so that the pseudo-visible observation can take its preferred action
     without penalty.
   - Neither learner can see that trade. The erased observation's estimates are trained only on
     erased-observation rewards, while the penalty lands elsewhere.
   - Both converge to the best-response fixed point: 0.50, against 0.95.
   - $\mu_{Y,q}$ is a *Newcomblike* environment, since its reward depends on the policy. The paper
     cites Bell et al. (2021) on value-based learners in such environments. The fixed point here is
     of the self-consistent kind studied there; that literature was not re-read for this note.
2. **With a stochastic query, the gain is strict and immediate** (0.494 against 0.422), as P1a
   predicts.
3. **With deterministic tabular learning, the gain is transient.** It is a small, consistent
   speed-up of about 0.015–0.02 in final value, with the same limit.
4. **With shared linear features, the transient gain is large** (0.749 against 0.664 at T =
   2,000). The annotation supplies one feature, "a = my erased action", that transfers across
   contexts. The plain feature class has no way to express it.

## Formal targets

- **P1b (theorem target).** For deterministic tabular Q-learning with greedy queries and standard
  step sizes:
  - A and SelfRefl(A) have the same set of limit policies, namely the best-response fixed points;
  - on some $\mu_{Y,q}$ these lie strictly below the stationary optimum.

  If this holds, the better-performance conjecture is true only for **rates of learning**, not for
  limits.
- **P1c (conjecture).** Take a linear learner whose features are shared across K contexts. On
  pseudo-visibility environments whose penalty structure is common to all contexts:
  - SelfRefl(A) learns the penalty with O(1) samples;
  - A needs Ω(K) samples.

**The author's obstacle, in these terms.**
- For deterministic tabular A, "already self-reflecting" is harmless, because the limits coincide.
- For stochastic A, no plain agent can self-reflect, because the realised draw is private to the
  query.
- For function-approximating A, the question is whether A's feature class already contains the
  "match my erased action" feature. P1c isolates exactly that.

# 2. Species identity is objective but not learnable in the limit

**Source.** S. A. Alexander, *Specieslike clusters based on identical ancestor points*, J.
Mathematical Biology, 2026. [arXiv:2602.05274](https://arxiv.org/abs/2602.05274).

**Status.** The theorem is proved. Conjecture 2b is open.

**Theorem.** Consider an observer who sees an infinite biosphere (the paper's Definition 1) as the
growing sequence of finite genealogies G↾t, ordered by birth. No guesser, not even a
non-computable one, converges on every biosphere to the right answer to either:
- (a) "does organism v satisfy the IAP condition in G?", that is, *not* (v has infinitely many
  descendants *and* infinitely many non-descendants);
- (b) "is G ∈ IAP?"

*Proof.*
- **The construction.** Encode a binary sequence b as a biosphere $G_b$:
  - two parentless organisms v (born at time 0) and u (born at ½);
  - at each time t ≥ 1, one organism $x_t$ is born;
  - its single parent is the youngest member of v's lineage if $b_t$ = 1, and of u's lineage if
    $b_t$ = 0.
- **$G_b$ is a legitimate biosphere.** Parents precede children, each organism has at most one
  child, and finitely many organisms are born before any time. The prefixes $G_b$↾t and b↾t
  determine each other.
- **What IAP says in $G_b$.**
  - The descendants of v are exactly its lineage (the 1-lineage). Its non-descendants are u and
    the 0-lineage.
  - So v violates IAP iff b has infinitely many 1s and infinitely many 0s.
  - Every other organism stands in the same relation to its own lineage and the other one. So
    $G_b$ ∈ IAP iff b is **eventually constant**.
- **Eventually constant sequences are not guessable.** They form a countable, dense, hence meagre,
  subset of Cantor space. A dense $G_δ$ set is comeagre, so this set is not $G_δ$, hence not Δ⁰₂.
  Guessable sets are exactly the Δ⁰₂ sets: this is Wadge's characterisation, recalled as Theorem
  1.2 of Alexander, *Guessing, mind-changing, and the second ambiguous class* (Notre Dame J. Formal
  Logic 57(2), 2016; [arXiv:1401.1894](https://arxiv.org/abs/1401.1894)).
- A guesser for (a) or (b) would therefore guess eventual constancy, which is impossible. ∎

**Reading.** In $G_b$, IAP fails exactly when the population has **permanently split** into two
infinite lineages. So no one watching births can converge on whether a split is permanent. That
fits the paper's objective-species theorem: the ∼-classes of maximal clusters are objective facts
about G, and yet no observer converges on them. It also explains why the internodon measurements
in `08-internodon-order-robustness` had to stipulate a permanent split within a finite window.

**Conjecture 2b.** Code biospheres as sequences of finite genealogies. Then "G ∈ IAP" is
**Π⁰₃-complete**.
- *The upper bound* is immediate: ∀v ¬(Π⁰₂ ∧ Π⁰₂), since descendant status is decided at birth.
- *For hardness,* take P3 = {x ∈ 2^{ω×ω} : every row has finitely many 1s}, which is
  Π⁰₃-complete. Let row k drive its own pair of lineages as b drives $G_b$.
- *What remains* is to stop different rows from creating IAP failures across rows. Disjoint
  lineages each add infinitely many non-descendants to every organism, so the pairs must be joined
  with care.

# 3. Universality of the avoiding populations is not learnable in the limit

**Status.** A short consequence of established descriptive set theory, not a new general theorem.
It builds on a companion result.

**Background.** The companion packet
[biological-unavoidability-results](https://github.com/avg-netizen/biological-unavoidability-results)
(§6 of its `results.md`) constructs, for each binary sequence s, a population $P_s$ with

$$P_s\text{ realises every infinite binary sequence}\iff s\text{ is eventually periodic}.$$

It also shows that no finite inspection certifies universality. The source question is from
S. A. Alexander, *Biologically unavoidable sequences*, Electronic J. Combinatorics 20(1), 2013.

**Proposition.** No function G : {0,1}^{<ω} → {0,1}, computable or not, has guesses G(s↾n)
that stabilise, for **every** s, to the correct answer about $P_s$'s universality.

*Proof.*
- The eventually periodic sequences form a countable dense set, hence a meagre $F_σ$ set.
- If the set were also $G_δ$, density would make it comeagre, and Cantor space would be a union of
  two meagre sets. So it is not $G_δ$, hence not Δ⁰₂, hence not guessable by Wadge's
  characterisation.
- *A direct argument.* Given a correct guesser, extend a prefix along an eventually periodic
  sequence until the guess is 1, then along a non-eventually-periodic sequence until it is 0, and
  repeat. The limit sequence makes the guesses oscillate forever. ∎

**Reading.** The companion result rules out finite *certification*. This strengthens it:
- even a procedure allowed arbitrarily many revisions cannot be eventually correct on every
  stream;
- by contrast, "a 1 occurs somewhere" is guessable (answer no, and switch permanently at the
  first 1) without ever being certifiable;
- promises change the picture. If every admissible stream is promised to have period p after
  position K, the first K + p symbols settle everything.

# 4. Problem statements for two future-work directions

Several of the author's papers end with future-work directions rather than posed problems. Two of
them are stated precisely here. The literature published since those papers has **not** been
checked for either.

**Pattern algorithms.** From S. A. Alexander, *Arithmetical algorithms for elementary patterns*,
Archive for Mathematical Logic, 2015
([doi:10.1007/s00153-014-0404-9](https://doi.org/10.1007/s00153-014-0404-9)), §6. The author
writes that he would "like to publish algorithms for the epsilon function α ↦ $\varepsilon_α$, the Gamma
function α ↦ $\Gamma_α$, the Veblen function (α, β) ↦ $\varphi_α$ β … [and] in terms of second-order patterns".
- *Target P2a.* An algorithm, working directly on Carlson's elementary patterns in the paper's
  geometric style, taking a pattern that notates α to one that notates $\varepsilon_α$. It should come with a
  proof of correctness against Wilken's isomorphism with the Cantor normal form.
- *Target P2b.* The same for $\varphi_α$ β, within the core.
- *Why it is well posed.* Carlson–Wilken normal forms make patterns computable objects, so each
  target has a checkable specification. Small patterns can be enumerated and both sides compared
  through the Cantor/Veblen normal form.

**Variadic Apply.** From S. A. Alexander, *The first-order syntax of variadic functions*, Notre
Dame J. Formal Logic 54(1), 2013 ([arXiv:1105.4135](https://arxiv.org/abs/1105.4135)), §7. The
first-order treatment cannot express Apply(G, n₁, …, $n_k$) = G(n₁, …, $n_k$) for variadic G.
- *Target P3.* A many-sorted variadic logic, with sorts for naturals and for finite sequences, in
  which Apply is definable.
- It should come with a completeness theorem relative to a conservative extension of the paper's
  semantics.

# 5. Conjectures

## 5.1 Founding-cohort and common-ancestor species agree up to ∼

This is Conjecture S1 of `06-founding-cohort-species`: every $T_{\mathrm{FC}}$-maximal set is ∼-equivalent to
a CA-maximal set, and conversely. The evidence there reduces it to a single comparison. For a
founder r with infinitely many descendants in S, the set $S_r$ = {r} ∪ (desc(r) ∩ S) must be
compared with the CA-maximal sets that contain it. If the conjecture holds, the objective-species
theorem does not depend on which convention is used.

## 5.2 Internodon co-membership is decided by merge-tree persistence

**Setting.**
- The undirforest is the merge tree of the genealogy, with birth rank as height
  (`08-internodon-order-robustness`, §1).
- Two topological orders with maximal rank displacement δ give merge trees within interleaving
  distance δ.

**Conjecture.** If the branch separating x and y in the undirforest has persistence greater than
2δ, their internodon co-membership is the same under every order within displacement δ.
- The analogue for persistence diagrams (bottleneck stability) is established. The content here
  is that the internodon rules (SD organisms, non-SD attachment) respect it.
- Non-SD attachment is the likely point of failure.

**Evidence.** Changed pairs increase with δ: 4–10% for reorderings within generations, against
10–14% for arbitrary orders.

**Test.** Record each pair's separating-branch persistence in `order_robustness_any.py`, and check
that every changed pair lies at or below 2δ.

## 5.3 No symmetric universal machine makes the sign of intelligence computable

**Source.** S. A. Alexander and M. Hutter, *Reward-punishment symmetric universal intelligence*,
AGI 2021 ([doi:10.1007/978-3-030-93758-4_1](https://doi.org/10.1007/978-3-030-93758-4_1), [arXiv:2110.02450](https://arxiv.org/abs/2110.02450)), §5. The paper leaves open whether
any ⊓-symmetric prefix-free universal machine U makes sgn $\Upsilon_U$ computable, in a strong sense (always
correct) or a weak sense (correct whenever Υ ≠ 0).

**Conjecture (strong form).** For **every** ⊓-symmetric U, the strong sign is not computable.

**Proof route.**
- The paper's Corollary 16 says reward-ignoring agents have Υ = 0 for every symmetric U.
- Let $A_{p,C}$ run a fixed reward-ignoring agent B until program p halts, at some turn n, and then
  follow a computable reward-sensitive rule C.
  - If p never halts, Υ($A_{p,C}$) = 0.
  - If p halts, the value is determined by behaviour after turn n.
- The strong sign would decide halting **given a uniform non-vanishing lemma**: a fixed finite set
  of rules C₁, …, $C_k$ such that, for every n and every symmetric U, not all Υ($A_{p,C_j}$) vanish.

Duals do not help here. By the paper's Theorem 5, the dual of a rule negates Υ, so it adds nothing
new; a genuinely different second rule is needed. The weak form is also expected to fail, with
less confidence. The paper's footnote-8 machine relies on one dominating environment, and for an
arbitrary U the analogous agent must make a hidden test environment dominate.

## 5.4 Question 26 fails for every r under symmetric normalisation

`01-quitters-and-question-26` settles Question 26 under Legg and Hutter's normalisation. The
natural setting after the 2021 symmetric paper has rewards and totals in [−1, 1], with a symmetric
U. There:
- partial sums can exceed the total, so quitters with thresholds up to 2 can trigger;
- quitting can *help*, by dodging later punishment.

**Conjecture.** For every r there are A and B with Γ′(A) > Γ′(B) and Γ′($B_r$) = Γ′(B), yet
Γ′($A_{r+1}$) ≤ Γ′(B).

**Route.**
- Use a dual pair (µ, µ̄) of equal weight, in which B's gains and losses cancel, so that $B_r$ = B
  on average without being equal environment by environment.
- A reaches a partial sum ≥ r + 1 early and then collects a refund, which the quitter $A_{r+1}$
  forgoes.

## 5.5 Minimality of introspection bundles beyond Lemma 19

From `07-minimal-introspection-bundle`.
- **The stratified analogue** (Lemma 64 / Corollary 71 of *Self-referential theories*) should
  have the same answer: drop the validity schema, keep assigned validity and deduction. The proof
  of Theorem 1 there uses only compactness, membership of the valid sentence in AV, and closure.
  All three have stratified counterparts. The likely snag is that stratified closure runs only
  upward in the ordinal index.
- **No other block of Corollary 23** can replace AV or i-Deduction for introspection.

## 5.6 The pseudo-visibility coupling gap is invisible to value learning

Consider any learner that updates the parameters used at erased observations only from rewards
received at erased observations.

**Conjecture.**
- The limit policies of A and of SelfRefl(A) are the same set.
- The gap between the optimum and the fixed point can approach q·p.

Closing the gap requires **cross-observation credit**: charging the penalty incurred at a
pseudo-visible observation back to the erased observation's parameters. That is a third wrapper,
neither A nor SelfRefl(A).

## 5.7 "Classical beats pop" is a claim about representation level

**Source.** S. A. Alexander, *Legg–Hutter universal intelligence implies classical music is better
than pop music for intellectual training*, The Reasoner, 2019. The argument, offered
playfully:
- a classical piece is determined by its score ("a few hundred kilobytes"), while a pop song needs
  its recording ("megabytes");
- so the environment "listen to X and derive pleasure" has lower Kolmogorov complexity for
  classical music, and gets more Legg–Hutter weight.

**Conjecture.** The asymmetry comes from comparing **a score with a recording**, not from a
property of the genres. At a matched level of representation, the two genres overlap:
- *symbolic:* score against lead sheet plus arrangement;
- *acoustic:* recording against recording, or performance given score against performance given
  lead sheet.

Any real difference lies in conditional complexity: K(performance | score) for classical
performances, against K(recording | transcription) for pop.

**Test.** For both genres, measure:
- the compressed size of the symbolic layer;
- the residual code length of the audio given its time-aligned symbolic layer, using automatic
  transcription and score-to-audio alignment.

The prediction is that genre separates the measurements less than representation level does.

# References

- J. Bell, L. Linsefors, C. Oesterheld and J. Skalse, *Reinforcement learning in Newcomblike
  environments*, NeurIPS 2021.
- D. Morozov, K. Beketayev and G. Weber, *Interleaving distance between merge trees*, TopoInVis
  2013.
- W. W. Wadge, *Reducibility and determinateness on the Baire space*, PhD thesis, UC Berkeley,
  1983. Cited for guessability as credited in Alexander's papers.
- The Alexander papers are cited inline above.
