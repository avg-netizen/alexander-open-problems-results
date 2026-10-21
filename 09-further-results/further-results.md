---
title: "Research notes and remaining questions"
subtitle: "A guide to the current results and exploratory targets"
date: "21 October 2026"
abstract: |
  This companion distinguishes proved results, conditional applications
  and questions recorded during the Alexander research project.
  The complete pseudo-visibility, species and quitting arguments have
  their own current papers. We give a self-contained finite-observation
  obstruction and explain its conditional application to a companion
  population construction. The remaining cards state the additional
  semantic or quantitative choices required before an exploratory
  suggestion becomes a theorem target. A recorded question is not a
  certification of present-day openness or novelty.
---

# 1. Where the full arguments are now presented

The project's results concern several different notions of learning,
representation and comparison. Keeping them in separate full papers
makes their assumptions easier to assess.

**Pseudo-visibility.** The full paper
[*Information and learning in pseudo-visibility environments*](../12-pseudovisibility-private-information/pseudovisibility-private-information.pdf)
separates deterministic policy representation, private-query value,
shared random seeds and learning dynamics. It gives exact one-step
values and a restricted sample-average tabular convergence theorem.
The included finite-horizon experiments are evidence about specified
learners, rather than a universal wrapper-improvement theorem.

**Species.** The full paper
[*Specieslike clusters with several founders*](../06-founding-cohort-species/founding-cohort-species.pdf)
combines founding cohorts and fixed founder bounds, proves coverage,
compares infinite generator-equivalence classes, and gives the
Borel complexity and binary non-learning results for IAP.
The equivalence statement concerns infinite clusters. A theorem
about deciding IAP does not by itself rule out every notion of
convergence for species-valued outputs.

**Quitting.** The full paper
[*Quitting thresholds and reward normalization in universal intelligence*](../01-quitters-and-question-26/quitters.pdf)
combines the ultrafilter boundary with pathwise and signed
expected-value models. For the latter, its counterexample has
quantifiers \(\forall r\,\exists U\,\exists A,B\). The universal
reference machine is chosen as part of the witness.

These are current arguments with their assumptions stated directly.
This companion does not provide alternative versions of their proofs.

# 2. A finite-observation obstruction

Consider an infinite binary stream \(s\). A learner sees successive
finite prefixes and outputs a binary guess. Eventual correctness
means that its guesses stabilize to the right answer on every input;
the learner need not be computable.

## Proposition. Eventual periodicity has no universally correct learner

No finite-prefix learner is eventually correct on every stream about
whether that stream is eventually periodic.

**Proof.** Let EP be the eventually periodic streams in Cantor
space. It is countable: a finite initial segment and finite period
specify a member. It is dense: every finite prefix can be continued
periodically. Each singleton is nowhere dense, so EP is meager.

If the guesses \(g_n\), based on length-\(n\) prefixes, converged
correctly on every input, then
\[
                     \mathrm{EP}
                        =\bigcup_N\bigcap_{n\geq N}\{g_n=1\}
\]
would be \(F_\sigma\), since each guess set is clopen.
The same expression with zero would make its complement
\(F_\sigma\), hence EP would also be \(G_\delta\).
But a dense \(G_\delta\) subset of Cantor space is comeager.
It cannot also be meager, by the Baire category theorem.
This is a contradiction.
\(\square\)

The argument is topological; it does not use a limitation of
computer running time. Any task continuously encoding this
yes/no property inherits the obstruction.

The public companion
[*Biological unavoidability results*](https://github.com/avg-netizen/biological-unavoidability-results)
gives a population family \(P_s\) for which realizing every
infinite binary sequence is equivalent to eventual periodicity
of \(s\). Under that construction and its finite-prefix
observation interface, the proposition gives non-learning
of its universality property. The construction itself is a
separately cited input, not proved here.

Finite certification, one-sided detection and eventual
two-sided correctness are different requirements.
The property that a 1 occurs is detected at its first occurrence.
An algorithm can start with no and switch to yes then.
A prefix containing a 1 certifies the positive answer; an
all-zero prefix cannot certify the negative one.
Promises can change a learning problem as well: a stream
promised to repeat a specified-length period after a known
cutoff is determined by a sufficiently long prefix.

# 3. Pattern arithmetic: specify the representation first

Alexander's *Arithmetical algorithms for elementary patterns*
(Archive for Mathematical Logic, 2015,
[DOI: 10.1007/s00153-014-0404-9](https://doi.org/10.1007/s00153-014-0404-9)),
Section 6, proposes further algorithms for epsilon, Gamma and
Veblen functions, and for second-order patterns.

A useful algorithmic target must fix the pattern class,
coding of inputs, notational range, operation and correctness
interpretation. For example, an epsilon-function algorithm
would take a pattern denoting \(\alpha\), return one denoting
\(\varepsilon_\alpha\), and establish correctness under the
chosen pattern/ordinal correspondence. A two-argument Veblen
algorithm needs an equally explicit domain and convention
for \(\varphi_\alpha(\beta)\).

These are recorded specifications, not claims that arbitrary
pattern arithmetic is elementary, that small tests prove
correctness, or that the literature has left each task open.
A new selection requires checking the precise existing
algorithm and current source version.

# 4. Variadic Apply: the function argument is part of the problem

Alexander's *The first-order syntax of variadic functions*
(Notre Dame Journal of Formal Logic 54(1), 2013,
[arXiv:1105.4135](https://arxiv.org/abs/1105.4135)),
Section 7, motivates an Apply operation:
\[
                \operatorname{Apply}(G,n_1,\ldots,n_k)
                           =G(n_1,\ldots,n_k).
\]
Giving a sort for finite sequences does not by itself make
the variable function \(G\) available.

An exact target must choose a function sort, a code domain
with an evaluation relation, or an indexed operator family.
It must say whether the functions are all intended functions
or a specified represented collection. Its completeness
claim must distinguish ordinary first-order models from
any intended full function semantics. Conservativity also
needs an explicit original language and class of reducts.

Until those choices are made, the card is a semantic design
question rather than a proved completeness theorem.

# 5. Questions retained with their limits

## Internodon membership and persistence

The [internodon paper](../08-internodon-order-robustness/internodon-order-robustness.pdf)
proves a clade-change bound and states a separate merge-tree
height-stability theorem. Neither directly controls the
co-membership of fixed organisms.

A possible next question is whether an additional persistence
margin, together with an organism-label correspondence and
the SD/test-organism rules, guarantees membership stability.
The separating branch and margin must first be defined for
that labelled construction. Ordinary diagram stability alone
does not supply this implication. The saved all-pairs
percentages do not establish it either.

## Intelligence sign for a fixed symmetric machine

Alexander–Hutter's *Reward-punishment symmetric universal
intelligence* (2021,
[DOI: 10.1007/978-3-030-93758-4_1](https://doi.org/10.1007/978-3-030-93758-4_1)),
Section 5, raises sign computability. Its duality gives zero
to reward-ignoring agents.

A recorded reduction strategy would run a reward-ignoring
agent until a program halts, then switch to one of finitely
many reward-sensitive rules. To decide halting from the
strong sign, one needs a uniform non-vanishing statement:
for every switch time and every reference machine under
consideration, at least one switched rule has nonzero value.
That statement is not supplied here. Adding the reward dual
of a rule only negates its value and does not repair
vanishing. The weak-sign variant has its own promise.
Neither the quitting paper nor finite special-prior
constructions settle this fixed-machine question.

## Introspection outside the unstratified lemma

Entry [07](../07-minimal-introspection-bundle/minimal-introspection-bundle.pdf)
analyzes the unstratified introspection bundle.
The stratified comparison concerns Lemma 65 and Corollary 71
of *Self-referential theories* (2020). A proposed extension
must check where compactness, assigned validity and closure
operate, and whether closure only moves upward in the
ordinal index. Reusing the unstratified proof's wording
does not establish that transfer. This card records the
dependency rather than claiming a new minimality theorem.

## Credit assignment and learning rates

The pseudo-visibility paper proves equal greedy limits only
for its finite tabular model with sample averages, unique
maximizers and explicit sampling/noise assumptions.
Extending that result to all algorithms that update erased
parameters from erased rewards is a broader question.
A bound on the gap, or on constant versus context-linear
sample complexity, needs specified rewards, learner,
features, accuracy and confidence. The existing experiment
does not pay those requirements.

## Representation and music complexity

Alexander's playful *Legg–Hutter universal intelligence
implies classical music is better than pop music for
intellectual training* (The Reasoner, 2019) invites a
representation-level comparison. A score, a recording and
a performance conditional on a score are different coding
objects. A meaningful comparison should hold that level
fixed and state the compressor, transcription and
conditioning information.

This is an exploratory empirical suggestion, not a proved
genre ranking or a conclusion about Kolmogorov complexity
from file sizes. No experiment for it is included.

# 6. How to use the cards

Each card separates a specified result from the missing
semantic, quantitative or source-status input. The purpose
is to make a next question assessable. A saved conjecture
does not establish present-day openness, and a finite
control does not replace an infinite proof.

The full papers linked in Section 1 provide their own
sources, assumptions and reproducibility guides.
The remaining cards record possibilities without claiming
a literature survey, research priority or new resolution.
