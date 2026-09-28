---
title: "Pseudo-visibility: what the information advantage actually proves"
subtitle: "A correction to P1a and a restricted proof of P1b (note 09, section 1)"
date: "27 September 2026"
---

**Provenance.** Produced by OpenAI Codex during an external audit of this repository (27 September 2026), and checked by Anthropic Claude before inclusion. Hand proofs; no independent human review; priority not established.

**Source.** S. A. Alexander, *Pseudo-visibility: a game mechanic involving willful ignorance*, FLAIRS-35, 2022 ([doi:10.32473/flairs.v35i.130652](https://doi.org/10.32473/flairs.v35i.130652)): Definition 2, the discussion after Lemma 4, and Definition 10.

# 1. A frozen random seed does not imply independent draws

The source suggests retaining a policy's random-generator state between action
queries and advancing it during training only. This makes a policy a fixed
function of observation and the retained seed during a step.

Counterexample to this repository's inference: retain a fair bit Z for the whole
step, and let the plain policy output Z at **every** observation. At both the
erased and visible observations its marginal action distribution is (1/2,1/2),
but its two outputs agree with probability 1. There is no mismatch penalty.
This repository's proposed q(m−1)δ penalty floor would give q/2 for m=2, δ=1/2.
Its independence premise is therefore an extra model assumption, not a
consequence of the source's random-generator advice.

This repository's script explicitly implements a different experiment: an isolated
query RNG supplies the query, a separate RNG supplies the actual action, and
the annotated arm reuses the annotation as the environment's query answer.
That is a usable private-query protocol, but it is not evidence for an
unconditional capacity advantage in the frozen-seed source protocol.

# 2. Exact value of a genuinely private counterfactual annotation

Fix one context. Suppose C has a fixed distribution p on a finite action set,
is hidden from the plain policy and revealed to the annotated policy, and
does not change distribution when the visible policy is changed. Let R(a) be
expected base reward and q≥0. Assume R does not additionally depend on C.

**Theorem.** The best plain and annotated one-step values are respectively

$$V_{\rm plain}=\max_a\{R(a)-q(1-p_a)\},
\qquad
V_{\rm ann}=\sum_c p_c\max_a\{R(a)-q\mathbf1[a\ne c]\}.$$

Consequently $V_{ann}$≥$V_{plain}$, but strictness is not automatic.

**Proof.** Any unannotated random action is a convex combination of the
displayed action values, so a pure maximizing action suffices. Once C=c is
observed, maximize separately in that conditional problem. The annotated
policy can always ignore C, proving the inequality. ∎

If R is constant, then copying C is optimal and the gain is exactly
q(1−max $p_a$), at least q(m−1)δ when every $p_a$≥δ. **This is a valid restricted
version of P1a.** It depends on private information and a matched base-reward
condition, not self-reference alone.

For an explicit failure of general strictness, take two actions, uniform C,
q=1/4, and R(0)=1, R(1)=0. Action 0 is optimal even after either annotation,
so both optimal values are 7/8. Always copying C instead has value 1/2.
Avoiding a penalty can cost more in base reward than it saves.

This theorem holds the erased-action distribution fixed. Optimizing the entire
self-referential policy can also change that distribution; that is a separate
optimization problem and must not be smuggled into this conditional comparison.

# 3. A precise restricted version of P1b

Consider the finite contextual **one-step bandit** implemented by note 09's
greedy-query tabular experiment. Contexts have positive sampling probability;
both erased and visible flags occur with positive probability. Returns have
stationary means R(x,y,a) and bounded conditional second moments. Use tabular
sample-average updates, and visit each action infinitely often at each state
that continues to occur. Queries use the current greedy erased action.

Assume, for every context x:

1. R(x,0,·) has a unique maximizer a₀(x).
2. R(x,1,a)−q 1[a≠a₀(x)] has a unique maximizer a₁(x).

**Theorem.** The final greedy policies of the plain and annotated tabular
learners converge almost surely to the same pair (a₀(x),a₁(x)).

**Proof.** Erased-state returns are stationary and never include the visibility
penalty. Infinite visits and the sample-average law of large numbers give
convergence of every erased action estimate to R(x,0,a). Uniqueness and the
finiteness of the context/action sets imply that all greedy erased actions
eventually stabilize simultaneously at a₀(x).

Thereafter, visible-state rewards have stationary means
R(x,1,a)−q 1[a≠a₀(x)]. For the annotated learner only the state
(x,1,a₀(x)) continues to occur; the other annotation states can be disregarded
when evaluating the eventual policy. Infinite action visits at the remaining
states and sample-average updates remove the finite pre-stabilization data.
The visible estimates converge to the same means in both learners. Their
unique maximizers give eventual greedy choice a₁(x). ∎

For this repository's example, p=1/2, q=2, R₀=(1,0.9), R₁=(0,1), this limit is
(0,0) with value 0.50; the joint optimum is (1,1) with value 0.95. Both
uniqueness conditions hold. Thus the finite experiment's observed gap has a
hand proof under the assumptions just stated. It is a gap in the **evaluation
of the limiting greedy policies**; persistent exploration changes training
returns.

The theorem does not cover constant learning rates, tied maxima, shared linear
features, multi-step MDPs, general policy-dependent environments, or a sampled
query. This repository's finite time points alone establish neither asymptotic
convergence nor a learning-rate theorem in those settings. Its O(1) versus
Ω(K) conjecture also needs a specified error tolerance, confidence, context
distribution and feature access before it is a sample-complexity statement.

Finite exact controls for the value formula and counterexamples are recorded
in the audit controls (`../audit-2026-09-27/controls.json`). No new training campaign or
claim of external novelty is involved.
