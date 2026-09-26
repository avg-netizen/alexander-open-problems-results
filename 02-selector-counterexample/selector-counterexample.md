---
title: "Observation-conditioned selection can reverse universal-intelligence rankings"
subtitle: "A counterexample for Questions 23–25 of S. A. Alexander, *Intelligence via Ultrafilters* (2019)"
date: "20 September 2026"
---

**Status.** A hand counterexample, pending independent review. It answers the
machine-independent reading of Questions 23–25 negatively: there is an admissible prefix-free
universal reference machine for which all three proposed implications fail. It does not show
failure for every reference machine, or for one specified externally.

**Source.** S. A. Alexander, *Intelligence via ultrafilters*,
[arXiv:1910.09721](https://arxiv.org/abs/1910.09721): Definitions 12 and 14, the discussion
after Propositions 13 and 15, and Questions 23–25.

Check script: `selector_checks.py` in this folder, which writes `selector_checks.json`.

# The question and the quantifier

The paper's Definition 12 defines $A\oplus B$ to follow $A$ if the first observation is even,
and $B$ otherwise. Question 24 asks whether

$$\min(\Gamma(A),\Gamma(B))>\max(\Gamma(A'),\Gamma(B'))$$

forces $\Gamma(A\oplus B)>\Gamma(A'\oplus B')$.
- A counterexample to this stronger premise also answers Question 23.
- For Question 25, take the first-disagreement selector $\oplus_X$, with $X$ the histories whose
  first observation is even. This is exactly $\oplus$.

Use the standard non-negative, reward-summable Legg–Hutter setup: $0\le V_\mu^\pi\le1$ for every
valid environment and agent, and

$$\Gamma_U(\pi)=\sum_{\mu\in\mathcal E}2^{-K_U(\mu)}V_\mu^\pi.$$

- The class may include stochastic environments. The two specially weighted ones below are
  deterministic.
- Values are expected total rewards where needed.
- No reward-negation symmetry of $U$ is imposed.

# Two environments and four computable agents

Let $A,B,A',B'$ always choose actions $0,1,2,3$ respectively. Define $\mu_e$ and $\mu_o$:
- both give initial reward 0, with initial observation 0 and 1 respectively;
- after the first action, each gives the single nonzero reward listed below, then reward 0
  forever;
- all later observations can be 0, and unlisted actions receive reward 0.

| Environment | $A$ | $B$ | $A'$ | $B'$ | $A\oplus B$ | $A'\oplus B'$ |
|---|---:|---:|---:|---:|---:|---:|
| $\mu_e$ | 0 | 1 | $1/4$ | $1/4$ | 0 | $1/4$ |
| $\mu_o$ | 1 | 0 | $1/4$ | $1/4$ | 0 | $1/4$ |

The selector picks the worse specialist in both environments. Yet both original specialists beat
both replacements when the two rows get equal weight. All four agents are distinct,
deterministic and computable. All rewards are rational, and each total lies in $[0,1]$.

# Incorporating every other computable environment

A finite table alone would not answer a question about a universal prior. Let $U_0$ be any
prefix-free universal description machine for environments. Construct $U$ with exactly these
description branches:

- `00` describes $\mu_e$;
- `01` describes $\mu_o$;
- `1111p` simulates $U_0(p)$;
- there are no other valid descriptions.

This machine is prefix-free and universal, with a simulation overhead of four bits.
- **The special environments.** Each has complexity exactly two: there is no shorter valid
  description, and every simulation description has length at least four. So both have weight
  $1/4$.
- **Every other environment** has a shortest description of the form `1111p`. Choose one for
  each distinct environment. These form a subset of a prefix-free domain, so Kraft's inequality
  gives

$$R:=\sum_{\mu\ne\mu_e,\mu_o}2^{-K_U(\mu)}\le2^{-4}=1/16.$$

The bound uses shortest-description weights, not the total weight of all programs describing the
same environment. It needs no algorithm for recognising valid environments or their shortest
programs.

**The rankings.** The two table rows give

$$\Gamma_U(A),\Gamma_U(B)\ge1/4,\qquad
\Gamma_U(A'),\Gamma_U(B')\le1/8+R\le3/16.$$

So the stronger premise holds with a margin of at least $1/16$. But

$$\Gamma_U(A\oplus B)\le R\le1/16<1/8\le\Gamma_U(A'\oplus B').$$

The proposed conclusion is strictly reversed, again with a margin of at least $1/16$. This proves
the counterexample for Questions 23, 24 and 25 under the declared machine quantifier. Normalising
all weights by a common factor does not change the rankings. Questions 26–28 are not addressed
here; see `01-quitters-and-question-26` for Question 26.

# What comparison does survive selection?

For a deterministic environment, write $E$ for the event that the first observation is even, and
set $\Delta_A=V^A-V^{A'}$ and $\Delta_B=V^B-V^{B'}$. Under any finite non-negative environment
weights,

$$\Gamma(A\oplus B)-\Gamma(A'\oplus B')
=\sum_{\mu\in E}w_\mu\Delta_A(\mu)+\sum_{\mu\notin E}w_\mu\Delta_B(\mu).$$

- The two unconditional advantages do not determine these selected sums.
- Conditional advantages within the selected strata do suffice. Pointwise dominance on each
  selected stratum is a stronger sufficient condition.
- With stochastic initial observations, the same statement uses the joint law of environment and
  initial percept, with the corresponding conditional values.
- An independent coin choosing one policy at the start has a different, linear-mixture formula.
  It does preserve componentwise advantages when the mixing weights are shared.

In short, an agent's overall scalar score discards the conditional performance needed to
evaluate an observation-based router.

# Provenance and scope

The paper already explains the failure of finite weighted averages (after Proposition 13) and
discusses manipulating the reference machine (after Proposition 15). The contribution here is:
- a fully specified universal machine;
- a Kraft bound on the unlisted environments;
- strict margins for exactly Questions 23–25.

Manipulating the prior is an established technique, in particular in Leike and Hutter. This is a
short application, not a new general theorem about universal priors.

The exact-rational checker verifies the table, the selector's choices, the prefix branches and
the worst-case residual bounds. The all-environment claim rests on the Kraft argument, not on
enumeration.

# References

- S. A. Alexander, *Intelligence via ultrafilters*, J. Artificial General Intelligence 10(1),
  2019. [arXiv:1910.09721](https://arxiv.org/abs/1910.09721).
- J. Leike and M. Hutter, *Bad universal priors and notions of optimality*, COLT 2015.
  [PMLR 40](https://proceedings.mlr.press/v40/Leike15.html).
- S. Legg and M. Hutter, *Universal intelligence: a definition of machine intelligence*, Minds and
  Machines 17(4), 2007.
