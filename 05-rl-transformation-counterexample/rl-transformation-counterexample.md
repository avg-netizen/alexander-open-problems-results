---
title: "A counterexample to the transformation classification as written"
subtitle: "On S. A. Alexander and A. P. Pedersen, *Representation and Invariance in Reinforcement Learning*, arXiv:2112.07752v5 (11 August 2026)"
date: "20 September 2026"
---

**Status.** An explicit counterexample under the printed Definition 2. Independent review of the
argument is the next step. There has been no proof-assistant check and no communication to the
authors.

**Scope.** The claim concerns version 5's Definition 2 and Theorem 3, and hence its Theorem 2
classification. It is not a judgement about the authors' other work, and it does not claim that
the intended result is false under a suitably strengthened definition.

**Source.** [arXiv:2112.07752v5](https://arxiv.org/abs/2112.07752v5): Definition 2 (printed
pp. 3–4), Theorem 3 and its proof (p. 12), and the rational-reward question (pp. 8 and 13).

# 1. The mismatch

Write a framework as $F=(A,E,V)$. Definition 2, printed pp. 3–4, calls a pair of functions

$$
 f:A\to\bar A,\qquad g:\bar E\to E
$$

a transformation when

$$
 \bar V_\mu^{f(\pi)}<\bar V_\mu^{f(\rho)}
 \quad\Longleftrightarrow\quad
 V_{g(\mu)}^\pi<V_{g(\mu)}^\rho
$$

for every $\pi,\rho,\mu$, together with two nontriviality conditions. The conditions require some two image agents to have different values in one destination environment, and some image agent to have different values in two destination environments.

Faithfulness compares **two agents in the same environment**. The proof of Theorem 3, p. 12, instead transfers the ordering of the values of **one agent across different environments**. Definition 2 does not license that inference. Its existential nontriviality conditions do not supply it.

This is more than a missing justification: the following maps meet the definition while contradicting Theorem 3.

# 2. Frameworks and agent map

Use the allowed action set $\{0,1\}$, and percepts $e_0,e_1$ with rewards 0 and 1. Let the source have deterministic agents and deterministic well-behaved environments, and the destination have stochastic agents and stochastic well-behaved environments. Use the paper's infinite-horizon total expected reward and its requirement of convergence for every agent.

For a source agent $\pi$, set

$$
 c(\pi)=\pi(\langle e_0\rangle)\in\{0,1\}.
$$

Let $b_i$ be the destination agent which always takes action $i$, represented as a point-mass stochastic policy. Define $f(\pi)=b_{c(\pi)}$. Thus the map retains just the source agent's first response to one fixed percept.

# 3. Environment map

For any well-behaved destination environment $\mu$, both real numbers

$$
 v_0=\bar V_\mu^{b_0},\qquad v_1=\bar V_\mu^{b_1}
$$

exist. Choose rewards $(r_0,r_1)$ by

| Condition | $(r_0,r_1)$ |
|---|---|
| $v_0<v_1$ | $(0,1)$ |
| $v_0=v_1$ | $(0,0)$ |
| $v_0>v_1$ | $(1,0)$ |

Define the deterministic source environment $g(\mu)$ to output $e_0$ initially, observe the first action $i$, output $e_{r_i}$ next, and output $e_0$ forever afterwards. This defines it on every environment history: at histories of length two it uses the recorded first action; at all other nonempty histories it outputs $e_0$.

It is well-behaved even against stochastic agents: its total reward is always 0 or 1, and the expected partial sums become constant after the second percept. For every deterministic source agent,

$$
 V_{g(\mu)}^\pi=r_{c(\pi)},\qquad
 \bar V_\mu^{f(\pi)}=v_{c(\pi)}.
$$

The table preserves the strict order and equality of the two values. Consequently the required faithfulness equivalence holds for **all** pairs of source agents and **all** destination environments, including stochastic environments.

# 4. Both nontriviality clauses hold

For agent nontriviality, take a destination environment that initially outputs $e_0$, gives reward equal to the first action, then gives zeros. Its values for $b_0,b_1$ are 0 and 1. Source agents with the corresponding first actions exist.

For environment nontriviality, compare the destination environment that always gives zero with the one that gives an initial reward 1 and then zeros. Every image agent has values 0 and 1 respectively. Both environments are well-behaved.

Thus $(f,g)$ is a transformation from the all-deterministic framework to the all-stochastic framework according to Definition 2, contrary to Theorem 3. For the two constant-reward environments in the previous paragraph, our $g$ returns the same all-zero source environment. This also makes the missing cross-environment preservation particularly visible.

The environment map uses comparisons of real expected values and need not be computable. **Definition 2 imposes no computability requirement on these maps.** A computability requirement would create a different problem; this construction does not settle that variant.

# 5. What to do with the rational-reward question

The paper explicitly asks, on pp. 8 and 13, whether its classification remains true for rational rewards. The integer classification first needs repair under the stated definition.

There is also a separate elementary observation: with the paper's **finite** percept set $E$, a map $R:E\to\mathbb Q$ has a common denominator $D$. Its values lie in $D^{-1}\mathbb Z$. For a deterministic agent and environment, a convergent total-reward sequence therefore has a limit in this same discrete lattice. Multiplying all rewards by $D>0$ preserves convergence and all comparisons of expected values.

Accordingly, the discrete-lattice part of an appropriately repaired integer argument would also apply to finite rational reward alphabets. Arbitrarily many rational values with unbounded denominators is a different model: for example $2^{-n}$ rewards permit a convergent deterministic sum that never stabilizes. It requires changing the finite-percept assumption or how rewards are generated. This distinction should be resolved before investing in the proposed extension.

One possible repair is to demand additional preservation of comparisons across environments. Requiring injectivity, computable wrappers, or preservation of actual values are other, different changes. **No replacement classification is proved here**, and the remaining lemmas, including composition and nontriviality, would have to be checked under a revised definition.

# Summary

The faithfulness clause of Definition 2 relates two agents in one environment. Any argument that
compares one agent across environments needs an additional preservation requirement. The maps
above satisfy the definition while collapsing all of that cross-environment information. That is
exactly why they escape Theorem 3.
