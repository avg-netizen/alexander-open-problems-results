---
title: "Signed quitting: normalisation boundary and explicit symmetric-prior counterexamples"
subtitle: "Question 26 of *Intelligence via Ultrafilters* under the reward-punishment-symmetric normalisation"
date: "27 September 2026"
---

**Provenance.** Produced by OpenAI Codex during an external audit of this repository (27 September 2026), and checked by Anthropic Claude before inclusion. Hand proofs; no independent human review; priority not established.

**Result.** For every real r there exist a symmetric universal reference machine U and computable agents A and B violating Question 26's implication under the expected-value normalisation. This proves Conjecture 5.4 of note 09 in that quantifier form. It is not a proof for every preassigned U, nor for one U working for all r. Under Legg and Hutter's pathwise normalisation (note 01), the implication holds for r ≥ 0.

Sources: [*Intelligence via ultrafilters*](https://arxiv.org/abs/1910.09721),
Definitions 17–19 and Question 26; [Alexander–Hutter, *Reward-punishment
symmetric universal intelligence*](https://www.hutter1.net/publ/symintel.pdf),
Definitions 1–2 and 10–12. This combines the first paper's designated skip action with the second paper's
**expected-value** normalization. Assume at least two actions and two
observations, and reward alphabet {−1,0,1}.

# 1. Which normalization?

The 2021 paper requires, for every agent π,
$V_\mu^\pi=\lim_n\mathbb E S_n\in[-1,1]$.
It does not require every realized trajectory to total at most 1.

For a deterministic skip-respecting environment with totals bounded by 1 for
every agent, every reachable partial sum is also at most 1: follow its action
prefix and then skip forever. The same argument applies under a genuinely
pathwise total bound in a stochastic environment. Consequently, in that
stronger model:

- If r>0, $A_{r+1}$ never quits on a reachable history.
- If r=0, $A_1$ can quit only at total 1, and doing so cannot lower its eventual
  value, even when later rewards can be negative.

Thus Question 26's implication holds for r≥0 in that model, regardless of the
condition on $B_r$. The proposed universal failure is impossible there.

Under the actual **expected-value** normalization, large partial sums can occur
on rare branches. For example, with probability 1/L an environment offers L
unit rewards, otherwise zero. Every agent's expected value is at most 1, but
the successful branch can total L. This is the resource used below.

# 2. Symmetry facts and the universal tail

Let $W_{skip}$ be the computable well-behaved environments respecting skipping.
It is closed under reward duality μ↦μ̄. Fix a symmetric universal machine U₀
for the paper's suitable RL encoding, and write

$$\Gamma'_U(\pi)=\sum_{\mu\in W_{skip}}2^{-K_U(\mu)}V_\mu^\pi.$$

The series converges absolutely. For a policy Q invariant under negating all
past rewards, dual environments give opposite values, so $\Gamma'_U$(Q)=0 whenever
U is symmetric. In particular Skip has value zero.

For a chosen non-self-dual pair μ₊, μ₋=μ̄₊, give them descriptions `00` and
`01`. Let the only other branch be `1^m p`, simulating U₀(p), with m≥3.
This gives a prefix-free universal machine U. Both special complexities are
exactly 2. Every other environment and its dual have complexities
$m+K_{U_0}(\mu)$, hence U remains symmetric. The total weight of all nonspecial
environments is at most $2^{-m}$, by Kraft's inequality. Since their values are
in [−1,1], their combined contribution to any agent lies in
$[-2^{-m},2^{-m}]$. This is the signed version of note 02's selector-tail
construction; it does not require recognizing shortest programs.

# 3. Counterexamples for r≤0

Set c=r+1≤1 and B=Skip. Let A take action 1 iff its **initial reward equals
1**, and otherwise always skip. A is computable and does not need to compute r.

On every skip-respecting environment, $A_c$ behaves as Skip: when the initial
reward is 1 it already meets the threshold, and otherwise A itself skips.
Thus $\Gamma'_U(A_c)=\Gamma'_U(B)=0$, and $B_r$=B.

The special μ₊ tosses a fair coin initially. On success it gives initial
reward 1 and a success observation, then offers one further unit reward for
action 1 on the first turn; on failure it gives zero and never rewards. It
then gives zero forever. Skips receive zero; any agent has expected value in
[0,1]. Its reward dual μ₋ is also well-behaved.

For A, the values are 1 in μ₊ and −1/2 in μ₋: it refuses the extra punishment
after the negative initial reward. The special weighted contribution is 1/8.
Choose m=4. Then $\Gamma'_U$(A)≥1/8−1/16>0, proving the required failure.

The r=0 case specifically separates this signed expected-value model from the
pathwise Legg–Hutter convention in note 01.

# 4. Counterexamples for r>0

Put c=r+1>1, K=⌈c⌉ and L=K+1. All rewards and partial sums are integers.
Define the computable agent A to act 1 until a partial sum has reached −K,
then skip forever. Let Q act 1 until the **absolute value** of a partial sum
has reached K, then skip forever. Q is reward-dual invariant.

On every skip-respecting environment, $A_c$ has the same trajectory as Q:
positive stopping occurs at integer threshold K, and negative stopping is
already built into A. After either event skipping freezes the reward sum.
Therefore $\Gamma'_U(A_c)=\Gamma'_U(Q)=0$ for every symmetric U. As before, take B=Skip,
so $B_r$=B and $\Gamma'_U$(B)=0.

The special μ₊ outputs initial reward zero and a success flag with probability
p=1/L. On success it offers reward +1 for action 1 on each of the next L
turns, and zero for skips; on failure all rewards are zero. Thereafter all
rewards are zero. Against every agent its expected value lies in [0,pL]=[0,1].
Its dual μ₋ offers the corresponding negative rewards and has all values in
[−1,0]. Both are computable, use the fixed finite alphabets, and are
well-behaved against stochastic agents as well.

Conditional on success:

| Policy | μ₊ total | μ₋ total |
|---|---:|---:|
| A | L | −K |
| $A_c$, equivalently Q on reachable histories | K | −K |
| Skip | 0 | 0 |

The special contribution to $\Gamma'_U$(A) is
$\tfrac14p(L-K)=1/(4L)$. Choose m≥3 with
$2^{-m}<1/(4L)$. Then

$$\Gamma'_U(A)\ge \frac1{4L}-2^{-m}>0
=\Gamma'_U(B)=\Gamma'_U(A_{r+1}),\qquad
\Gamma'_U(B_r)=\Gamma'_U(B).$$

This proves the counterexample for each r>0. The finite integer K can be built
into A even if r is not a computable real; no uniform algorithm from arbitrary
real descriptions of r is claimed. ∎

# What is and is not resolved

Under pathwise bounded totals, failure for every r is false. Under the 2021
expected-value normalization, it is realizable for every r with an explicitly
chosen symmetric universal prior. The claim for **each fixed arbitrary**
symmetric prior remains open: uncontrolled tail contributions could cancel or
reverse A's advantage. The constructions do not settle Questions 27–28 or sign
computability for all symmetric machines.

Exact finite controls (`../audit-2026-09-27/controls.py`) check the special-pair
arithmetic, threshold cases and universal-tail margins. Symmetric cancellation
over all environments is the hand argument above, not an enumeration.
