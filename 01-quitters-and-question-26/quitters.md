---
title: "Quitters: a correction to Proposition 20 and an answer to Question 26"
subtitle: "On S. A. Alexander, *Intelligence via Ultrafilters* (2019)"
date: "25 September 2026"
---

**Status.** Elementary hand proofs, with an exact-arithmetic check script. No independent human
review. A bounded search did not locate a published answer; priority is not established.

**Source.** S. A. Alexander, *Intelligence via ultrafilters: structural properties of some
intelligence comparators of deterministic Legg–Hutter agents*, Journal of Artificial General
Intelligence 10(1), 2019. [arXiv:1910.09721](https://arxiv.org/abs/1910.09721),
[doi:10.2478/jagi-2019-0003](https://doi.org/10.2478/jagi-2019-0003).

**Summary.**

1. **Proposition 20 is false as printed for every r ≤ 0, and true for every r > 0.** The initial
   reward arrives before any action, so neither the skipping hypothesis nor the bounded-reward
   hypothesis constrains it. It alone can reach r + 1.
2. **Question 26, under Legg and Hutter's own normalisation** (rewards in [0, 1], total reward at
   most 1): the answer is **yes for every r ≥ 0 and no for every r < 0**. The negative cases turn
   on the same initial-reward edge.

Check script: `quitters_check.py` in this folder, which writes `quitters_check.json`.

# The setting (the paper's Definitions 1, 17–19)

- The environment emits an **initial** reward–observation pair (r₁, o₁) = e(⟨⟩) *before* the
  agent's first action. A deterministic agent (DLHA) maps reward–observation histories to actions.
- An environment **respects skipping** if the reward in response to the action "skip" (0) is 0.
  It has **bounded rewards** if every reward is at most 1. Rewards may be negative.
- The **quitter** $A_r$ acts as A while r₁ + ⋯ + rₙ < r, and skips forever once the sum is at least
  r.

**Proposition 20** (as printed). Let E be an electorate with bounded rewards that respects
skipping, let A $>_E$ B, and let r ∈ ℝ. If $B_r$ $=_E$ B, then $A_{r+1}$ $>_E$ B.

**Question 26.** Let Γ′ be Legg–Hutter universal intelligence restricted to environments that
respect skipping and have bounded rewards. If Γ′(A) > Γ′(B) and Γ′($B_r$) = Γ′(B), must
Γ′($A_{r+1}$) > Γ′(B)?

# 1. Proposition 20 fails for every r ≤ 0 and holds for r > 0

**The gap.** The proof asserts that $B_r$'s total is below r + 1. The argument is that $B_r$ stops at
the first n with r₁ + ⋯ + rₙ ≥ r, and the last reward is at most 1. That is right when n ≥ 2,
since the previous partial sum is below r.

When n = 1, the total is just r₁, the initial reward. That reward is *not* a response to a skip,
so neither hypothesis bounds it below 1. If r₁ ≥ r + 1, which is possible exactly when r ≤ 0, the
step fails.

**Counterexample (any r ≤ 0).** Let every eₙ be the same environment e. It gives initial reward
1, then reward ½ in response to a first action that is not "skip", and 0 otherwise.
- It has bounded rewards and respects skipping. Definition 6 allows any sequence of environments,
  including constant sequences.
- Let A = always act 1, with total 3/2, and B = always skip, with total 1. Then A $>_E$ B.
- $B_r$ = B, since B only skips anyway, so $B_r$ $=_E$ B.
- $A_{r+1}$ sees r₁ = 1 ≥ r + 1 and skips at once, with total 1. So $A_{r+1}$ $=_E$ B, **not**
  $A_{r+1}$ $>_E$ B.

The script checks this at r = −1, −½ and 0. At r = ¼ the conclusion holds.

**Repair.** For r > 0 the case n = 1 is harmless: r₁ ≥ r > 0 and r₁ ≤ 1 give r₁ < r + 1. The
printed proof then goes through unchanged. So Proposition 20 holds with the hypothesis
**r > 0**. For r ≤ 0 it needs an extra condition, for instance that initial rewards are below
r + 1.

# 2. Question 26 under Legg–Hutter normalisation: yes iff r ≥ 0

Γ is Legg and Hutter's measure. Its environments have rewards in [0, 1] and **total reward at
most 1** for every agent, and every environment of the restricted class gets a positive weight
2^(−K).

**Two facts used throughout.**

1. **Quitting never helps when rewards are non-negative.** Couple the two runs on the same
   environment randomness. $B_r$ earns B's rewards until it stops, and 0 afterwards; B earns ≥ 0
   afterwards. So $V_e$($B_r$) ≤ $V_e$(B) in every environment. All weights are positive, so
   **Γ′($B_r$) = Γ′(B) forces $V_e$($B_r$) = $V_e$(B) for every e.** The same argument gives
   $V_e$(Skip) ≤ $V_e$(X) for every agent X.
2. **Partial sums never exceed 1**, since totals are at most 1.

**r > 0: yes.** The stopping condition, a partial sum ≥ r + 1 > 1, never occurs. So $A_{r+1}$ plays
exactly as A on every reachable history, and Γ′($A_{r+1}$) = Γ′(A) > Γ′(B).

**r = 0: yes.** A₁ stops only once its partial sum reaches 1. The total is at most 1, so every
later reward is 0, whichever agent plays. So $V_e$(A₁) = $V_e$(A), and Γ′(A₁) = Γ′(A) > Γ′(B).

**r < 0: no.** Put c = r + 1 < 1 and let B = Skip. Every partial sum is ≥ 0 > r, so $B_r$ = Skip = B
and the hypothesis holds.
- **If c ≤ 0,** take A = always act 1.
  - $A_{r+1}$ skips from the start, so Γ′($A_{r+1}$) = Γ′(Skip) = Γ′(B).
  - Yet Γ′(A) > Γ′(Skip): the class contains an environment that rewards acting, and A never
    scores below Skip.
- **If 0 < c < 1,** take A = "act 1 if r₁ ≥ c, else skip".
  - *The gain is real.* The class contains e\*, with initial reward q ∈ [c, 1) (rational) and then
    (1 − q)/2 for acting once. A gains there, so Γ′(A) > Γ′(B).
  - *The quitter throws it away.* $A_c$ skips at once whenever r₁ ≥ c. When r₁ < c it copies A,
    which skips, so its partial sum never reaches c. On every trajectory $A_{r+1}$ scores exactly as
    Skip, so Γ′($A_{r+1}$) = Γ′(B).

A randomized check found no violation in 90 cases with r ≥ 0, and a counterexample in all 110
cases with r < 0. It uses positive stand-in weights, since the arguments above do not depend on
the weights' values.

**Reading.**
- Under Legg and Hutter's own normalisation, Question 26 is nearly degenerate for r > 0: a
  total-≤ 1 environment never lets a quitter with threshold above 1 quit.
- Its content sits at r ≤ 0, and it is decided by the **same initial-reward edge case** that
  breaks Proposition 20.
- In the ultrafilter setting totals can exceed 1. That is why r = 0 fails there but holds here.

# Scope

- The answer takes Γ to be Legg–Hutter 2007, with rewards in [0, 1] and totals at most 1.
- The paper adds "bounded rewards" to Γ′ as if Γ lacked it. That suggests it may have intended a
  class with larger totals, or with negative rewards. Under such a normalisation:
  - quitting can *help*, by avoiding later punishment, so the per-environment equality in fact 1
    is lost;
  - the averaged hypothesis Γ′($B_r$) = Γ′(B) then allows cancellations;
  - a counterexample for r > 0 would need explicit control of universal weights.

  That variant is **not** settled here. A conjecture about it is in `09-further-results`.
- Questions 27–28 (the Hernández-Orallo–Dowe and Hibbard analogues) are untouched.
- Both results are elementary. The correction concerns the printed statement; the intended use
  (r > 0) is unaffected.

# References

- S. Legg and M. Hutter, *Universal intelligence: a definition of machine intelligence*, Minds and
  Machines 17(4), 2007, 391–444.
- S. A. Alexander, *Intelligence via ultrafilters*, as above: Definitions 1, 6, 17–19,
  Proposition 20, Question 26.
