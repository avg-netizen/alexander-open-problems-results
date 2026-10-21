---
title: "Quitting thresholds and reward normalization in universal intelligence"
subtitle: "An ultrafilter boundary and explicit symmetric-prior counterexamples"
date: "21 October 2026"
abstract: |
  Alexander asks whether an intelligence advantage survives replacing an
  agent by a quitter at a threshold one unit above a comparison agent's
  threshold. We determine the boundary for his ultrafilter proposition
  and for the nonnegative pathwise reward-summable interpretation of
  universal intelligence. The ultrafilter implication holds for positive
  thresholds and fails at every nonpositive threshold. Under nonnegative
  pathwise totals bounded by one, Question 26 holds exactly for
  nonnegative thresholds. We then combine designated skipping with
  Alexander–Hutter's signed expected-value normalization. For every real
  threshold there are computable agents and a suitably chosen symmetric
  universal reference machine that violate the implication. The proof
  controls the full universal tail and states the quantifier over
  reference machines explicitly. Pathwise and expected bounds yield
  different conclusions even at threshold zero.
---

# 1. Why the reward convention matters

Stopping after a satisfactory reward total appears to preserve a
sufficiently large performance advantage. In *Intelligence via
ultrafilters* [A], Alexander makes this intuition precise: if \(A\)
outperforms \(B\), and stopping \(B\) at threshold \(r\) does not
change its score, should stopping \(A\) at \(r+1\) still leave
\(A\) ahead?

There are two separate issues. First, an initial reward is received
before any action. A quitting rule may therefore trigger before it
has had a chance to do anything. Second, a bound on each reward,
a bound on every realized total, and a bound on expected total
are different assumptions. A rare trajectory can be large while
its expectation remains small.

The paper develops those distinctions in one framework.
Section 3 treats the ultrafilter proposition. Section 4 answers
Question 26 under nonnegative pathwise reward summability.
Sections 5–7 construct signed expected-value counterexamples
with a controlled symmetric prior. The reference machine in the
last result may depend on \(r\); it is not a counterexample for
every preassigned machine.

# 2. Initial rewards, skipping, and comparison

An interaction begins with a reward and observation
\((r_1,o_1)\), followed by an action \(a_1\), then the next
reward and observation, and so on. Put
\[
                              S_n=\sum_{i=1}^n r_i.
\]
The designated skip action is 0. An environment respects
skipping if the reward in response to a skip is always zero.
This condition does not require the initial reward to vanish.

For an agent \(A\), its quitter at threshold \(c\) is
\[
 A_c(r_1,o_1,\ldots,r_n,o_n)=
 \begin{cases}
 A(r_1,o_1,\ldots,r_n,o_n),&S_n<c,\\
 0,&S_n\geq c.
 \end{cases}
\]
These are [A, Definitions 17–19]. Once a quitter skips in a
skip-respecting environment, the sum stays fixed, so it keeps
skipping. Write Skip for the agent that always skips.

In the deterministic setting, an environment is required to
give a convergent total for every agent. Its rewards are
*bounded* in [A]'s sense when each is at most 1; negative
rewards are allowed. For an electorate
\(E=((e_0,e_1,\ldots),\mathcal U)\), where \(\mathcal U\)
is an ultrafilter on \(\mathbb N\), define
\[
 A>_E B\quad\Longleftrightarrow\quad
                  \{n:V_{e_n}(A)>V_{e_n}(B)\}\in\mathcal U.
\]
Equality is defined using equality of totals in the same way.
We need only closure of \(\mathcal U\) under finite intersections
and supersets; the constant electorates below work for any
ultrafilter.

For a numerical comparison, let
\[
                         \Gamma'(\pi)=\sum_{\mu}w_\mu V_\mu(\pi),
\]
where the environments respect skipping, all weights are
positive, and the sum is well-defined. Universal intelligence
uses complexity weights \(w_\mu=2^{-K_U(\mu)}\).
Question 26 of [A, Section 6.1] asks for the implication
\[
 \Gamma'(A)>\Gamma'(B),\quad
 \Gamma'(B_r)=\Gamma'(B)
       \quad\Longrightarrow\quad
 \Gamma'(A_{r+1})>\Gamma'(B).                         \tag{Q}
\]
We specify the environment class and normalization each time
we use this question.

# 3. The exact boundary of Proposition 20

## Theorem 1. The ultrafilter implication

For every electorate with rewards at most 1 that respects
skipping, Proposition 20's implication
\[
 A>_E B,\quad B_r=_E B
                  \quad\Longrightarrow\quad A_{r+1}>_E B
\]
holds when \(r>0\). For each \(r\leq0\), a constant electorate
violates it.

**Proof: positive thresholds.** First observe that the total
earned by \(B_r\) in any environment is strictly below \(r+1\).
If its first threshold crossing occurs at \(n\geq2\), the
preceding partial sum is below \(r\), and the last reward is at
most 1. Its frozen total is therefore below \(r+1\).
If it crosses at \(n=1\), its total is \(r_1\leq1<r+1\).
If it never crosses, convergence of the total gives a limit
at most \(r\), again below \(r+1\).

Intersect the ultrafilter sets on which \(A\) beats \(B\) and
\(B_r\) equals \(B\). In every environment of that intersection,
\(V(B)<r+1\). If \(A\) never reaches \(r+1\), its quitter
has exactly its original run and still beats \(B\). If it
reaches that threshold, its quitter freezes at a total at
least \(r+1>V(B)\). Thus the winning set for \(A_{r+1}\)
contains an ultrafilter set, as required.

**Proof: nonpositive thresholds.** Use one environment repeatedly.
It gives initial reward 1, then reward \(1/2\) if the first
action is nonzero, and zero thereafter. Rewards are at most
1, skipping receives zero, and every total converges.

Let \(A\) always choose action 1 and \(B=\mathrm{Skip}\).
Their totals are \(3/2\) and 1. The quitter \(B_r\) still skips.
But \(r+1\leq1\), so \(A_{r+1}\) skips at its first decision
and also earns 1. All hypotheses hold and strict superiority
fails.
\(\square\)

The printed proof's overshoot argument applies after an action
has produced a reward. At the first decision there is no
preceding partial sum below \(r\). The initial reward is still
bounded by 1; what fails at \(r\leq0\) is its required strict
comparison with \(r+1\).

This distinction is elementary but consequential: a per-reward
bound permits total \(3/2\), whereas the next section's
environment class excludes it.

# 4. Nonnegative pathwise reward summability

Use nonnegative rewards and require every realized total to be
at most 1, as in Legg–Hutter's reward-summable model
[LH, Section 3.2]. Restrict to computable skip-respecting
environments, each with positive universal weight.
Keep the initial-reward convention of Section 2.

## Theorem 2. Question 26 holds exactly for \(r\geq0\)

In this class, (Q) holds for every \(r\geq0\). For every
\(r<0\) there are computable deterministic \(A,B\) violating
it, for any full-support universal prior on this class.

**Proof: \(r\geq0\).** All partial sums lie in \([0,1]\).
If \(r>0\), the threshold \(r+1>1\) is never reached, so
\(A_{r+1}\) has exactly \(A\)'s value. If \(r=0\), the
quitter can stop only at sum 1. Nonnegativity and the total
bound force every subsequent reward of \(A\)'s original
run to be zero. Again the values agree in every environment.
Thus the first hypothesis alone gives the desired strict
inequality.

**Proof: \(r<0\).** Put \(c=r+1<1\) and \(B=\mathrm{Skip}\);
then \(B_r=B\). Any agent earns at least Skip's value:
Skip earns the initial reward and nothing further, while
all additional rewards are nonnegative.

If \(c\leq0\), take \(A\) to choose action 1 on its first
turn and skip thereafter. Its quitter skips immediately in
every environment. There is a computable environment giving
zero initially and a positive reward for that first action,
so \(A\) strictly beats Skip under every positive-weight
universal prior.

If \(0<c<1\), choose a rational \(b\in[c,1)\).
Let \(A\) choose action 1 on its first turn exactly when the
initial reward equals \(b\), and skip thereafter. Its quitter
\(A_c\) always behaves as Skip: on the only histories where
\(A\) would act, the initial reward already reaches \(c\).
An environment giving initial reward \(b\) and an additional
\((1-b)/2\) for the first non-skip action is computable and
reward summable. It gives \(A\) a strict advantage. Everywhere
else the advantage is nonnegative, so the weighted sum is
strictly positive. This proves the failure of (Q).
\(\square\)

The rational \(b\) is a fixed parameter of the witness, not an
algorithm required to compute an arbitrary real \(r\).
Testing equality to \(b\) is computable on the rational reward
symbols in this model.

Here the averaged premise about \(B_r\) is stronger than it
may first appear: quitting never improves a nonnegative-reward
run. Equality of the weighted sums, with all weights positive,
forces equality in each environment. The proof above does
not need that fact, because the conclusion for \(r\geq0\)
already follows from the pathwise cap.

## A signed pathwise comparison

Allowing negative rewards alone does not remove the positive
result. Suppose totals converge and every realized total
under every policy is still at most 1. Any reachable finite
partial sum is at most 1: follow its action prefix and then
skip forever to freeze that sum.

For \(r>0\), \(A_{r+1}\) therefore never stops.
For \(r=0\), if it stops it freezes at 1, while \(A\)'s
original eventual total is at most 1. Hence
\(V(A_1)\geq V(A)\). Positive weights again imply (Q) for
\(r\geq0\). With signed rewards this is an inequality,
rather than the per-environment equality in Theorem 2.

# 5. Expected bounds and a symmetric universal prior

Alexander–Hutter [AH, Definitions 1–2] use a different condition:
\[
 V_\mu^\pi=\lim_n\mathbb E_\mu^\pi S_n
                         \text{ exists in }[-1,1]
                    \quad\text{for every agent }\pi.
\]
A computable environment satisfying it is well-behaved.
This does not bound each realized trajectory by 1.

For example, with probability \(1/L\) an environment can
offer \(L\) unit rewards, and otherwise offer none.
Every agent's expected reward is at most 1, while a successful
branch can reach \(L\). This is the mechanism used below.
We use at least two actions, two observations, reward alphabet
\(\{-1,0,1\}\), and the additional designated-skip convention.
This is an explicitly combined model, rather than a change
to the wording of either source.

Reward duality negates rewards in histories and outputs.
Write \(\bar\mu\) for the dual environment and \(\bar\pi\)
for the dual agent. The skip-respecting well-behaved class
\(W_{\rm skip}\) is closed under this operation.
Fix a prefix-free, suffix-free RL encoding whose codes begin with 0;
this choice can be made once for all thresholds. For an
encoding-symmetric universal machine \(U\), put
\[
       \Gamma'_U(\pi)=
             \sum_{\mu\in W_{\rm skip}}2^{-K_U(\mu)}V_\mu^\pi.
\]
If \(\bar\pi=\pi\), dual pairs cancel and \(\Gamma'_U(\pi)=0\).
In particular \(\Gamma'_U(\mathrm{Skip})=0\).
Absolute convergence justifies pairing; Appendix A gives
an explicit weight bound in the source's encoding convention.

## Lemma 3. A symmetric prior with a controlled tail

Fix a computable non-self-dual pair \(\mu_+,\mu_-=\bar\mu_+\).
For any \(m\geq3\), there is an encoding-symmetric prefix-free
universal machine \(U\) for which both special complexities
are 2 and the total weight of all other environments is at
most \(2^{-m}\).

**Proof.** Use the fixed encoding and let \(\ell\) be the length of its
empty-history code. Fix an encoding-symmetric universal
machine \(U_0\), supplied by [AH, Theorem 11].
Reserve programs 00 and 01 for the two special environments,
and a branch beginning with \(1^{m+\ell}\) to simulate \(U_0\).
These branches are prefix-disjoint.

Appendix A spells out parsing in the source's function-program
convention. No shorter special instruction is possible, and
every nonspecial environment has complexity
\(m+\ell+K_{U_0}(\mu)\). The fixed-input Kraft bound there gives
\(\sum_\mu2^{-K_{U_0}(\mu)}\leq2^\ell\).
Consequently the nonspecial weight is at most \(2^{-m}\).
Equal special lengths and the symmetry of \(U_0\) preserve
equal complexity for every dual pair.
\(\square\)

Since every value lies in \([-1,1]\), the entire nonspecial
contribution to any agent's score is in
\([-2^{-m},2^{-m}]\). Thus a special-pair advantage exceeding
that budget survives all remaining environments, without
enumerating them or identifying shortest programs.

# 6. Counterexamples at nonpositive thresholds

## Theorem 4. Signed expected-value counterexamples

For every real \(r\), there exist computable agents \(A,B\)
and an encoding-symmetric universal machine \(U\) such that
\[
 \Gamma'_U(A)>\Gamma'_U(B),\qquad
 \Gamma'_U(B_r)=\Gamma'_U(B),\qquad
 \Gamma'_U(A_{r+1})=\Gamma'_U(B).
\]

**Proof for \(r\leq0\).** Let \(B=\mathrm{Skip}\), and let
\(A\) choose action 1 on every turn if its initial reward is
1, otherwise skip. Put \(c=r+1\leq1\).
In every skip-respecting environment \(A_c\) behaves as Skip.
When the initial reward is 1, it stops immediately; otherwise
\(A\) itself skips. Thus both quitters have score zero.

The special environment \(\mu_+\) tosses a fair initial coin.
On success it gives initial reward 1 and offers one more unit
for action 1 on the first turn. On failure all rewards are
zero. After that first action all rewards are zero.
Every agent has expected value in \([0,1]\).
Use its reward dual for \(\mu_-\).

Agent \(A\) gets value 1 in \(\mu_+\), and \(-1/2\) in
\(\mu_-\): after the negative initial reward it skips the
extra punishment. Give these environments the special codes
from Lemma 3. Their weighted contribution is
\((1-1/2)/4=1/8\).
Choose \(m=4\), so the full score is at least
\(1/8-1/16>0\), whereas Skip and both required quitters
have score zero.
\(\square\)

This includes \(r=0\), where the pathwise model gave an
affirmative result. The successful positive branch here totals
2, so it does not belong to that stronger environment class.

# 7. Counterexamples at positive thresholds

**Completion of Theorem 4 for \(r>0\).** Put
\[
                  c=r+1>1,\qquad K=\lceil c\rceil,\qquad L=K+1.
\]
Let \(A\) choose action 1 until its partial sum first reaches
\(-K\), then skip forever. Let \(Q\) choose action 1 until
the absolute value of its partial sum first reaches \(K\),
then skip forever. These are computable finite-threshold rules.

All partial sums are integers. Positive threshold \(c\) is
therefore crossed precisely at integer threshold \(K\).
The negative stopping rule is already built into \(A\).
Thus \(A_c\) and \(Q\) have the same reachable trajectories
in every skip-respecting environment in this alphabet.
The rule \(Q\) is reward-dual invariant, so
\(\Gamma'_U(A_c)=\Gamma'_U(Q)=0\) for every symmetric \(U\).

Let \(\mu_+\) issue initial reward zero and a success flag
with probability \(p=1/L\). On success it offers reward 1
for action 1 on each of the next \(L\) turns; on failure
all rewards are zero. Skips receive zero. Use the dual
environment for \(\mu_-\). These environments are computable
and well-behaved against every agent, including stochastic
ones: on the success branch at most \(L\) rewards can be
collected, and \(pL=1\).

Conditional on success, their totals are

| Agent | In \(\mu_+\) | In \(\mu_-\) |
|---|---:|---:|
| \(A\) | \(L\) | \(-K\) |
| \(A_c=Q\) on reachable histories | \(K\) | \(-K\) |
| Skip | \(0\) | \(0\) |

The pair contributes
\[
                \frac14\,p(L-K)=\frac1{4L}
\]
to \(A\)'s score. Choose \(m\geq3\) with
\(2^{-m}<1/(4L)\) and apply Lemma 3. Then
\[
             \Gamma'_U(A)\geq\frac1{4L}-2^{-m}>0.
\]
Taking \(B=\mathrm{Skip}\) completes all three assertions.
The integer \(K\) is built into the witnesses; no uniform
algorithm from an arbitrary real representation of \(r\)
is claimed.
\(\square\)

![The positive-threshold construction, conditional on success. The original agent collects one more positive unit than its quitter while stopping at the same negative threshold. Dual-invariant \(Q\) cancels exactly across the symmetric prior.](figures/rare-branch.pdf){width=95%}

# 8. What the answers depend on

The outcomes can now be compared without changing conventions
inside an argument.

| Setting | Conclusion established here |
|---|---|
| Deterministic electorate, individual rewards at most 1 | Proposition 20 holds for \(r>0\); counterexamples for every \(r\leq0\) |
| Nonnegative rewards, realized totals at most 1 | Question 26 holds exactly for \(r\geq0\), for any full-support universal prior |
| Signed rewards, realized totals at most 1 | The implication still holds for \(r\geq0\) |
| Signed rewards, expected totals in \([-1,1]\) | For each \(r\), some symmetric universal prior and computable agents violate it |

The last row has quantifier order
\(\forall r\,\exists U\,\exists A,B\).
It proves neither failure for every fixed symmetric \(U\)
nor the existence of one \(U\) working at all thresholds.
The fixed-prior question is left unresolved by this paper.

The result also concerns the restriction to skip-respecting
environments. It does not classify the unrestricted measure,
the sign-computability question in [AH], or the alternative
intelligence measures in [A, Questions 27–28].

# Appendix A. Encoding and the tail budget

The source [AH, Definitions 8–10] describes a machine as a
prefix-free partial function on binary strings. An instruction
\(y\) computes an environment when
\(U(y\kappa(s))=\kappa(\mu(\cdot\mid s))\) for every history
\(s\), where \(\kappa\) is the RL encoding.
A fixed encoding cost should therefore be retained in a
Kraft estimate.

Choose a prefix-free, suffix-free encoding with a common
initial 0 and codes long enough to avoid empty-code edge
cases. A common prefix can be added to a source encoding
without losing either property.
Let \(\ell=|\kappa(\varnothing)|\).
For one shortest instruction \(y_\mu\) per environment,
the distinct strings \(y_\mu\kappa(\varnothing)\) belong
to the prefix-free domain of \(U_0\). Hence
\[
       \sum_\mu2^{-(|y_\mu|+\ell)}\leq1,\qquad
       \sum_\mu2^{-K_{U_0}(\mu)}\leq2^\ell.
\]
This also proves absolute convergence on any subclass with
values bounded by 1.

For Lemma 3, define the special branches on exactly the
arguments \(00\kappa(s)\) and \(01\kappa(s)\), returning
the corresponding encoded output laws. Define
\(U(1^{m+\ell}x)=U_0(x)\), and leave other strings undefined.
The domain is prefix-free; the last branch gives universality.

Suffix-freeness makes a special instruction followed by any
extra nonempty prefix before \(\kappa(s)\) invalid: the
result cannot be a history code with \(\kappa(s)\) as a
proper suffix. Instructions of length zero or one cannot
compute an environment either. The empty instruction and
instruction 0 would require a strict suffix of a history
code in a special branch; instruction 1 meets an invalid
10 prefix. A proper initial segment of the long all-ones
branch also fails when the following history code begins
with 0. Every valid nonspecial instruction therefore has
the full simulation prefix followed by a \(U_0\) instruction.
This proves the complexity equalities used in Lemma 3.
\(\square\)

# Appendix B. Finite controls

The retained quitter program checks the initial-reward
counterexample and sampled finite positive-weight comparisons
using exact rational arithmetic. Its record has 90 sampled
nonnegative-threshold cases without a violation and 110
negative-threshold counterexamples. Those finite samples are
controls, not the universal proof of Theorem 2.

The retained audit controls check the special-pair margins,
integer threshold behavior and reward-dual cancellation on
8,748 finite reward tapes. The script's margin parameter
represents the residual budget \(2^{-m}\); Appendix A includes
the additional fixed encoding cost in the actual simulation
prefix. The controls do not implement a universal machine or
enumerate its environments. All programs and saved outputs
are unchanged.

# References

**[A]** Samuel Allen Alexander. *Intelligence via ultrafilters:
structural properties of some intelligence comparators of
deterministic Legg–Hutter agents*. Journal of Artificial
General Intelligence 10(1), 2019.
[DOI: 10.2478/jagi-2019-0003](https://doi.org/10.2478/jagi-2019-0003);
[arXiv:1910.09721](https://arxiv.org/abs/1910.09721).
Definitions 1, 6–7, 17–19; Proposition 20; Question 26.

**[LH]** Shane Legg and Marcus Hutter. *Universal intelligence:
a definition of machine intelligence*. Minds and Machines
17 (2007), 391–444.
[DOI: 10.1007/s11023-007-9079-x](https://doi.org/10.1007/s11023-007-9079-x).
[Author manuscript](https://www.hutter1.net/ai/iorx.pdf),
Section 3.2, reward-summable environments, equation (2).

**[AH]** Samuel Allen Alexander and Marcus Hutter.
*Reward-punishment symmetric universal intelligence*.
Artificial General Intelligence (2021).
[DOI: 10.1007/978-3-030-93758-4_1](https://doi.org/10.1007/978-3-030-93758-4_1);
[author manuscript](https://www.hutter1.net/publ/symintel.pdf).
Definitions 1–2 and 8–13; Theorem 11 and reward-duality results.
