# Source map and model contracts

Samuel Allen Alexander, *Pseudo-visibility: a game mechanic involving
willful ignorance*, FLAIRS-35 (2022),
[DOI 10.32473/flairs.v35i.130652](https://doi.org/10.32473/flairs.v35i.130652).

| Source location | Use |
|---|---|
| Definition 2 | The environment queries the erased-observation action and penalizes mismatch |
| Discussion after Lemma 4 | Generator-state advice; reproducibility does not imply independent calls |
| Definitions 9–10 | Agent act/train interface and annotation wrapper |
| Proposition 12 | Environment-side representation of the wrapper |
| Better-performance discussion | Informal motivation and the possibility that the underlying agent already reflects |

The current paper proves a fixed-query information theorem and a different
policy-dependent learning theorem. Neither is a blanket formalization
of every possible meaning of the source's informal conjecture.

Theorem 2 holds the query distribution fixed and assumes no query access
or correlated private randomness for the plain action. Its base reward
has the stated query-independent conditional mean. Equal marginal action
probabilities alone do not imply those assumptions.

Theorem 4 specifies independent episode sampling, infinite action visits,
sample averages, unique maximizers and conditionally unbiased noise with
bounded conditional second moments. This makes the sample-average law
of large numbers applicable at adaptive visits. Merely having stationary
marginal means, without a suitable noise law, is not its assertion.
The result is about greedy-policy evaluation, not persistent exploratory
training reward, constant steps, general function approximation or MDPs.

## Computational records

The saved program and JSON remain at their existing paths in
09-further-results/pseudovisibility/. The coupled run has 4,000 episodes,
30 seeds, exploration 0.1, noise standard deviation 0.3, visible
probability 0.5 and penalty 2. Its final greedy values are both 0.5,
while enumerating all four deterministic action pairs gives 0.95.

The 40-context scenario uses base-reward seed 56, four actions, a
0.4 visible bonus, penalty 0.6, visible probability 0.4, noise
standard deviation 0.5, and 2,000/20,000 episodes.
The figure uses saved final means and standard errors for sample-average
greedy-query tabular and step-0.05 greedy-query linear learners.
It does not interpolate a learning curve or test a paired difference.

The existing audit controls verify the shared-fair-bit example and
the exact flat-reward and 7/8 equality calculations. No new training
campaign, performance ranking or learning-rate result was added.
The new equality criterion follows directly from the displayed
max-versus-average formula.
