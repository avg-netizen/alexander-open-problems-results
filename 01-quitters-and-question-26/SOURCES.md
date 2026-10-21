# Sources, assumptions and proof scope

## Primary sources checked

- S. A. Alexander, *Intelligence via ultrafilters* (2019),
  [arXiv:1910.09721](https://arxiv.org/abs/1910.09721),
  [DOI 10.2478/jagi-2019-0003](https://doi.org/10.2478/jagi-2019-0003).
  Definitions 1 and 6–7 give convergent deterministic environments,
  agents and electorate comparison. Definitions 17–19, printed
  pp. 14–15, give skipping, bounded rewards and quitters.
  Proposition 20 is on printed p. 15; Question 26 is on p. 20.
- S. Legg and M. Hutter, *Universal intelligence: a definition of
  machine intelligence* (2007),
  [author manuscript](https://www.hutter1.net/ai/iorx.pdf),
  Section 3.2, equation (2), PDF page 19. Its nonnegative rational
  rewards and pathwise reward-summable bound are the explicit
  interpretation in Theorem 2.
- S. A. Alexander and M. Hutter, *Reward-punishment symmetric universal
  intelligence* (2021),
  [author manuscript](https://www.hutter1.net/publ/symintel.pdf),
  [DOI 10.1007/978-3-030-93758-4_1](https://doi.org/10.1007/978-3-030-93758-4_1).
  Definitions 1–2 use the limit of expected partial sums, not a
  pathwise cap. Definitions 8–10 specify prefix-free machines,
  suffix-free RL encoding and environment-complexity symmetry.
  Theorem 11 supplies a symmetric universal machine.
  Reward-duality results justify cancellation of dual-invariant agents.

The signed result adds a designated skip action to that expected-value
framework. It does not attribute this combined model to a single source.

## What the rewrite makes explicit

Theorem 1 writes out the positive-threshold proof, including a quitter
that never crosses its threshold. The initial reward is bounded by 1;
the failed inequality at nonpositive thresholds is strictness below r+1.

Theorem 2 distinguishes the pathwise cap from a bound on expectations.
Its negative-threshold witness can test equality to a fixed rational
initial reward, avoiding a requirement to compute an arbitrary real
threshold. The signed pathwise comparison gives value dominance at
threshold one, not equality when negative later rewards are allowed.

Lemma 3 and Appendix A retain the fixed empty-history encoding cost
in the source's function-program convention. If that code has length
ell, Kraft gives total base environment weight at most 2^ell.
The actual simulation prefix has m+ell bits, giving the residual
budget 2^(-m). The special 00/01 instructions are handled using
prefix/suffix-free parsing. This is an explicit proof expansion,
not a claim that the prior formula was copied verbatim.

The existing audit script labels its residual-budget parameter
simulation_prefix_bits. Its finite arithmetic still checks the
displayed margins, while it does not implement the universal machine
or account for arbitrary encoding syntax. Neither it nor the sampled
quitter checks certify the infinite weighted argument.

Theorem 4 has quantifier order for every r, some U and agents.
No fixed arbitrary U, single U for all r, sign-computability theorem,
or resolution of Questions 27–28 is inferred.
