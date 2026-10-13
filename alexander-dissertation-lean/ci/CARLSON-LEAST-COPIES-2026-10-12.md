# Least-copy completeness and finite amalgamation existence

The source is Carlson, *Patterns of Resemblance of Order 2*, October 16, 2008
manuscript: Theorem 14.10 (printed pp. 67–68), the agreement implication of
Theorem 14.11 (pp. 69–70), and Definition 15.8 / Theorem 15.9(1) (pp. 74–75).
The retained source is `samuel-allen-alexander/audit-3-1-x-claude-2026-09-30/sources/p2.txt`.
These results concern the pure language with the two resemblance relations.

`OrdinalGenerationTransport` moves a derivation's entire finite support to
ordinal ranks before transporting its endpoints. This includes intermediate
labels hidden in a recursive certificate; it does not extend an endpoint map
arbitrarily across that support. It proves transport for generating rules and
exact generation chains.

`LeastCopyCompleteness` captures any finite subset below a fair realization's
bound in one actual stage. Stage chains then generate every bounded induced finite
extension. Both stages and every finite isominimal ordinal carrier are correct
at both relation levels in every finite induced ordinal ambient structure. The
ambient structure need not be contained in the fair limit. Global relation bounds
force every point needed for correctness below the limit bound.

For an isominimal carrier U contained in V, U generates V exactly when each point
of V is at or below some old point of U. This includes the empty carrier without
assuming that a maximum exists. Together with unconditional coveredness,
`exists_complete_minimal_ordinal_copy` supplies the pure-case conclusions of
Theorem 14.10: an exact least copy, pointwise minimality among all coverings,
isominimality, global correctness, and generation of bounded finite extensions.
There is no separate arithmetic closure obligation in this pure language.

`LeastCopyAgreement` proves that actual least realizations agree on the source
of a valid rational rule. It also proves that a valid ordinal subpattern of an
isominimal target is isominimal. This is the agreement implication of 14.11;
it does not assume or prove the full converse characterization.

`AmalgamationExistence` proves that every isominimal ordinal carrier is exact in
any finite induced ordinal structure containing it. It defines the actual
Definition 15.8 obligations: a target pattern, an explicit isomorphism from each
input to its induced image, the union of those images, and exactness of every
image in the target. Every finite family of pure rational patterns has such an
ordinal amalgamation: take the union of their actual least copies. Both the union
and every input image are isominimal. The family may have length zero.

The focused gate expands the ambient correctness and amalgamation obligations,
audits all new declarations transitively (28 reports), and uses the existing axiom whitelist.
Controls include empty and singleton carriers, a genuine nonidentity generated
extension of a least strict two-point second-relation chain, failure without
boundedness, and failure without isominimality. Amalgamation controls include an
empty family, coalescence of two distinct rational singletons at ordinal zero,
failure of an ordinary covered union to satisfy exactness, and least-copy
agreement on a genuine downward reflection adding a third point. GitHub compilation of proofs,
controls, and the gate is required before merge.

The [October 13 continuation](CARLSON-POINTED-COMPARISON-2026-10-13.md) proves
Theorem 15.9 uniqueness and rational existence, pointed-pattern comparison in
Lemma 15.10(1), and the full pure rational 14.11 characterization.
Effective amalgamation algorithms remain open.
The existence construction is classical. It is not an effective representative
enumeration or a computation of cross-seed relations. Fair-stage algorithms still
need implementation in the project's `Program` language; unconditional 3-1-3 and
3-1-2 remain unconstructed.
