# Generation characterization and pointed core comparison

The subsequent [effective comparison checkpoint](CARLSON-EFFECTIVE-COMPARISON-2026-10-13.md)
now supplies certified exactness and amalgamation verifiers, terminating
certificate search, and actual machines for all five pointed comparisons.
The remaining-work descriptions below record this earlier checkpoint's scope.

The source is Carlson, *Patterns of Resemblance of Order 2*, October 16, 2008
manuscript: Theorem 14.11 and Corollary 14.12 (printed pp. 69–70),
Definition 15.8 / Theorem 15.9 (pp. 74–76), and Lemma 15.10(1) (p. 76).
The retained text is
`samuel-allen-alexander/audit-3-1-x-claude-2026-09-30/sources/p2.txt`.
These results concern the pure rational language with the two resemblance
relations. There is no further arithmetic function-symbol obligation in this case.

`FiniteIsomorphism` constructs finite carrier order isomorphisms, proves their
uniqueness on the carrier, and identifies two copies of the same finite target
by an actual isomorphism. The total maps can differ away from their carriers.

`ExactLeastCopyAgreement` proves that an exact subpattern retains its labels
in the actual least ordinal realization of the target. Its initial span has
an isominimal image because it is an initial, 1-correct subcarrier of the
isominimal target image. Agreement along the source-to-span generation then
identifies each old label. Exact embeddings therefore commute with the given
actual least realizations; the statement names the given embedding.

`DenseGenerationTransport` extends any prescribed increasing finite map into
an unbounded dense order while retaining its prescribed values. For compatible
rational endpoint isomorphisms, it extends the target map over the generation
proof's entire finite support, including hidden recursive patterns and the
larger chain witness. It then transports actual generation and exactness.
Compatibility is required only on the old carrier; an arbitrary extension of
the endpoint map is not assumed increasing.

`GenerationCharacterization` proves the full pure rational Theorem 14.11.
For patterns P and Q, generation is equivalent to validity plus continuity,
and to cofinal validity plus continuity. For an induced subpattern and actual
least realizations A and B, generation is equivalent to both: every point of
Q is at or below an old point of P, and B agrees with A on P. The ordinal
least-copy completeness theorem gives generation of the corresponding images;
the finite-support transport brings it back to the given rational endpoints.
Coveredness is discharged for all pure rational patterns. The bound formulation
also handles empty carriers without a chosen maximum. Actual rational generation
composes, completing Corollary 14.12 together with the existing restriction lemma.

`AmalgamationUniqueness` proves Theorem 15.9(2): any two rational amalgamations
have an actual isomorphism compatible with every supplied input embedding.
Exact-label agreement identifies both least target images with the union of
the least input images. A finite inverse then supplies the compatible map.
The family can be empty and its input images can overlap.

`PointedPatternComparison` defines a pointed pattern using an existing encoded
`CoreSeed` and a point of its finite carrier. Its map is that point's actual
least ordinal label. Its image is exactly the existing `CorePoint` domain.
In any rational amalgamation, equality, non-strict and strict order, and the
actual ordinal R1 and R2 relations of these labels are equivalent to the
corresponding finite comparisons on the distinguished images. This proves
Lemma 15.10(1) for these relation symbols, including negative comparisons.

`RationalAmalgamation` proves actual rational amalgamation existence for every
finite family of pure rational patterns. It relabels the ordinal union into
rationals and transports each input's exactness. The target can be chosen in
the existing finite-edge `RationalPresentation` format. This is an existential
construction; it does not yet give a computable search or comparison procedure.

Two independent gates expand the original generation, validity, continuity,
amalgamation, and actual core-label comparison obligations. They audit the new
public declarations transitively: 21 reports in
`CompileCarlsonGenerationCharacterization.lean` and 28 in
`CompileCarlsonPointedComparison.lean`, including the pointed-pattern type.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

Twelve controls cover fixed rational endpoints with a new point between them,
placement on both sides of a fixed point, rejection of reversed endpoints,
boundedness without validity, validity without boundedness, coalescence of
distinct singleton inputs, target displacement from 0 to 17, carrier uniqueness
with distinct off-carrier maps, empty families, positive and negative strict
R2-chain comparisons, and singleton versus first strict-chain label. A final
finite-edge amalgamation combines a singleton and a strict two-point R2 chain:
their input point 0 must have different images, with the singleton before
the chain and the reverse R2 edge absent. Ordinary identity union cannot realize
that witness.

`compile-carlson-pointed-comparison.yml` builds the proofs and controls and
checks both gates with the existing axiom policy. GitHub CI must pass before
merge. The pure semantic comparison is now proved, but effective exactness
and amalgamation recognition, terminating pointed comparison procedures,
fair-stage recursion in the project's `Program` language, duplicate-free
natural enumeration of the whole common core, and its actual relation Programs
remain. Unconditional 3-1-3 and 3-1-2 are still unconstructed.
