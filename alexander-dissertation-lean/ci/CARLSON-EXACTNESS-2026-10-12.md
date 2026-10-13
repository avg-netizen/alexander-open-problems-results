# Exact subpatterns and isominimal initial cuts

This advances the comparison across finite seeds needed for an effective
presentation of the [common classical core](CARLSON-CORE-2026-10-12.md).
The source is Carlson, *Patterns of Resemblance of Order 2*, the author's
October 16, 2008 manuscript, printed pp. 73–75: Definition 15.5 and Lemmas
15.6–15.7. The source text is also retained in the vault's
`samuel-allen-alexander/audit-3-1-x-claude-2026-09-30/sources/p2.txt`.

`Exactness` defines the initial span through a finite carrier as all points
at or below one of its members. For a nonempty carrier this is exactly
the initial cut through its maximum; for the empty carrier it is empty.
`Str.Exact P Q` says that `Q` is a pattern, `P` generates this initial span,
and the span is 1-correct in `Q`. The development proves all three parts of
Lemma 15.6: generation implies exactness, exactness restricts to every
intermediate subpattern, and exactness implies actual substructure inclusion.

For every downward closed subcarrier, 1-correctness is equivalent to
closure under outgoing first-relation edges. This finite characterization
is proved directly from the existing `LeastGE` and `KCorrect` definitions;
it imposes no new relation semantics.

`IsominimalCuts` first derives a pointwise least exact ordinal copy of any
finite induced ordinal structure from the existing rational least-copy
theorem. Isominimality then identifies that copy with the original carrier;
uniqueness of increasing finite maps makes the copy map the identity.
Consequently every isominimal ordinal pattern is pointwise least among
all ordinal coverings, including coverings which preserve relations only
forward. This also proves that a finite union of two isominimal ordinal
patterns is isominimal.

The main restriction theorem is Lemma 15.7, generalized to every downward
closed 1-correct induced subcarrier. Splice a proposed downward-moving
isomorphism of the cut with the identity on its tail. Downward closure
ensures this map preserves strict order. Correctness excludes first edges
leaving the cut and therefore excludes second edges too; relation edges
from the tail back into the cut are excluded by their order bounds.
The splice is thus an actual ordinal covering of the whole pattern.
Whole-pattern pointwise leastness forces the cut map to be the identity,
which proves isominimality of the cut.

`ExactnessExamples` includes the empty-carrier case, the characterization
that an ordinal singleton is isominimal exactly at zero, and a negative
control built from the actual least copy of a strict two-point chain.
Its lower singleton cut is not isominimal, and an actual first edge leaves
that cut, so it is not 1-correct. This proves that removing correctness
would make the restriction statement false.

`CompileCarlsonExactness` independently checks source-shaped statements,
including an expanded isominimal restriction conclusion and the actual
cross-cut relation condition. Its 26 axiom reports are checked by the
existing whitelist. The focused GitHub workflow builds the proof modules,
controls and gate; successful GitHub compilation is required before merge.

[The least-copy continuation](CARLSON-LEAST-COPIES-2026-10-12.md) now proves
correctness and finite generation around least ordinal copies (Theorem 14.10),
least-copy agreement along valid rules, and actual exact embeddings into a finite
ordinal amalgamation (Theorem 15.9(1)). Amalgamation uniqueness and pointed-pattern
comparison from Theorem 15.9 and Lemma 15.10 remain unproved. Those results are
needed before finite certificate search can compute cross-seed equality, order,
and both resemblance relations. No effective enumeration or relation Program
follows yet from classical amalgamation existence.
