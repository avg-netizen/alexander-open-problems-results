# Effective exactness, amalgamation search and pointed comparison

This checkpoint formalizes Carlson's Definition 15.8, the fixed-arity
positive verifier route of Lemma 15.12(4), and the pure rational case of
Theorem 15.13, using the preceding rational
amalgamation existence and actual pointed-label comparison theorems.
The retained source is *Patterns of Resemblance of Order 2*, October 16,
2008 manuscript, printed pp. 74–78, at
`samuel-allen-alexander/audit-3-1-x-claude-2026-09-30/sources/p2.txt`.

`RationalExactness` computes the target's initial span and checks its
patternhood, an original generation certificate, and the 1-correct boundary.
Acceptance is equivalent to original semantic `Str.Exact`, for arbitrary
stored presentations. Restriction changes the carrier and retains the stored
edge tables, including irrelevant off-carrier edges. The historical dependent
`RationalCertificate` and mutual derivation decoders are preserved exactly.
`PrimitiveRationalExactness` certifies patternhood, restriction, span,
boundary correctness and the complete verifier as primitive recursive.
One actual `Nat.Partrec.Code` machine handles every raw certificate code.

`RationalMaps` evaluates finite association tables: the first matching key
wins and missing keys return zero. Completeness lists the supplied map on
its finite carrier, retaining its values there without constraining its
off-carrier behavior. `PrimitiveRationalMaps` certifies evaluation by a
list fold. `PrimitiveRationalIso` certifies the original carrier image,
strict-order and two relation equivalences on all carrier pairs.

`AmalgamationCertificates` stores a finite-edge target, one finite map table
and one exactness code per input. The complete checker verifies target
patternhood, every original input embedding, the covered union and every
input image's exactness in the target. Acceptance implies original
`Str.Amalgamation`; every actual rational amalgamation has an accepted
candidate with that same target and the same map values on the input carriers.
Rational finite-edge existence then supplies a termination witness for
every finite pattern family, including the empty family.

This **new** candidate format explicitly uses the existing product, list,
and `Encodable.finArrow` vector codecs. It does not use the distinct general
dependent finite-function codec selected by ordinary instance search.
`PrimitiveAmalgamationCertificates` certifies the actual selected decoder
and complete checker on every raw candidate code, for each fixed input
dimension. Its input-family encoding is proved equal to the ordinary
encoding of `List.ofFn P`; it is not an assumed codec equivalence.

`ComputableAmalgamation` tests natural candidate codes in increasing order
with `Nat.find`. Its existence proof supplies termination and is erased
from execution; it does not choose the returned candidate. The decoded
result satisfies all original amalgamation requirements. A supplied
accepted witness bounds the search; no uniform complexity bound or practical
runtime is claimed. `PartialAmalgamationSearch` proves minimization of the
same total checker is partial recursive, gives an actual machine code,
and proves it halts at exactly the same least code on every pattern family.

`ComputablePointedComparison` reads equality, non-strict and strict order,
R1 and R2 from that computed two-input amalgamation. Each Boolean answer
is equivalent to the corresponding relation between the input points'
**actual** least ordinal labels. `PartialPointedComparison` certifies one
partial-recursive machine on two presentations and two rational points.
It terminates on every typed pointed-pattern input and outputs the same
five Booleans, encoded with the existing product codec. The computation
does not take ordinal labels or a semantic comparison oracle as inputs.

Twenty-nine controls include a proper downward-reflection extension with
a new point; exactness acceptance; generation and patternhood passing while
boundary correctness fails; empty-source/nonempty-target acceptance;
retained off-carrier tables; nonpattern and malformed-code rejection; actual
exactness-machine behavior; duplicate-key/default map behavior; empty-family
acceptance and nonempty-target rejection; coalescence of different singleton
carriers; a concrete accepted search bound; an ordinary covered union that
passes every frame test and rejects every exactness code; five decoded
comparison outputs; reflexive and reversed strict comparisons; and an actual
machine's reflexive five-answer tuple.

The two independent gates expand the original exactness, dependent decoder,
amalgamation and actual core-label obligations. They require actual machines,
not a supplied computability premise, and audit 37 and 99 declarations
transitively with only `propext`, `Classical.choice`, and `Quot.sound` allowed.
`compile-carlson-effective-comparison.yml` builds all proofs and controls,
checks both gates and audits the logs. GitHub CI must pass before merge.

The pure pointed presentation now has proved effective comparisons. It
still permits multiple pointed inputs for the same core element. A computable
choice of distinct representatives, an enumeration indexed by all naturals,
the actual relation Programs on that enumeration, and the final unconditional
3-1-3/3-1-2 package construction remain. This checkpoint does not construct
those packages or certify the whole unfinished library.
