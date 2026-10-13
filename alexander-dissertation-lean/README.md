# Alexander dissertation formalisation — Lean compilation

Lean 4 formalisation of Samuel Allen Alexander's dissertation
*The Theory of Several Knowing Machines* (2013), covering Questions 3-1-1,
3-1-2 and 3-1-3. This copy includes all tracked sources, the revised paper and
its PDF from the standalone Lean repository at `b06b50a`.
[Import provenance](IMPORT-PROVENANCE.json) records the original file hashes.

The existing Lean module names and theorem identifiers (such as `thesis313`)
are retained so the checked proofs and their historical records remain usable.
Historical repository URLs retain their original names. The workflows under
`.github/workflows/` are retained from the standalone repository; GitHub Actions
only discovers workflows at the outer repository root.

**Current result, 13 October 2026:** `Alexander313.thesis311`, `thesis312`
and `thesis313` have unconditional proofs at the unchanged independent comparator
types. The Carlson whole-core presentation constructs the last ordinal package;
PR 31's focused CI checked the unconditional 3-1-2/3-1-3 proofs with only
`propext`, `Classical.choice` and `Quot.sound`. The local continuation's
`Completion.lean` checks all three targets together and stronger witnesses for
Alexander's literal particular-code formula, whose existential is outside
knowledge. It uses explicit target imports and does not require the unfinished
legacy Wilken library's aggregate root to build.

The local completion and core gates passed 101 axiom reports over a 320-module
project import closure. [The checkpoint](ci/CARLSON-UNCONDITIONAL-2026-10-13.md)
records the source qualifications and reproduction commands.

The [8 October revised finite-guard paper](paper/REVISED-3-1-3-PROOF.md) is
included unchanged. The [careful section and lemma comparison](paper/LEAN-COMPARISON-2026-10-13.md)
records construction differences and the claims outside the checked scope.
`CompileRevisedPaper.lean` exposes known parameter mechanicalness, entire-theory
inheritance and literal codes along subordinate paths for the same 3-1-3
witness. The focused core-presentation workflow checks this gate alongside
the unconditional completion and core gates.

Reproduce the completion check with:

```sh
lake build +Alexander313.Thesis313Unconditional +Alexander313.PaperComparison
lake env lean Completion.lean > completion.log
python3 scripts/check_axioms.py completion.log
lake env lean CompileRevisedPaper.lean > revised-paper.log
python3 scripts/check_axioms.py revised-paper.log
```

The arithmetic template uses domains of Mathlib's concrete partial-recursive
program numbering. A separately fixed numbering or arithmetic formula would
require a translation theorem. The older sections below retain their milestone
scopes; their statements that unconditional targets are absent are superseded.

**Routine workflow (since 2026-10-09): `compile-gates.yml`.** It builds the joint import
closure of every gate file listed in `ci/gates.txt`, caches the project build products
between runs, then runs each gate with `lake env lean` and `scripts/check_axioms.py`.
`logs/gates.txt` in the artifact records PASS or FAIL per gate. The three workflows below
are now manual (`workflow_dispatch`) so that an export does not rebuild the same modules
several times; their sections describe what they check.

**Focused finite-checker workflow: `compile-carlson-finite-checks.yml`.** It
builds the uniform finite structural checkers and their kernel regressions,
then runs `CompileCarlsonFiniteChecks.lean` and the same axiom whitelist.
Carlson changes on pull requests and on `main` trigger this focused workflow.
Its scope is the imported checker development, rather than every independent
gate in the repository.

## 3-1-1 — `compile-311.yml`

The theorem is `Alexander313.thesis311 : Alexander313.Comparator.challenge311`:

> for every recursively enumerable well-founded hierarchy R there is an effective
> original-language family of knowing machines satisfying Epistemic Arithmetic, in which
> every machine knows everyone's truthfulness, particular codes of its subordinates, and
> its subordinates' mechanicalness (`Solution311` in `Alexander313/Specification.lean`).

The workflow runs:

1. `lake build +Alexander313.Thesis311Complete`, after fetching the mathlib cache;
2. `lake env lean Compile311.lean`, which checks the theorem against the independent
   `Comparator.challenge311` and prints `#print axioms Alexander313.thesis311`;
3. `scripts/check_axioms.py`, which accepts only `propext`, `Classical.choice` and
   `Quot.sound`. `sorryAx` or any project axiom fails.

A pass certifies the formal theorem and its import chain. It does not certify that
`challenge311` faithfully states the dissertation's question; that still needs an
independent comparison with the source.

## Conditional 3-1-3 — `compile-313-package.yml`

`Compile313Package.lean` checks two implications against the independent comparator targets:

```lean
Alexander313.challenge313_of_package : OrdinalPackage → Comparator.challenge313
Alexander313.challenge312_of_package : OrdinalPackage → Comparator.challenge312
```

`OrdinalPackage` (`Alexander313/OrdinalPackage.lean`) is the abstract order-2 ordinal input
of the hand proof: a coded well-ordered label domain with positively recognised order, ≤₁ and
≤₂, finite reflection, connectedness, guard room and strict ≤₂-chains of every finite length. The chain does not
import the Wilken library. A pass certifies the stage-genericity argument relative to that
interface; it does not construct an instance, so `thesis313` itself is still absent.

## Carlson pattern construction — `CompileCarlsonPatterns.lean`

The pure finite-pattern development now includes Carlson's generating-rule
calculus (Definition 13.10), finite exact generation and generation by
restriction (Definition 14.2). `GeneratingRules` defines finite derivations
from the five rule clauses and proves that every derivation has pattern
endpoints, is continuous and is cofinally valid. The finite-chain clause
retains the requirement that the restricted extension occurs at one old
point. Validity is derived, and generation preserves an existing ordinal
covering of its source. Rational downward reflection, upward reflection and minimal
lifting yield derivations in the calculus.

`GeneratingTransport` realizes a compatible isomorphism of a continuous
rule as a minimal lifting. This proves that generating rules survive
changes of labels, as in Lemma 13.11(1). `CoveringRigidity` proves the
stronger validity form of Lemma 14.6: if a structure is covered, every
covering into a valid extension sends each old point to an equal or greater
point. The proof minimizes the ordinal image of one point at a time and
uses the extension property to rule out a smaller image.

The continuous lifting construction supplies Carlson's Lemma 12.6. Given a
continuous source extension and a continuous embedding
of its base into a target pattern, it constructs a continuous minimal pattern lifting
on any supplied arithmetic carrier. Rational target labels admit such a carrier by
the existing arithmetic lifting theorem, giving an existence result without an assumed
pattern lifting. Every minimal lifting of these continuous data is continuous.

`PatternLiftingFirst` and `PatternLiftingSecond` prove the eight pattern axioms and exact
agreement with the two given patterns. `PatternLiftingConstruction` proves continuity
and minimality of the explicit candidate. `PatternLiftingNormalization` handles arbitrary
lifting maps by identifying source patterns with their images;
`PatternLiftingExistence` assembles the general and rational existence theorems.
The construction also preserves cofinal validity when the source rule has it.

The executable finite presentation is supplied by `FinitePatterns`,
`FiniteReflection`, `FiniteLifting`, `FiniteCertificates` and `FiniteRecognition`.
`PatternCode n` stores a carrier inside `Fin n` and two Boolean relation tables.
Patternhood, substructures, coverings, continuity, extension points and the
reflection hypotheses have computable decision procedures. Downward and upward
table constructions decode to exactly the existing propositional constructions.
The lifting checker verifies both actual lifting and minimality. Minimality is
decided by exhaustive enumeration of finite relation tables and total maps;
its correctness theorem identifies this finite test with the original
quantification over arbitrary propositional structures on the fixed carrier.

`RuleCertificate`, `ChainCertificate` and `GenerationCertificate` are finite
data types with executable natural-number encodings. Their total checkers
verify all rule hypotheses, chain joins and endpoint restrictions. The three
natural-number recognizers also verify the claimed source and target. Their
soundness and completeness theorems give the exact characterizations

```lean
Str.GeneratingRule P.toStr Q.toStr ↔ ∃ code, checkRule P Q code = true
Str.ExactlyGenerates P.toStr Q.toStr ↔ ∃ code, checkChain P Q code = true
Str.Generates P.toStr Q.toStr ↔ ∃ code, checkGeneration P Q code = true
```

for `P Q : PatternCode n`, under `Alexander313.Carlson.Finite`. Accepted
certificates inherit cofinal validity and, from a covered source, coveredness
and covering rigidity. Classical presentation of arbitrary predicate tables is
used only in the completeness proofs; it is absent from the executable checks.
`FiniteCertificateExamples` checks accepted and rejected instances of the rule
constructors, chain joins, restrictions, decoding and endpoint verification
using ordinary kernel reduction. The exhaustive minimality algorithm is a
reference recognizer with no practical performance guarantee for large bounds.

`FiniteRelabeling`, `FiniteFrame`, `ReflectionRelabeling`,
`LiftingRelabeling` and `GeneratingRelabeling` connect the fixed finite
calculus to ambient labels. Every rule, exact chain and generation witness
has a finite ordered frame supporting its entire derivation, including all
recursive source patterns and intermediate carriers. Changing labels on that
frame preserves both reflection constructions, continuous embeddings, actual
liftings and their universal minimality condition. Minimality is transported
by pulling each competing structure back to the original carrier and using
arithmetic uniqueness to identify the competing maps there.

`FiniteDerivationNormalization` proves soundness and completeness on any
nonempty ambient linear order, including `ℚ`. Its three
`*_iff_finite_certificate` theorems identify a rule, exact chain or generation
witness with an accepted certificate on one finite increasing grid. For
generation, the statement is

```lean
Str.Generates P Q ↔
  ∃ n : ℕ, 0 < n ∧ ∃ (labels : Fin n → α) (C D : PatternCode n) (code : ℕ),
    StrictMono labels ∧ Str.IsIso C.toStr P labels ∧
      Str.IsIso D.toStr Q labels ∧ checkGeneration C D code = true
```

Both endpoint isomorphisms use the same grid, and its order is preserved on
the entire `Fin n`, including labels used only by hidden intermediate
structures. Empty endpoint carriers are included by adding one ambient point
to the frame. Arbitrary relation values outside the carriers are handled by
identity isomorphisms. `RelabelingExamples` checks rational grids, reflection
and lifting transport, and interpretation of accepted finite codes. The
existence of a suitable frame and presentation is a classical proof; the
finite certificate checks retain their existing executable definitions.

`RationalPresentation` and `RationalRecognition` make this characterization
executable for finite rational endpoint data. A presentation stores its
finite carrier and two finite edge sets. A natural-number certificate stores
a positive grid size, every rational grid label, both finite endpoint tables,
and an encoded finite derivation. Its total checker verifies strict increase
on the entire grid, exact isomorphisms to both claimed rational endpoints,
and acceptance of the finite derivation. Failed decoding is rejected.

The three soundness and completeness theorems give, for
`P Q : RationalPresentation` in `Alexander313.Carlson.Finite`,

```lean
Str.GeneratingRule P.toStr Q.toStr ↔
  ∃ code, RationalPresentation.checkRule P Q code = true
Str.ExactlyGenerates P.toStr Q.toStr ↔
  ∃ code, RationalPresentation.checkChain P Q code = true
Str.Generates P.toStr Q.toStr ↔
  ∃ code, RationalPresentation.checkGeneration P Q code = true
```

Bounded search checks all certificate codes below a supplied bound.
Acceptance is monotone as the bound increases, and some bound accepts
exactly when the corresponding rational derivation exists. These are
executable Lean definitions and proved certificate characterizations;
no translation into the project's `Program` language is asserted.
Unsuccessful bounded search does not decide that no derivation exists.

`RationalCertificateExamples` checks valid rules, chains and generation,
negative fractional labels, empty carriers, changed endpoint data, and
off-carrier edges. It also rejects duplicate or reversed unused grid labels
even when both endpoint isomorphisms pass. The examples use ordinary kernel
reduction. Classical presentation of arbitrary propositional structures is
confined to the completeness side; the recognizers use supplied finite data.

`ComputableAnchors` supplies the first executable component of the lifting
construction. For any linear order, `Str.computableUp S x` computes the least
point of the finite carrier `S` at or above `x`, returning `x` when none exists.
The executable definition uses finite filtering and a minimum, without
requiring an inhabited ambient type. Its imported proof dependencies still
use the project's allowed axioms, including `Classical.choice`. It satisfies
the original `LeastGE` specification for bounded queries and is proved
equal to `Str.up` in all cases. The module also proves carrier membership
for bounded queries, preservation of old points, and global monotonicity.
Five small rational computations cover empty carriers, queries
below the minimum, exact old points, negative fractional queries between
anchors, and the fallback above the maximum. These use Lean kernel reduction.

`ComputableArithmeticLifting` supplies deterministic rational placement and
the complete arithmetic lifting map. It finds the greatest old target point
below an anchor, using the anchor minus one when there is no predecessor.
A positive affine map places the finite source inside that open gap. The
computed lifting preserves the given base map, uses `computableUp` for each
new point, and returns the old target union the source image. Its
`computable_rat` theorem proves the original bounded `ArithmeticLifting`
specification, including strict monotonicity and placement just below the
correct anchor. Empty carriers require no chosen point.

`ComputablePatternCandidate` maps finite rational presentations by mapping
their on-carrier edge sets. The interpreted result agrees exactly with
`Str.map`, even for a noninjective supplied map. It also computes both
normalized candidate relation tables by finite filtering and finite
existential search, using `computableUp` throughout. The result is exactly
isomorphic to `PatternLiftingConstruction.Data.candidate` on its carrier;
irrelevant off-carrier edges are discarded.

`ComputablePatternLifting` assembles these operations into
`RationalPresentation.lift P Pplus Q h`, which returns both a finite target
presentation and a total rational lifting map. Under the original source
and target pattern hypotheses, continuous source extension, and continuous
base embedding, `lift_spec` proves that the computed result is a continuous
minimal pattern lifting. Minimality quantifies over every competing pattern
and every competing map on the same carrier. It follows directly from the
candidate's forced relations and arithmetic uniqueness, without choosing
a smaller pattern or exhaustively searching for one. The module also proves
old-point agreement, the exact target cardinality, transport of extension
points, and preservation of cofinal validity. `lift_generatingRule` shows
that this computed target realizes the lifting clause of Carlson's calculus.

The constructor's definitions do not depend on proofs or on a patternhood
decision. Correctness requires the stated hypotheses; arbitrary input data
still produce a total output. Ordinary kernel computations cover multiple
anchored blocks, translated base maps, negative and fractional labels,
empty and stationary cases, exact output edge tables, all mixed relation
cases, and an incoming second-level edge whose witness must be a different
source point. Off-carrier witnesses and edges are rejected. The
`PrimitiveArithmeticLifting` and `PrimitivePatternLifting` modules below
certify these data operations in the project's `Program` language for a
primitive-recursive supplied base map. The executable fair-sequence
construction below uses the identity-base specialization.

`GeneratingSequence` constructs the union of a sequence of generating rules,
with every relation witness restricted to a finite stage carrier. It proves
exact agreement with each stage, capture of every finite subset in a later
stage, and generation of every finite induced extension of an old stage.
The union satisfies the eight pure reflection axioms and is continuous over
each stage, as in Carlson's Lemma 14.8(1–2).

`GeneratingSequenceCovering` extends any prescribed ordinal covering of any
stage to a coherent covering of the whole union. The covering preserves
order strictly and both relations forward. Coveredness of a stage therefore
implies that the union order is well-founded and isomorphic to an ordinal.
Every covering of a finite structure into the union is captured in a finite
stage; covering rigidity consequently holds in the union. These are
Lemma 14.8(3–4, 6), with the covering extension generalized to any starting
stage. They require no fairness assumption.

`FairSequence` proves that every rational pattern starts a fair sequence in
the sense of Definition 14.7. The request indexed by `Nat.pair n e` considers
finite rational table `e` as an extension of stage `n`; pairing guarantees
that the source stage already exists. A generating request is realized by a
minimal lifting along the stage inclusion, while other requests leave the
stage unchanged. Countable finite tables and identity isomorphisms handle
all off-carrier presentations. Every requested rule embeds exactly into the
union, fixing its source. The principal existence statements are

```lean
GeneratingSequence.exists_fair :
  ∀ (P : Str ℚ), P.IsPattern →
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair

GeneratingSequence.exists_fair_with_ordinal_limit :
  ∀ (P : Str ℚ), P.IsPattern → Str.Covered P →
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair ∧
      ∃ o : Ordinal, Nonempty (S.Limit ≃o Set.Iio o)
```

This existence proof in `FairSequence` is classical: testing a generating request
and choosing a lifting use classical choice. The gate includes the empty
initial carrier and checks that arbitrary off-carrier edges do not enter
the union.

`ComputableRequests` replaces the unbounded rule test with a schedule of
finite proof certificates. Each request contains a rational target
presentation and a natural-number certificate. At step `k`, `Nat.unpair k`
supplies the earlier source-stage index and the encoded request. Decoding
failure or certificate rejection leaves that request unaccepted. Every
check terminates. The soundness and completeness theorems show that every
accepted request is a generating rule and that every generating rule has
an accepted scheduled request. Completeness includes arbitrary rational
target structures through an identity isomorphism of their finite carriers.

`ComputableFairSequence` defines the complete stage data by primitive
recursion from a supplied `RationalPresentation`. An accepted certificate
triggers `RationalPresentation.lift` along the inclusion of the earlier
source into the current stage. A rejected request preserves the current
presentation exactly. No pattern proof or unbounded search contributes to
the computed data. The initial pattern hypothesis certifies that every
step is a generating rule; each accepted step is a continuous minimal
lifting. Earlier stages remain unchanged as the approximation grows.

The principal declarations, in
`Alexander313.Carlson.Finite.ComputableFairSequence`, are

```lean
stage (P : RationalPresentation) (n : ℕ) : RationalPresentation

specification (P : RationalPresentation) (hP : P.toStr.IsPattern) :
  (toGeneratingSequence P hP).stage 0 = P.toStr ∧
    (toGeneratingSequence P hP).Fair
```

Fairness has the original universal meaning: every generating rule from
every earlier stage is eventually lifted over a later stage. The schedule
enumerates target-and-certificate pairs, so one failed certificate cannot
prevent a valid certificate for the same target from being considered.
This supplies an executable Lean fair sequence with exactly the supplied
initial finite presentation. Its translation into the project's `Program`
language has not yet been proved.

`ComputableFairLimit` gives total bounded searches for membership in the
union carrier and for both union relations. Acceptance is monotone in the
stage bound and eventually occurs exactly when the corresponding union
fact holds. Relation checks require both endpoints to belong to the checked
stage, excluding off-carrier edges. Once both endpoints have appeared,
their finite-stage relation values agree with the union. A covered initial
pattern gives the computed fair sequence an exact ordinal realization
through the existing semantic theorem. That ordinal realization remains
an existence proof; it does not supply an effective ordinal label map.

`ComputableFairCarrier` presents this union by a decidable subset of natural
numbers. A code stores a rational point and its first stage of appearance.
The total validity check verifies the canonical rational encoding, membership
at the claimed stage, and absence from every earlier stage. Each point of the
union has exactly one valid code. `Label P` carries the rational order, so
neither the numerical order of codes nor the order of appearance determines
the mathematical order.

Both relation queries use the finite stage at the maximum of the two stored
birth stages. For pattern initial data and valid endpoints, that stage contains
both points and its positive and negative answers are exact for the whole
union. Invalid endpoints are rejected before they can contribute an edge.
`limitOrderIso` identifies
the entire coded order with the computed limit; `relates_labels` preserves
and reflects both relations. Covered initial data give well-foundedness and
an exact ordinal realization of this same coded structure. The decidable
subset may be empty or finite, so this does not identify it with all of
`Nat`. Formal representation of the full stage and carrier algorithms in
the project's `Program` language remains a separate obligation.

The module also proves a sufficient condition for infinitude. Any strict
first-relation edge in the initial presentation or a later stage forces
infinitely many valid labels. Fair finite reflection supplies a nonempty
initial interval below the edge's lower endpoint with no greatest point.
This uses patternhood and the sequence's proved fairness, without a
coveredness hypothesis. It supplies the infinitude input for a future
enumeration by all natural numbers when such an edge is available.

`ComputableFairCarrierExamples` checks canonical initial codes, repeated
birth claims, a malformed code whose fallback is a valid rational point,
the rational order when its codes have the reverse numerical order, and
both relation levels of a nontrivial computed lifting. Stored off-carrier
edges and invalid endpoints are rejected. Every code is proved invalid for
the empty seed, with no fixed bound on its claimed birth stage. Numeric
checks use ordinary kernel reduction.

`PrimitiveRationalData` supplies a first formal `Program` component for the
executable construction. It equips the existing rational encoding with a
`Primcodable` proof, preserving every existing code. Primitive-recursive
integer arithmetic and a bounded greatest-common-divisor computation justify
the normalized-code test, rational numerator and denominator projections,
normalization, arithmetic, and order. Addition, subtraction, multiplication,
and division have actual `Nat.Partrec.Code` implementations returning the
encoded result on paired canonical rational inputs. A separate machine
recognizes strict rational order by halting exactly when the left input is
smaller than the right. This certifies the rational arithmetic foundation;
its proofs support the finite-data and presentation codecs below.

`PrimitiveListData` certifies insertion, insertion sort, the equivalent
merge sort, membership, duplicate detection, and duplicate removal under
the existing list encoding. Sorting requires a certified comparison;
the applicable order laws justify transfer to the merge sort used by the
multiset encoder.

`PrimitiveFiniteData` adds `Primcodable` proofs for the original multiset
and finite-set encodings, with definitional equality of their underlying
`Encodable` instances. Decoding a multiset accepts any decoded list. Decoding
a finite set additionally rejects duplicates, while accepting unsorted
lists without duplicates. The all-input decoder and normalization equations
preserve that behavior: re-encoding sorts accepted lists by element codes.
Canonical list views, list conversions, membership, length, and duplicate
properties connect these encodings to primitive-recursive list operations.
The order of the canonical list is the order of element codes.

`PrimitiveFiniteOperations` certifies cardinality, filtering, image, bounded
existential and universal tests, inclusion, nonemptiness, disjointness,
union, intersection, difference, insertion, erasure, Cartesian products,
and natural ranges. The parameterized operations require primitive-recursive
proofs of their supplied maps and predicates. Concrete `Nat.Partrec.Code`
witnesses return Boolean rational membership answers, rational finite-set
unions, and strict initial-segment filters on canonical typed input codes.

`PrimitiveFiniteExtrema` certifies the ordinary finite minimum and maximum
with a supplied default used only for the empty set. The ambient comparison
must itself have a primitive-recursive certificate. Optional list extrema
fold over the existing canonical list, so the result follows the ambient
order even when that list's code order differs. The proofs identify these
computations with the original dependent `Finset.min'` and `Finset.max'`
branches, without encoding a nonemptiness proof or introducing a new
finite-set representation.

`PrimitiveRationalPresentation` certifies the original derived presentation
encoding: a constructor-tagged S-expression with three finite-set fields.
Its exact decoder equation covers every raw natural input, including wrong
tags, missing or extra fields, malformed terminators, component failures,
and accepted noncanonical finite-set codes. The new primitive coding instance
retains the original encoder and decoder definitionally. Construction,
field projections, and carrier and relation-table membership are primitive
recursive. The decoder has a total machine implementation on all natural
inputs, and membership machines return Boolean answers on canonical typed
inputs. Stored off-carrier edges remain part of the presented data.

`PrimitiveArithmeticLifting` certifies the original `computableUp`,
`computablePredBound`, `computablePlaceBelow`, `computableMap`, and
`computableTarget`. The finite carriers, anchor, query, and coded base-map
parameters remain uniform inputs. A supplied family `h : σ → ℚ → ℚ`
requires `Primrec₂ h`; an arbitrary Lean function is not treated as coded
data. Concrete machine witnesses cover anchors, predecessor bounds,
placement, and fixed-map or identity-base lifting evaluation and target
carriers. All typed inputs are covered, including empty carriers and
fallback branches. Pattern, boundedness, and monotonicity hypotheses
remain in the separate mathematical correctness theorems.

`PrimitivePatternLifting` certifies the actual presentation map, normalized
lifting candidate, lifting-map evaluation, and complete finite target.
The candidate's second relation retains the bounded search over the source
carrier. Presentation mapping accepts noninjective certified maps and
discards off-carrier source edges before taking images. Coded parameter
families can supply all presentations and the base-map evaluation jointly;
the identity specialization gives a closed target program for the three
presentations used by the fair construction. A combined theorem states
that the same target machine satisfies the existing continuous minimal
lifting specification under its separate pattern, continuity, and embedding
hypotheses. The function-valued pair returned by `lift` is represented by
separate target and map-evaluation programs.

`PrimitiveRequests` certifies the corresponding original two-field request
encoding and the existing `sourceIndex`, `decode`, `target`, and `index`
operations. Raw request decoding, scheduled decoding, target lookup, and
source-index lookup have actual machine implementations on every natural
input, including the existing empty-target fallback. Request decoding retains
every natural certificate value; deciding whether the certificate is valid
still requires a separate computability proof for `checkRule`.

`PrimitiveFiniteFunctions` certifies the original finite-function encoding
uniformly in its domain size. Its component-decoder interface also supports
size-dependent nested data, including the two dimensions of Boolean relation
tables. The original `finPi` representation tags every stored value with its
index; decoding checks those tags and re-encoding reconstructs them. Exact
decoder and normalization equations cover every natural input.
Incorrect tags, lengths, or failed component decodes are rejected; lookup returns
`none` outside the decoded domain. The size is a machine input, so these
results supply one program for all finite bounds.

`PrimitivePatternCode` extends this to the original constructor-tagged
`PatternCode n` format. A uniform primitive-recursive decoder exposes the
carrier as natural labels and both complete tables as lists of rows. It checks
carrier bounds and duplicate rejection and both table dimensions, while
retaining every off-carrier relation entry. Accepted unsorted carrier codes
are normalized by the existing finite-set encoder. The data view is lossless,
and its carrier and relation lookups agree with the original structure.
The primitive coding instance preserves the original encoder and decoder
definitionally. The main uniform machine statement has the quantifier order

```lean
∃ c : Nat.Partrec.Code, ∀ n code : ℕ,
  c.eval (Nat.pair n code) =
    Part.some (encode (Encodable.decode (α := PatternCode n) code))
```

`PrimitiveRationalCertificate` assembles the existing four-field witness
record and dependent-sum certificate codec. Its primitive coding instance
also retains the original encoding definitionally. A single total machine
decodes every raw rational certificate code, including malformed tags,
field counts, terminators, and dependent components. Primitive-recursive
projections expose the size, rational labels, source and target tables,
and stored derivation value. The whole-grid check has its own machine
certificate: it checks positive grid size and strict increase across every label,
including labels absent from both endpoint carriers.

Decoding still accepts well-formed zero-size witnesses and arbitrary natural
derivation values. `checkGrid` separately rejects size zero, duplicate labels,
and reversed labels. Endpoint isomorphism checks and the recursive finite
derivation verifier, including exhaustive minimality checking, remain before
the complete `RationalPresentation.checkRule` machine theorem. The new codec
results do not certify a derivation merely because its data decode.

`PrimitiveFiniteDataExamples` and `PrimitivePresentationExamples` check
noncanonical ordering and re-encoding, duplicate rejection, malformed
rational elements, valid empty data, record tags and field counts, malformed
terminators, stored request certificates, and the scheduler's fallback.
They combine proved normalization equations with ordinary kernel reduction
and exercise both Boolean membership answers from one certified machine.

`PrimitiveLiftingExamples` checks extrema defaults and the difference between
code order and rational order. Its machine specifications exercise empty
and nonempty extrema, translated and constant presentation maps, and both
answers to the candidate's incoming-edge search. One lifting target machine
handles varying affine coefficients and all three finite presentations,
covering a nontrivial new rational point, stationary and empty cases, and
inputs proved not to be patterns. The exact tables use kernel reduction;
their encoded machine outputs follow from the uniform representation
theorems. The complete certificate checker and fair-stage recursion still
require their own formal computability proofs.

`PrimitiveCertificateExamples` checks malformed components, dimension
mismatches, duplicate and out-of-range carrier labels, noncanonical carrier
ordering, preserved off-carrier tables, empty certificates, and the whole-grid
condition. Ordinary kernel reduction checks the data operations; uniform
machine specifications cover accepted and rejected inputs without evaluating
large literal certificate codes.

`PrimitiveEndpointIso` certifies the two endpoint isomorphism checks of
`RationalWitness.check`, uniformly in the grid size. Its data-level test
`IsoData` reads the lossless table view of a pattern code and the list of
all grid labels. It compares the labelled carrier with the claimed rational
carrier, checks strict order preservation on every carrier pair, and compares
both stored table entries with membership of the labelled edge in the claimed
edge sets. Off-carrier table entries and stored off-carrier rational edges are
never consulted. `isoData_dataView_iff` identifies this test with `Str.IsIso`
for every pattern code and labeling. `checkFrame` combines the whole-grid
check with both endpoint checks, and `witness_check_eq` splits the original
witness check into this frame and the stored finite derivation check.

The complete raw-code recognizer is then reduced to its finite part:

```lean
checkCertificate_primrec :
  Primrec (fun c : RationalCertificate =>
      finiteCheck c.1 c.2.source c.2.target c.2.derivation) →
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkCertificate finiteCheck x.1.1 x.1.2 x.2)
```

Failed decoding is included. `checkRule_primrec_of_finite`,
`checkChain_primrec_of_finite` and `checkGeneration_primrec_of_finite`
specialize this to the three rational recognizers. Their hypothesis, the
uniform primitive recursiveness of the finite derivation checkers with
exhaustive minimality checking, is not discharged here.
`PrimitiveEndpointExamples` checks acceptance, stored off-carrier edges,
a wrong target carrier, a missing on-carrier source edge, grids that fail
while both endpoint checks pass, and missing raw table entries. One certified
frame machine returns both Boolean answers.

`PrimitiveFiniteChecks` certifies agreement on a supplied finite set and
substructure checking uniformly in the ambient size. Agreement reads both
complete tables on the supplied set, including points outside either carrier;
substructure checks carrier inclusion and agreement only on the source
carrier. Its raw-code specifications cover every input, including malformed
records and accepted noncanonical finite-set encodings.

`PrimitivePatternChecks` certifies each of the eight original `IsPattern`
conditions and their conjunction. The data predicates quantify over carrier
points, pairs and triples. `patternData_dataView_iff` identifies that finite
test with the original predicate, and `checkPattern_eq` identifies the total
raw-code checker with the original decoder followed by `checkPattern`.
The single machine in `checkPattern_program` accepts both the ambient size
and the raw pattern code as inputs. Empty carriers satisfy the pattern
conditions, but malformed complete tables still reject during decoding.

`PrimitiveEmbeddingChecks` certifies finite coverings and exact
isomorphisms with independently varying source and target dimensions.
`decodeMap_eq` preserves the original position-tagged total-function codec
on every raw input; successful decoding checks the full domain length and
every output bound, including map values away from the source carrier.
The covering test requires strict order and forward preservation of both
relations on carrier pairs, with the image inside the target carrier.
The isomorphism test requires exact image equality and reflects both
relations as well. Each raw checker has a total machine, with no patternhood
hypothesis. Continuous embeddings and lifting minimality remain separate.

`PrimitiveContinuityChecks` certifies the least-old-upper-bound and
just-below predicates, correctness at both relation levels, continuity,
and extension at a specified old point. The correctness test bounds all
three universal labels by their carriers and searches for its target
witness in the old carrier; its semantic equivalence proves that these
bounds lose no instance of the original condition. Continuity also checks
substructure and the old upper-bound requirement. Extension at a point
requires at least one added point, with every added point just below the
same supplied old anchor. Raw point codes are checked against the ambient
size, and all failed pattern or point decodes reject. The original `Lvl`
type is preserved; a Boolean selects its two levels in the data tests.

The three corresponding `*ChecksExamples` modules use ordinary kernel
reduction. Their cases distinguish all independent pattern fields,
coverings from isomorphisms, strict order from collapsed maps, both relation
tables, off-carrier data, empty and unequal ambient dimensions, malformed
map tags and bounds, missing or incorrect anchors, a new maximum, and
independently failing correctness at either level. The focused gate retains
the earlier agreement/substructure regressions and audits the public
declarations of all three new proof layers.

`PrimitiveReflectionChecks` certifies all twelve downward-reflection
hypotheses and all eleven upward-reflection hypotheses. The copied block,
fresh points, placement below the old anchor, exact image and strict map
order are bounded finite tests. The upward test also checks continuity
and a nontrivial extension at the source anchor. The downward relation
level varies through the same Boolean selector used by the earlier
correctness checks. Pattern, point, finite-set and total-map decoders
retain their original behavior on every raw code. These results certify
the reflection hypotheses; primitive-recursive certificates for the
constructed downward/upward relation tables remain separate.

`PrimitiveContinuousEmbeddingChecks` forms the target restriction to the
source image without changing either complete relation table. It combines
the certified exact isomorphism onto that image with the certified
continuity of the image in the whole target. The raw checker is uniform
in the independent source and target dimensions and is equivalent to the
original `checkEmbedding`, including every failed decode.

`PrimitiveLiftingChecks` certifies all ten arithmetic lifting conditions
and all six pattern lifting fields. It checks both extended patterns,
both substructures, boundedness, strict order, landing in the target,
agreement with the base map, the exact target carrier, placement relative
to every old target point and exact agreement of both relations. The
apparently unbounded placement clause reduces to old-source anchors and
extended-source points because `JustBelow` already implies anchor
membership. Four pattern records and both entire maps are decoded with
the original codecs before testing; both dimensions vary as inputs.

`PrimitiveFiniteEnumeration` proves primitive recursiveness of finite
list products with variable lengths. It enumerates every complete pair
of Boolean relation tables on a supplied carrier and every total finite
map, re-encoding them with the original tagged codecs. Its completeness
theorems cover each original pattern code on that carrier and each
original total-map code, including all off-carrier entries.

`PrimitiveMinimalityChecks` uses those certified enumerations to check
the original fixed-carrier `PatternLifting.IsMinimal` exhaustively.
Each competitor is decoded before the certified lifting antecedent and
identity-covering conclusion are tested. Invalid competitor decodes
impose no obligation; invalid external inputs reject. Enumeration
completeness and decoder soundness prove both directions of equivalence
with the original finite minimality checker. Candidate lifting validity
remains the separate `checkLifting` condition, exactly as in the original
definition. A single primitive-recursive checker and total machine handle
both dimensions and all external natural codes, with no remaining
finite-enumeration or minimality hypothesis.

The corresponding reflection, continuous-embedding, lifting and minimality
example modules exercise the original Boolean checkers, their raw-code
boundaries and the certified machine answers. They distinguish copying
conditions, both relation levels, exact image continuity, individual
arithmetic lifting fields, fixed-carrier versus different-carrier
competitors, nonvacuous minimality and vacuous minimality, and rejection
of a candidate by an explicit competing lifting. Larger negative
minimality examples use concrete competitor witnesses; the proof does
not rely on a large exhaustive computation in the kernel. The focused
workflow compiles every new example and audits the new public declarations
alongside the previous checker results.

`ComputableFairSequenceExamples` checks scheduled certificate acceptance,
malformed encodings, wrong endpoints, and an invalid zero-size grid.
Two successive checked downward-lifting operations compute new labels
`1/5` and `9/25`, checking both complete relation tables and the updated
predecessor bound. Further regressions evaluate early recursive stages,
literal preservation after rejection, and bounded queries at both relation
levels. An empty seed is proved to have an empty carrier at every stage.
Large certificate encodings remain symbolic through their proved decoding
equations; the finite checks and computed outputs use kernel reduction.

`FairDownward` and `FairUpward` use fairness to realize the downward,
linked downward, and cofinal upward finite-copy conditions inside the
union. Their forward implications require no coveredness assumption.
`FairConverse` derives the first converse from covering rigidity;
`FairSecondConverse` proves the second converse by the two finite-stage
compression arguments of Lemma 14.8(8). `FairSemantics` combines them into
the exact intrinsic equations of Lemma 14.8(7–8): for a fair sequence with
covered stage zero,

```lean
S.limitRel .one a b ↔
  a ≤ b ∧ FirstCondition (S.limitRel .one) (S.limitRel .two) a b

S.limitRel .two a b ↔
  SecondCondition (S.limitRel .one) (S.limitRel .two) a b
```

Here `SecondCondition` includes endpoint order, linked downward copying,
and cofinal copying. `SemanticTransport` and `InitialSegmentSemantics`
transport these conditions through order isomorphisms and restrict them
to initial segments. `SemanticUniqueness` proves that the coupled
equations uniquely determine both relations on a well-founded linear
order: induction determines the first relation at an upper endpoint
before determining the second. Its ordinal specialization identifies the
relations with the actual recursively defined `R1` and `R2`.

`FairOrdinalRealization` therefore upgrades the ordinal order type to an
exact realization of the full structure. `OrdinalRealization S` contains
an ordinal bound, an order isomorphism `S.Limit ≃o Set.Iio bound`, and
equivalences between both union relations and their ordinal counterparts.
The principal existence statement is

```lean
GeneratingSequence.exists_fair_ordinalRealization :
  ∀ (P : Str ℚ), P.IsPattern → Str.Covered P →
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair ∧
      Nonempty (GeneratingSequence.OrdinalRealization S)
```

`OrdinalRealization` proves the structural consequences of Lemma 14.9
in the pure language. Every finite stage is exactly isomorphic to its
induced ordinal image. Its realized label map is pointwise least among
all ordinal coverings of that stage, so the image is isominimal. The
limit bound is the least strict ordinal bound of any fixed stage; it is
zero exactly when that stage is empty. Neither `R1` nor `R2` can leave
the realized initial segment. These statements apply to every stage,
using a common label map.

As a consequence, `GeneratingSequence.exists_minimal_ordinal_copy`
gives every covered rational pattern an exact ordinal copy whose labels
are pointwise least among all its ordinal coverings. This is a classical
existence result. The construction handles empty carriers and preserves
the given initial structure literally, including arbitrary off-carrier
relation values.

The Carlson gate compiles these declarations and audits their axioms under the same
policy as the other gates. The generating calculus is stated on a fixed ambient
linear order, including rational labels. `Tallness` now separately proves that
every finite pure pattern is covered by countable ordinals. Finite-certificate recognition extends
to executable checks of rational derivations through the common-grid characterization. The
semantic saturation and classical core-realization arguments of
Lemma 14.8(7–8) and Lemma 14.9 are now formalized. The fair sequence now
has executable Lean stage data, bounded searches for its limit facts, and
a decidable canonical-code presentation of the limit. Its rational arithmetic,
finite-container operations and extrema, presentation and request codecs,
request decoding and target selection, complete rational lifting, uniform
finite-pattern and rational-certificate codecs, whole-grid checking, and both
endpoint isomorphism checks have formal primitive-recursive certificates and
actual machine implementations. This now also includes the finite
agreement, substructure, patternhood, covering, exact isomorphism,
correctness, continuity, extension-at-a-point, reflection-hypothesis,
continuous-embedding, arithmetic/pattern-lifting and exhaustive fixed-carrier
minimality checks. `PrimitiveReflectionConstructors` now also certifies the actual
downward and upward target tables uniformly in the finite bound. Its raw algorithms
use the original decoders and target encoder on all inputs, preserve off-carrier
table behavior, and have total machine implementations. `PrimitiveSExpression`
supplies primitive-recursive tree recursion on the original derived codes.
`PrimitiveRecursiveCertificates` instantiates that recursion for the original
mutual rule and chain codecs, with exact decoding and normalization on every raw
input, unchanged primitive coding instances and uniform total machines.
The generation-record codec uses the same original component encodings.
`PrimitiveCertificateAlgebra`, `PrimitiveRecursiveChecks` and
`PrimitiveGenerationChecks` now certify the actual recursive endpoints and
Boolean checks uniformly in the finite bound. Their all-input equations use the
original derived decoders and retain complete endpoint tables even for invalid
certificates. `PrimitiveDerivationRecognition` discharges the finite checker
premises: the original rational rule, chain and generation checkers are primitive
recursive and have actual total machines. Existential machine acceptance
characterizes all three original semantic generating relations.
`UnconditionalRealization` discharges coveredness for every rational fair/minimal
realization. `Core`, `CoreIsominimal` and `CoreTallness` prove that Carlson's core
is one countable initial segment, identify it with the union of finite isominimal
ordinal substructures, and put finite guards of every rank inside it.
`OrdinalPackage.ofCarlsonCore` uses those proved guards, leaving the effective
presentation and three actual relation-recognizing Programs as inputs.

`Exactness` and `IsominimalCuts` prove exact subpattern restriction and that
1-correct initial cuts preserve isominimality, supporting later comparison
between seeds. `LeastCopyCompleteness` proves global correctness at both levels
and generation of bounded finite extensions for least ordinal copies.
`LeastCopyAgreement` proves agreement along valid rules.
`AmalgamationExistence` constructs an actual finite amalgamation of any finite
family of pure rational patterns by union of their least ordinal copies.
`ExactLeastCopyAgreement` identifies the least labels of exact embeddings.
`DenseGenerationTransport` preserves generation across the whole finite proof
support with prescribed rational endpoint labels. `GenerationCharacterization`
proves the full pure rational Theorem 14.11 and generation transitivity.
`AmalgamationUniqueness` proves compatible rational amalgamation uniqueness;
`RationalAmalgamation` supplies actual rational finite-edge existence.
`PointedPatternComparison` identifies equality, order, R1 and R2 of actual
pointed core labels with finite amalgamation comparisons.
`RationalExactness` adds a sound and complete positive certificate verifier
for original exactness, using the unchanged dependent rational generation
decoder. `PrimitiveRationalExactness` certifies every finite check and supplies
one actual total machine on all raw generation-certificate inputs.
`RationalMaps`, `PrimitiveRationalMaps` and `PrimitiveRationalIso` supply
finite table maps and primitive-recursive original isomorphism checks.
`AmalgamationCertificates` verifies the full pattern, embedding, union and
exactness obligations and proves an accepted code exists for every finite
pattern family. Its new candidate format explicitly selects the existing
vector codecs for finite functions. Historical rational and derivation codecs
are unchanged. `PrimitiveAmalgamationCertificates` certifies this actual
decoder/verifier on every raw candidate code, for each finite input dimension.
`ComputableAmalgamation` searches for the first accepted candidate;
`PartialAmalgamationSearch` supplies an actual machine that returns that same
code on every pattern-family input. `ComputablePointedComparison` and
`PartialPointedComparison` give a terminating algorithm and an actual machine
for equality, order, R1 and R2 of any two actual pointed core labels.
Representation of fair-stage algorithms in the project's `Program` language
remains.
A computed fair sequence for one seed does not yet present the whole common core:
unique representative enumeration by all natural numbers and the relation
Programs on that enumeration still need construction before
unconditional 3-1-3 can be obtained.
These results do not provide a termination bound for searching for a
derivation that may not exist.

The focused gates are `CompileCarlsonTallness.lean` (36 theorem reports),
`CompileCarlsonCore.lean` (35), `CompileCarlsonReflectionConstructors.lean` (43),
`CompileCarlsonExactness.lean` (26), `CompileCarlsonRecursiveCertificates.lean` (62),
`CompileCarlsonDerivationChecks.lean` (93), `CompileCarlsonLeastCopies.lean` (28),
`CompileCarlsonGenerationCharacterization.lean` (21),
`CompileCarlsonPointedComparison.lean` (28),
`CompileCarlsonRationalExactness.lean` (37), and
`CompileCarlsonComputableComparison.lean` (99),
with focused GitHub compilation and axiom audits. The construction
and remaining dependencies are recorded in
[the coveredness note](ci/CARLSON-TALLNESS-2026-10-12.md),
[the core note](ci/CARLSON-CORE-2026-10-12.md),
[the reflection constructor note](ci/CARLSON-CERTIFICATES-2026-10-12.md),
[the exactness note](ci/CARLSON-EXACTNESS-2026-10-12.md),
[the recursive codec frontier](ci/CARLSON-RECURSIVE-CODECS-2026-10-12.md),
[the total derivation verifiers](ci/CARLSON-DERIVATION-CHECKS-2026-10-12.md),
[the least-copy and amalgamation results](ci/CARLSON-LEAST-COPIES-2026-10-12.md),
[generation and pointed comparison](ci/CARLSON-POINTED-COMPARISON-2026-10-13.md), and
[effective exactness and comparison](ci/CARLSON-EFFECTIVE-COMPARISON-2026-10-13.md).

## Wilken library — `compile-wilken.yml`

The ordinal-notation work from Wilken's *Pure Σ₂-Elementarity beyond the Core*
(arXiv:1710.01870v5) needed for 3-1-2 and 3-1-3. The export holds every
`Alexander313/Wilken` module, every module that imports one (the `Effective` program
modules), and their import closure; `ci/wilken-targets.txt` lists the build targets. The
workflow builds them all, then runs `AuditWilken.lean`, which holds the Wilken lines of the
working package's `Audit.lean`, through the same axiom checker.

This library is unfinished, and it has no comparator challenge: no Lean proposition states
what it is meant to prove. A pass therefore means every declaration written so far
typechecks without `sorry` or project axioms. It does not mean the ordinal package is
complete.

## Contents and provenance

This repository starts from an export of a separate working package.
`SOURCE-MANIFEST.json` preserves that export's file hashes, the drift of the
3-1-1 closure from the working package's readiness manifest, and modules
exported in neither snapshot. Subsequent repository continuations, including
the Carlson sequence modules, must be carried back to the working package
before regenerating the export; the original manifest does not assert that
this transfer has occurred. `ci/*-inputs.sha256` records the current checked
inputs and changes when a target's inputs change. The routine workflow runs
on that change or on manual dispatch. Logs are uploaded as the `compile-gates-logs`, `compile-311-logs`,
`compile-313-package-logs` and `compile-wilken-logs` artifacts.

Pinned environment: Lean `v4.32.0-rc1`, mathlib `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
The proofs were written by AI systems at the repository owner's direction. No human review
is recorded.
