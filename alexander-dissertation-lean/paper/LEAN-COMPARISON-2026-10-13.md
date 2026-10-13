# Lean against the revised finite-guard paper — 13 October 2026

## Conclusion and scope

The checked Lean chain proves the main unrestricted 3-1-3 existence statement
for every recursively enumerable well-founded relation on natural-number
owners, with a single uniformly r.e., sentence-only, consequence-closed family.
Its actual knowledge interpretation is consequence membership in standard
arithmetic. Modal induction, mutual known truthfulness, literal particular-code
existentials outside knowledge, and all known mechanicalness use that same
family. No ordinal-package or source-soundness premise remains in the final
theorem.

The revision's stronger parameter mechanicalness and entire-theory inheritance
are now exposed in `Alexander313.thesis313_revised_paper` in
`Alexander313/PaperComparison.lean`. The theorem supplies one witness for these conclusions and known
literal codes for every `StrictBelow R` subordinate. Its gate independently
spells out the parameter quantifiers inside knowledge and outside the code
existential.

This is a formal proof of the main target by the finite-guard method, with
construction differences described below. It is **not a formal verification
of every assertion in the revised paper**. In particular, the exact pure
ordinal identification in §6 and the comparisons in §§18.3–18.6 are not
certified by the completion theorem. The arithmetic formula represents the
fixed `Nat.Partrec.Code` numbering. Portability to another preselected formula
or numbering requires a separate theorem.

The paper is preserved unchanged, including its stronger ordinal claims.
Its SHA-256 is
`bc012600043e35b9a415311614b31fbc9e2b61847af044fe1a3452f0a185c16a`.
The historical completion receipt and new paper-comparison receipt distinguish
their input snapshots. A passing axiom audit certifies the formal declarations;
the statement-to-paper comparison is this explicit human-readable record.

## Statement and semantic checks

| Paper requirement | Actual Lean definition or proof | Comparison |
|---|---|---|
| §1: arbitrary r.e., well-founded `j R i` | `HierarchyRE`, `WellFounded R` | Same orientation and unrestricted hypotheses; no transitivity, finite height, branching bound, downward-ideal decider or computable rank. |
| One effective family for all formulas | `EffectiveFamily.recognizes`, `recognizes_correct`, `recognizes_only_syntax`, `joint_re` | A real partial-recursive joint recognizer on encoded owner/formula pairs, not merely a chosen Lean predicate. |
| Closed theories and BL consequence closure | `MachineFamily.sentences`, `theory_closed` | Equality of membership and consequence for every closed conclusion. No closure claim for open sentences is needed. |
| Actual standard-arithmetic knowledge | `actualTruth`, `ActualRealization`, `MachineFamily.actualRealization` | `K_i φ[s]` tests the literal numerical closure in the theory; admissible weak modal structure and standard arithmetic are constructed. |
| Self-doubting EA, unrestricted modal induction | `PAInstance.induction`, `StructuralInstance`, `EAInstance`, `satisfiesEA` | Induction accepts every formula and input variable. Known arithmetic and structural axioms, introspection and reflection are included. |
| Everyone knows everyone's truthfulness | `knowsTruth`, `CommonCorePresentation.knowsTruth` | Every formula and assignment, including self and nested/modal formulas. |
| `∃e K_i ∀x(K_j φ ↔ W(e,x))` | `sourceParticularCodeSentence`, `knowsSourceParticularCodes` | Literal existential is outside knowledge; the inner code variable is closed to its witness numeral. The comparator's external witness alone was insufficient to assert literal syntax. |
| `K_i ∃e ∀x(K_j φ ↔ W(e,x))` | `mechanicalSentence`, `Solution313.all_mechanicalness` | Existential remains inside knowledge for every pair and unrestricted exactly-unary formula. |
| §18.1 parameter quantifiers inside knowledge | `parameterMechanicalSentence`, `knowsParameterMechanicalness` | Universal closure binds the remaining free parameters outside `∃e`, all inside `K_i`; all fresh code variables are allowed. No movement of quantifiers through knowledge is used. |
| §18.2 full subordinate inheritance and `R⁺` codes | `original_inherits`, `inheritsTheories.transitive`, `sourceParticularCodes.transitive` | All accepted sentences transfer along finite paths. The same witness has source codes on `StrictBelow R`. No assertion of exactness on nonedges. |

`ComparatorChallenge.lean`, `Specification.lean`, `Syntax.lean`,
`Semantics.lean` and `ArithmeticCoding.lean` are unchanged from the synchronized
online checkpoint. The new gate cannot obtain its result by weakening these
definitions.

## Section and lemma correspondence

The review read the complete revised paper and followed the key definitions,
quantifier orders and proof bodies in the completion chain. The Lean kernel
checks the entire imported dependency closure. This table names the principal
correspondence; it does not claim that every auxiliary module was independently
reviewed line by line.

| Paper location | Lean correspondence and checked point |
|---|---|
| §2.1 base logic | `Alexander/BaseLogic.lean`: free-variable independence, alpha invariance, capture-free **variable** substitution; `Valid` ranges over all nonempty arithmetic domains and admissible weak structures. `Certificate` contains actual validity of the finite implication. |
| §2.2 Assigned Validity | `BackgroundGenerator.assigned`, `ArithmeticInstances.lean`, `SourceModels.lean`: assigned instances are admitted explicitly. Numerical closure of arbitrary weak-modal validity is not assumed valid. |
| §2.3 program enumeration | `Computability.lean`, `SourceColumns.lean`, arithmetic template/finite-bounds modules: actual code evaluation, bounded computation, s-m-n, fixed point, parameter/unary columns and positive PA certificates. See numbering qualification below. |
| §§3.1–3.3 source table and fixed point | `CommonCoreAssembly.lean`, `Effective/CommonCorePrograms.lean`, `ConsequencePrograms.lean`, `SourceFixedPoint.lean`: smaller core has original-owner parameter mechanicalness only; source families are built by one joint fixed point. Source codes name the source recognizer's columns. See the core-compiler difference below. |
| §4 filtered semantics and columns | `Semantics.lean`, `SourceModels.lean`, `ColumnGenericity.lean`, `FinitePolicy.lean`: raw acceptance plus recursive body truth; per-column r.e. suffices for semantic reconstructions, with no uniform computable selector for their indices. |
| §5 direct smaller-core genericity | `CommonCorePresentation.core_genericity_columns`: uses full outside raw soundness for original owners, even on formulas containing the core; no self-mechanicalness generator is needed. |
| §6 ordinal input | `OrdinalPackage.lean`, `Carlson/Package.lean`, `CoreTallness.lean`, `ComputableCoreEnumeration.lean`, `EffectiveCorePackage.lean`: a constructed effective whole-core package with finite coverings and room. This is the substantive construction variant, not a certified identification with the paper's pure relations. |
| §7 recording and Lemma 1 | `RecordedErasure.lean`, `RecordedLogic.lean`, `RecordedLabelMaps.lean`: shape-shared tables, free variables, substitution and closure commute; pullback of arbitrary weak models proves forward validity preservation. No converse to erasure validity. |
| §8 admissions and Lemma 2 | `RecordedBackground.lean`, `RecordedMain.lean`, `FullRecordedAdmissions.lean`, effective recorded compiler modules, `RecordedStageColumns.lean`: actual generator certificates and finite consequence compiler, positive relation/edge tests, literal source code numbers. See the freshness difference below. |
| Lemma 3 source necessity | `CommonCorePresentation.necessity`: finite certificate, prefixed premises, own validity and deduction; does not use source soundness. |
| Lemma 4 erasure | `FullRecordedAdmissions.erased_member`, `erasure_of_provable`, `RecordedStage.cuts_erasure`: translates each real admission, prefixes and the actual valid implication. Padded rows erase to logical consequences of the unchanged source code sentence. |
| Lemma 5 local derived prefix | `FullRecordedPrefixes.prefix_of_certificate`, `prefix_of_provable`, `RecordedStage.cuts_prefix`: whole supports of premises and the implication lie below the prefix label; the conclusion is explicitly admissible. |
| Lemma 6 marker discharge | `RecordedStageMarkers.lean`, `main_unpadded_cuts`: own-validity proves the arithmetic markers in their cut; each guard point remains literal padded support. |
| Lemma 7 contextual cut substitution | `RecordedNumericalContexts.lean`, `RecordedStageContexts.cuts_contextual_query`: closes the context while removing substitutions at binders on the hole path; admits a literal closed contextual row. |
| Lemmas 8–9 preservation and exact collapse | `FullRecordedAdmissions.relabel`, `FiniteCertificateTransport.provable_labelCut_iff`, `RecordedStage.cuts_collapse`: reflect support of the displayed premises and conclusion; validity transport is global and needs no pattern constraints on intermediate validity-proof lines. |
| Lemma 10 legitimate stage structure | `RecordedStagePredicates.rawAlphabetic`, `filteredRealization`, `truth_close`: cut alpha invariance comes from consequence closure; live erasure and empty ghosts give a valid model before cut soundness. |
| Lemmas 11–12 contextual/background truth | `RecordedStageContexts.contextual_truth`, `RecordedStageBackground.background_truth`: indexed outer contexts use admitted cut equivalence, not an assumption that that equivalence is true. Induction uses standard-natural induction and literal substitution identities. |
| Lemma 13 coherent labels | `RecordedCoherentCollapse.cuts_record_coherent`: paired label tables, admissible pointwise minima, child-before-parent changes, explicit contextual rows; intermediate formulas need not be source-shared. |
| Lemma 14 fixed-label transport | `RecordedFixedLabelTransport.fixed_label_transport`, `fixed_label_transport_mask`: chooses each finite source certificate, places depth labels on separated guard copies above prescribed support, lifts background and code rows, prefixes, then changes the target labels coherently. Mixed-label deduction is corrected by two contextual rows in `RecordedGeneratorLifts.mixed_deduction_cuts`. |
| Lemma 15 room recovery | `RecordedStage.room_recovery`, `ExtensionStage.lift_active_exact`: proof at the guard top collapses to the copy head; quantifiers cover arbitrary closed formulas of every query shape, and nonclosed formulas are rejected. Target room/table is fixed before term variants and assignments. |
| Lemmas 16–17 reconstruction | `RecordedReconstruction.truth_reconstructed`, `StageMainRow.lift_truth`: `selectPredicates` keeps each lower-ideal predicate in full; every other branch is shape-masked cut, old external column or empty. Soundness and query agreement cover all accepted formulas, not a finite list. |
| §15 literal guards supply X | `mainGuarded_active_query`, `ExtensionStage.mainRow_truth`: guards use the rank of the live external argument, inspect nested queries, and recover every descendant query-shape class at its prescribed label. |
| Lemma 18 support soundness | `StageSupport.finite_support_soundness`, `RecordedStage.stage_sound`: separate empty-support case; local main truth gets soundness of cuts at the row's labels from strictly smaller generator support. All closed cut consequences are sound, including nonadmissible conclusions. |
| §16.1 original rank induction | `Hierarchy.nodeRank_below`, `frontierRank_strict`, `IdealGenericityInduction.idealGen_all`: semantic ordinal rank of arbitrary `R`; strict decrease is proved only for nonempty lower frontiers. Empty lower frontier uses `idealGen_empty`. |
| §16.2 finite outside reduction | `GenericityReduction.lean`, `finite_policy_genericity_reduction`: keeps core and entire ideal full, restricts outside query classes, transfers outside truth by hereditary query agreement. |
| §§16.3–16.5 whole ideal and actual family | `active_sound`, `lower_sound`, `idealGen_step`, `family_sound`: active recovery first, then full passive-ideal reconstruction, then core genericity; finally restricts actual source predicates to a finite frontier covering the theorem's owners. Outside emptiness is used without assuming actual-family soundness. |
| §§17.1–17.2 target schemas | `CommonCoreAssembly.lean`, `SourceParticularCode.lean`: prefixes produce known schemas; arithmetic coherence and consequence closure transfer the literal code-variable matrix. |
| §§17.3–17.4 inheritance/mechanicalness | `CoreInheritance.common_core_inheritance`, `inherits_core`, `PaperComparison.lean`: pads a closed theorem by `x=x`, uses its actual source column, positive computation trace, Assigned Validity and reflection. Parameter mechanicalness is inherited as a whole sentence. |
| §17.5 reduct | `OriginalReduct.lean`, `OriginalSchemas.lean`, effective owner-map modules: owner 0 is deleted, original owners shift by successor, arithmetic/code numerals stay fixed; proof closure and semantic equivalence are proved. |
| §§18.1–18.2 | Explicitly exposed by `thesis313_revised_paper`. This proves inheritance for the constructed witness, not the paper's separate claim that inheritance follows in every possible 3-1-3 solution. |
| §§18.3–18.6 | Larger-core strictness and its countermodel, additional-agent constructions and fixed theory, global-chain corollary, and the Reinhardt negative boundary are not formalized by this gate. They remain prose claims. |

## Construction differences and why the main proof still applies

1. **Ordinal structure.** Paper §6 names the true pure elementary relations
   and an isomorphism with `[0,υ₁)`, and requests two-way relation reflection.
   Lean constructs Carlson's recursively defined covering relations and their
   whole core. `FiniteLabelCovering` keeps equality and order exactly and sends
   R₁/R₂ edges forward; it does not reflect missing edges. `package_exists`
   proves the package from actual relation definitions, finite-pattern/core
   results and effective comparisons. It has no assumed relation recognizer
   or ordinal oracle. The order is the pullback of ordinal order along a proved
   duplicate-free, surjective core enumeration, not ordinary natural order.
   False Boolean comparison answers are converted to divergence, not halting
   rejection, so program **domain** recognition is exact.

   Paper Lemma 8 itself says forward preservation suffices. All transported
   generator side conditions use positive relation facts and strict nesting;
   no missing R₁/R₂ edge is required to stay missing. `relabel` and exact
   `cuts_collapse` verify this weaker contract. Tallness is inside one common
   core via minimal exact copies of every finite full-chain pattern. Room
   copies exclude the last guard endpoint and remain completely separated,
   including rank zero and empty parameter sets. Thus the package suffices for
   the main proof. The equality of this structure/core with Wilken's precise
   pure elementary structure, its named bound, and the paper's claim about
   guards in proper initial segments are not consequences of this audit.

2. **Choice of core-code compiler.** Paper §3.2 fixes a standalone compiler
   `d(φ)` for U before R is introduced. Lean builds one joint recognizer for
   the entire family and specializes its owner-0 column for core code rows,
   using `F.unaryColumnIndex 0 φ`. Consequently those numerical codes may
   depend on the chosen joint fixed point for R. The owner-0 generator table
   itself contains only background and original-owner parameter mechanicalness,
   with no subordinate code rows. Every proof uses exact core-column equations
   and preserves the selected numeral, so pre-R independence of that numeral
   is not needed for the main target. The paper's specified pre-R compiler and
   later fixed-common-theory claims should not be attributed to this Lean
   construction without an additional independence/translation result.

3. **Marker freshness.** Paper §8 excludes marker tag shapes from both source
   subshapes and all hereditary-mask argument subshapes; it permits further
   certificate exclusions. `RecordedMain` requires distinct tag indices and
   exclusion from the source sentence's subshapes only. This is a broader
   admission table. The checked proof derives each arithmetic marker directly
   by own validity and transports its displayed label, without reinterpreting
   or recording the marker through the source table. `main_source_cuts`
   constructs these bundles explicitly; all guards occur in their literal
   support. The additional paper exclusions are therefore unnecessary for
   this proof's soundness. The two admission tables are not literally equal.

4. **General stage constructors.** The generic recorded table also has a
   core-mechanical row with `A={0}`. Paper's extension stages exclude active
   owner 0. `ExtensionSides.core_active` and `ExtensionStage.zero_not_A`
   exclude that constructor in both transport and `mainRow_truth`, by an
   explicit contradiction. Actual genericity stages contain only code main
   rows, as required by the revision.

5. **Empty frontier.** Lean defines `frontierRank` by finite ordinal supremum,
   so its empty value is zero. It never claims a strict decrease to that value
   from an empty frontier. `frontierRank_strict` requires nonemptiness and
   `lift_truth` explicitly dispatches the empty lower frontier to direct core
   genericity. This implements the paper's separate empty case.

6. **Numbering and syntax.** W is the domain predicate of the pinned Mathlib
   partial-recursive code enumeration and is represented by a constructed
   arithmetic formula. Recursion, s-m-n and finite positive PA proofs are
   formalized for this choice. No theorem equates it with an arbitrary
   separately stipulated source numbering. The exact-unary condition is
   `freeVars={input}`; open parameters are addressed by the additional
   parameter schema, not silently admitted as unary formulas. Arithmetic
   terms and literals are unchanged by recording, erasure and owner reduct.

7. **Temporary raw predicates.** `ColumnAdmissible` records alphabeticity on
   closed inputs and r.e. numerical columns. It does not separately require
   arbitrary temporary predicates to reject every open input, as the paper's
   convention does. Actual modal queries always close their arguments; the
   source family and cut predicates explicitly reject open sentences. Thus
   this broader temporary interface preserves the final sentence-only result.
   The recorded model is also defined on the full head type, with allowed-head
   checks on admissions, rather than restricting its underlying language to
   allowed heads. Soundness covers every closed logical conclusion in that
   larger language.

## Reproduction and audit boundaries

```sh
lake build +Alexander313.PaperComparison +Alexander313.Thesis313Unconditional +Alexander313.Carlson.CorePresentationExamples
lake env lean CompileRevisedPaper.lean > revised-paper.log
python3 scripts/check_axioms.py revised-paper.log
lake env lean Completion.lean > completion.log
python3 scripts/check_axioms.py completion.log
lake env lean CompileCarlsonCorePresentation.lean > core-presentation.log
python3 scripts/check_axioms.py core-presentation.log
```

The focused core-presentation workflow runs all three gates. The new receipt
`ci/revised-paper-comparison-2026-10-13.json` binds the paper, imported source
closure, pins, gate files and checker to their SHA-256 digests, command results
and log digests. Only `propext`, `Classical.choice` and `Quot.sound` are accepted.
Explicit theorem parameters still matter; the final paper theorem has only
`R`, `HierarchyRE R` and `WellFounded R` as mathematical inputs.

The local final build passed with 321 imported project modules. The completion,
core-presentation and revised-paper gates passed respectively 7, 94 and 6
axiom reports: 107 total. The protected target/semantic files match the online
checkpoint byte for byte. The receipt records the precise verification time,
input digests, successful command results and log digests.

The checked scope is the imported completion/core development. The repository
also contains historical, unfinished Wilken source-tracking work. This review
does not certify a build of its aggregate library root or declare the entire
repository free of unfinished declarations.
