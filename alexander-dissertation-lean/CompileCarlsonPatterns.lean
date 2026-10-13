import Alexander313.Carlson.DownwardExistence
import Alexander313.Carlson.CoveringEnumeration
import Alexander313.Carlson.UpwardExistence
import Alexander313.Carlson.ComputableAnchors
import Alexander313.Carlson.ComputableArithmeticLifting
import Alexander313.Carlson.ComputablePatternCandidate
import Alexander313.Carlson.ComputablePatternLifting
import Alexander313.Carlson.ComputableLiftingExamples
import Alexander313.Carlson.ComputableRequests
import Alexander313.Carlson.ComputableFairSequence
import Alexander313.Carlson.ComputableFairLimit
import Alexander313.Carlson.ComputableFairSequenceExamples
import Alexander313.Carlson.ComputableFairCarrier
import Alexander313.Carlson.ComputableFairCarrierExamples
import Alexander313.Carlson.PrimitiveRationalData
import Alexander313.Carlson.PrimitiveListData
import Alexander313.Carlson.PrimitiveFiniteData
import Alexander313.Carlson.PrimitiveFiniteOperations
import Alexander313.Carlson.PrimitiveFiniteDataExamples
import Alexander313.Carlson.PrimitiveRationalPresentation
import Alexander313.Carlson.PrimitiveRequests
import Alexander313.Carlson.PrimitivePresentationExamples
import Alexander313.Carlson.PrimitiveFiniteExtrema
import Alexander313.Carlson.PrimitiveArithmeticLifting
import Alexander313.Carlson.PrimitivePatternLifting
import Alexander313.Carlson.PrimitiveLiftingExamples
import Alexander313.Carlson.PrimitiveFiniteFunctions
import Alexander313.Carlson.PrimitivePatternCode
import Alexander313.Carlson.PrimitiveRationalCertificate
import Alexander313.Carlson.PrimitiveCertificateExamples
import Alexander313.Carlson.PrimitiveEndpointIso
import Alexander313.Carlson.PrimitiveEndpointExamples
import Alexander313.Carlson.ArithmeticLiftingExistence
import Alexander313.Carlson.ArithmeticLiftingIso
import Alexander313.Carlson.PatternLifting
import Alexander313.Carlson.LiftingCofinality
import Alexander313.Carlson.PatternTransport
import Alexander313.Carlson.PatternLiftingContinuity
import Alexander313.Carlson.PatternLiftingData
import Alexander313.Carlson.PatternLiftingFirst
import Alexander313.Carlson.PatternLiftingSecond
import Alexander313.Carlson.PatternLiftingNormalization
import Alexander313.Carlson.PatternLiftingConstruction
import Alexander313.Carlson.PatternLiftingExistence
import Alexander313.Carlson.CoveringRigidity
import Alexander313.Carlson.GeneratingTransport
import Alexander313.Carlson.GeneratingRules
import Alexander313.Carlson.FinitePatterns
import Alexander313.Carlson.FiniteReflection
import Alexander313.Carlson.FiniteLifting
import Alexander313.Carlson.FiniteCertificates
import Alexander313.Carlson.FiniteRecognition
import Alexander313.Carlson.FiniteCertificateExamples
import Alexander313.Carlson.FiniteRelabeling
import Alexander313.Carlson.FiniteFrame
import Alexander313.Carlson.ReflectionRelabeling
import Alexander313.Carlson.LiftingRelabeling
import Alexander313.Carlson.GeneratingRelabeling
import Alexander313.Carlson.FiniteDerivationNormalization
import Alexander313.Carlson.RationalPresentation
import Alexander313.Carlson.RationalRecognition
import Alexander313.Carlson.RationalCertificateExamples
import Alexander313.Carlson.RelabelingExamples
import Alexander313.Carlson.GeneratingSequence
import Alexander313.Carlson.GeneratingSequenceCovering
import Alexander313.Carlson.FairSequence
import Alexander313.Carlson.ReflectionConditions
import Alexander313.Carlson.SemanticTransport
import Alexander313.Carlson.FairDownward
import Alexander313.Carlson.FairUpward
import Alexander313.Carlson.FairConverse
import Alexander313.Carlson.FairSecondConverse
import Alexander313.Carlson.FairSemantics
import Alexander313.Carlson.InitialSegmentSemantics
import Alexander313.Carlson.SemanticUniqueness
import Alexander313.Carlson.OrdinalRealization
import Alexander313.Carlson.FairOrdinalRealization

/-!
# Carlson patterns, coverings and reflection rules

Finite patterns of order two (pure case), coverings, valid and cofinally valid
rules, k-correctness, continuity and existence of downward and upward
reflections on rational labels, including preservation of cofinal validity
under upward reflection. Bounded arithmetic liftings, their rational existence
and uniqueness, and minimal pattern liftings on a fixed carrier, including
preservation of cofinal validity by a supplied minimal lifting. Transport
of continuity, old-upper-bound factorizations, normalization to image carriers,
and continuous minimal lifting existence on supplied carriers and rational labels,
including cofinal validity and transport of extension points.
Finite upper-anchor lookup is executable, globally monotone and proved equal
to the existing classical anchor operation, including its fallback cases.
Rational arithmetic placement and finite candidate tables now compute a complete
continuous minimal lifting, returning its target presentation and embedding map.
The correctness theorem compares all competing maps on the same carrier;
the computed result also realizes the generating calculus's lifting clause.
The pure generating-rule calculus, finite exact generation and generation
by restriction have derived continuity and cofinal validity. Compatible
isomorphisms preserve generating rules. Coverings of covered patterns into
valid or generated extensions cannot move old points downward.
Boolean finite pattern tables, executable reflection and lifting checks,
and natural-number certificates now recognize all five generating-rule
clauses, finite chains and generation by restriction. The recognizers are
sound and complete for derivations on each fixed finite ambient order.
Accepted certificates inherit cofinal validity and covering rigidity.
Encoded common-grid witnesses give executable, sound and complete recognition
of rational rules, chains and generation. Bounded search eventually accepts
exactly the existing derivations, with no negative decision or Program claim.
Generating-sequence unions satisfy reflection and stage continuity.
Prescribed ordinal coverings extend coherently to the union, giving an
ordinal order type and covering rigidity whenever a stage is covered.
Finite rational pattern presentations now compute fair generating sequences
by total certificate scheduling. Accepted requests are realized by a computable
minimal lifting, and rejected requests retain the current stage. Bounded
carrier and relation queries enumerate the fair union; once both endpoints
have appeared, their relation is decided by that finite stage. Covered fair
limits satisfy both intrinsic semantic equations, which determine the ordinal
relations uniquely. Exact ordinal realizations give pointwise least stage
coverings, isominimal finite images, and closure of the ordinal limit under
both relations. Canonical first-appearance codes give a decidable carrier
presentation with exact total order and relation queries. The existing
rational and finite-container encodings, arithmetic and finite operations,
presentation and request codecs, and request decoding and target selection
have primitive-recursive certificates and machine-code implementations.
Finite extrema, upper anchors, arithmetic placement and lifting maps, and
complete rational pattern-lifting targets now have uniform primitive-recursive
certificates. Supplied maps require jointly certified first-order evaluation.
The target machine realizes the continuous minimal-lifting specification
under its separate semantic hypotheses. Compilation of the full certificate
checker and stage algorithms into Program and finite tallness remain separate.
Finite-function and complete Boolean-table decoding are primitive recursive
uniformly in their domain size. The original finite-pattern and dependent
rational-certificate codecs retain their encoders and all-input decoder
behavior. Their data projections, positive grid size, and whole-grid strict-order
check have machine implementations; decoding alone does not verify a rule.
Axiom audit only; no package claim.
-/

#print axioms Alexander313.Carlson.Str.ofOrdinals_isPattern
#print axioms Alexander313.Carlson.Str.IsPattern.mono
#print axioms Alexander313.Carlson.Str.Valid.trans
#print axioms Alexander313.Carlson.Str.CofinallyValid.trans
#print axioms Alexander313.Carlson.Str.CofinallyValid.restrict
#print axioms Alexander313.Carlson.Str.Continuous.trans
#print axioms Alexander313.Carlson.Str.DownData.isPattern
#print axioms Alexander313.Carlson.Str.DownData.continuous
#print axioms Alexander313.Carlson.Str.DownData.extensionAt
#print axioms Alexander313.Carlson.Str.DownData.cofinallyValid
#print axioms Alexander313.Carlson.Str.exists_copy_justBelow_rat
#print axioms Alexander313.Carlson.Str.DownData.card_lt
#print axioms Alexander313.Carlson.Str.DownData.exists_rat
#print axioms Alexander313.Carlson.Str.exists_downward_extension_rat
#print axioms Alexander313.Carlson.Str.exists_one_point_downward_extension_rat
#print axioms Alexander313.Carlson.Str.IsCovering.coversStructure_image
#print axioms Alexander313.Carlson.Str.exists_covering_of_coversStructure
#print axioms Alexander313.Carlson.Str.coversStructure_iff
#print axioms Alexander313.Carlson.Str.exists_covering_extension_of_coversStructure
#print axioms Alexander313.Carlson.Str.CofinallyValid.cofinalCopies_at
#print axioms Alexander313.Carlson.Str.UpData.original_r₁_iff
#print axioms Alexander313.Carlson.Str.UpData.r₁_PN_below
#print axioms Alexander313.Carlson.Str.UpData.copiedBlock_isIso
#print axioms Alexander313.Carlson.Str.UpData.isPattern
#print axioms Alexander313.Carlson.Str.UpData.extensionAt
#print axioms Alexander313.Carlson.Str.UpData.continuous
#print axioms Alexander313.Carlson.Str.UpData.cofinallyValid
#print axioms Alexander313.Carlson.Str.UpData.card_universe
#print axioms Alexander313.Carlson.Str.UpData.exists_rat
#print axioms Alexander313.Carlson.Str.exists_upward_extension_rat
#print axioms Alexander313.Carlson.Str.exists_cofinally_valid_upward_extension_rat
#print axioms Alexander313.Carlson.eqOn_of_strictMonoOn_image_eq
#print axioms Alexander313.Carlson.Str.JustBelow.leastGE
#print axioms Alexander313.Carlson.Str.up_mono
#print axioms Alexander313.Carlson.Str.computableUp
#print axioms Alexander313.Carlson.Str.computableUp_spec
#print axioms Alexander313.Carlson.Str.computableUp_eq_of_leastGE
#print axioms Alexander313.Carlson.Str.computableUp_of_mem
#print axioms Alexander313.Carlson.Str.computableUp_of_not_bounded
#print axioms Alexander313.Carlson.Str.computableUp_empty
#print axioms Alexander313.Carlson.Str.computableUp_eq_up
#print axioms Alexander313.Carlson.Str.le_computableUp
#print axioms Alexander313.Carlson.Str.computableUp_mem
#print axioms Alexander313.Carlson.Str.computableUp_le_of_mem
#print axioms Alexander313.Carlson.Str.computableUp_mono
#print axioms Alexander313.Carlson.ComputableAnchorsExamples.regression_suite
#print axioms Alexander313.Carlson.ArithmeticLifting.new_not_mem
#print axioms Alexander313.Carlson.ArithmeticLifting.tail_image
#print axioms Alexander313.Carlson.ArithmeticLifting.tail_card
#print axioms Alexander313.Carlson.ArithmeticLifting.card_target
#print axioms Alexander313.Carlson.ArithmeticLifting.target_bounded
#print axioms Alexander313.Carlson.ArithmeticLifting.leastGE_image
#print axioms Alexander313.Carlson.ArithmeticLifting.up_image
#print axioms Alexander313.Carlson.ArithmeticLifting.unique
#print axioms Alexander313.Carlson.ArithmeticLifting.exists_orderIso_over
#print axioms Alexander313.Carlson.Str.exists_increasing_justBelow_rat
#print axioms Alexander313.Carlson.ArithmeticLifting.exists_rat
#print axioms Alexander313.Carlson.PatternLifting.base_relations
#print axioms Alexander313.Carlson.PatternLifting.base_covering
#print axioms Alexander313.Carlson.PatternLifting.source_covering
#print axioms Alexander313.Carlson.PatternLifting.extensionAt
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal
#print axioms Alexander313.Carlson.PatternLifting.IsMinimal.iso_of_same_carrier
#print axioms Alexander313.Carlson.Str.IsPattern.pullback
#print axioms Alexander313.Carlson.Str.IsPattern.inter
#print axioms Alexander313.Carlson.Str.interPullback_isPattern
#print axioms Alexander313.Carlson.PatternLifting.cofinallyValid
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_cofinallyValid
#print axioms Alexander313.Carlson.Str.IsPattern.rel_between
#print axioms Alexander313.Carlson.Str.Continuous.rel_up_of_rel
#print axioms Alexander313.Carlson.Str.Continuous.factor_rel_to_old
#print axioms Alexander313.Carlson.Str.Continuous.factor_rel_cross
#print axioms Alexander313.Carlson.Str.Continuous.rel_from_old_up
#print axioms Alexander313.Carlson.Str.Continuous.of_covering_id
#print axioms Alexander313.Carlson.Str.IsIso.isPattern
#print axioms Alexander313.Carlson.Str.map_isIso
#print axioms Alexander313.Carlson.Str.Continuous.of_isIso
#print axioms Alexander313.Carlson.PatternLifting.IsMinimal.continuous_of_lifting
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_continuous
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.source_target_iff
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.up_source_target
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.source_anchor_rel
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_r₁_source
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_le₁
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_refl₁
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_trans₁
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_convex₁
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_r₂_source
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_sub₂
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_refl₂
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_trans₂
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_respect₂
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_isPattern
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_source_sub
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_target_sub
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_lifting
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_r₁_up_target
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_r₂_up_target
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_continuous
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_coversInto
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_isMinimal
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.exists_continuous_minimal
#print axioms Alexander313.Carlson.PatternLiftingConstruction.Data.candidate_cofinallyValid
#print axioms Alexander313.Carlson.ArithmeticLifting.normalized
#print axioms Alexander313.Carlson.ArithmeticLifting.normalizedData
#print axioms Alexander313.Carlson.PatternLifting.exists_continuous_of_arithmetic
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_continuous_of_arithmetic
#print axioms Alexander313.Carlson.PatternLifting.IsMinimal.continuous_of_continuous_source
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_continuous_rat
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_continuous_extensionAt_rat
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_continuous_cofinallyValid_of_arithmetic
#print axioms Alexander313.Carlson.PatternLifting.exists_minimal_continuous_cofinallyValid_rat

#print axioms Alexander313.Carlson.Str.CoversInto.comp_coveringR
#print axioms Alexander313.Carlson.Str.Covered.exists_minimal_at
#print axioms Alexander313.Carlson.Str.Valid.le_of_coversInto
#print axioms Alexander313.Carlson.Str.CofinallyValid.le_of_coversInto
#print axioms Alexander313.Carlson.Str.not_valid_of_coversInto_lt
#print axioms Alexander313.Carlson.Str.IsIso.continuousEmbedding
#print axioms Alexander313.Carlson.PatternLifting.of_isIso
#print axioms Alexander313.Carlson.PatternLifting.isMinimal_of_isIso
#print axioms Alexander313.Carlson.Str.IsSub.reverse_of_same_universe
#print axioms Alexander313.Carlson.Str.Continuous.of_same_universe
#print axioms Alexander313.Carlson.Str.CofinallyValid.of_same_universe
#print axioms Alexander313.Carlson.Str.GeneratingRule.sound
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.sound
#print axioms Alexander313.Carlson.Str.GeneratingRule.continuous
#print axioms Alexander313.Carlson.Str.GeneratingRule.cofinallyValid
#print axioms Alexander313.Carlson.Str.GeneratingRule.valid
#print axioms Alexander313.Carlson.Str.GeneratingRule.refl
#print axioms Alexander313.Carlson.Str.GeneratingRule.exactlyGenerates
#print axioms Alexander313.Carlson.Str.GeneratingRule.of_isIso
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.continuous
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.cofinallyValid
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.valid
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.trans
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.generatingRule
#print axioms Alexander313.Carlson.Str.Generates.sound
#print axioms Alexander313.Carlson.Str.Generates.continuous
#print axioms Alexander313.Carlson.Str.Generates.cofinallyValid
#print axioms Alexander313.Carlson.Str.Generates.valid
#print axioms Alexander313.Carlson.Str.Generates.refl
#print axioms Alexander313.Carlson.Str.Generates.restrict
#print axioms Alexander313.Carlson.Str.Generates.generatingRule
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.generates
#print axioms Alexander313.Carlson.Str.GeneratingRule.generates
#print axioms Alexander313.Carlson.Str.Valid.covered
#print axioms Alexander313.Carlson.Str.Covered.mono
#print axioms Alexander313.Carlson.Str.GeneratingRule.covered_iff
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.covered_iff
#print axioms Alexander313.Carlson.Str.Generates.covered_iff
#print axioms Alexander313.Carlson.Str.Generates.le_of_coversInto
#print axioms Alexander313.Carlson.Str.GeneratingRule.le_of_coversInto
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.le_of_coversInto
#print axioms Alexander313.Carlson.Str.not_generates_of_coversInto_lt
#print axioms Alexander313.Carlson.Str.GeneratingRule.exists_downward_rat
#print axioms Alexander313.Carlson.Str.GeneratingRule.exists_upward_rat
#print axioms Alexander313.Carlson.Str.GeneratingRule.exists_lifting_rat

#print axioms Alexander313.Carlson.Str.isPattern_iff_conditions
#print axioms Alexander313.Carlson.Finite.PatternCode.mem_all
#print axioms Alexander313.Carlson.Finite.PatternCode.mem_patterns
#print axioms Alexander313.Carlson.Finite.PatternCode.checkPattern_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkAgree_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkSub_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkCoversInto_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkIso_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkKCorrect_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkContinuous_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkExtensionAt_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.toStr_ofDecidable
#print axioms Alexander313.Carlson.Finite.PatternCode.toStr_encode
#print axioms Alexander313.Carlson.Finite.PatternCode.encode_toStr
#print axioms Alexander313.Carlson.Finite.PatternCode.toStr_injective
#print axioms Alexander313.Carlson.Finite.finiteBack_eq_back
#print axioms Alexander313.Carlson.Finite.PatternCode.toStr_downward
#print axioms Alexander313.Carlson.Finite.PatternCode.toStr_upward
#print axioms Alexander313.Carlson.Finite.PatternCode.checkDownward_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkUpward_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.downward_isPattern_of_check
#print axioms Alexander313.Carlson.Finite.PatternCode.upward_isPattern_of_check
#print axioms Alexander313.Carlson.ArithmeticLifting.iff_conditions
#print axioms Alexander313.Carlson.PatternLifting.iff_conditions
#print axioms Alexander313.Carlson.Finite.PatternCode.minimalCriterion_iff
#print axioms Alexander313.Carlson.Finite.PatternCode.checkLifting_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkEmbedding_eq_true
#print axioms Alexander313.Carlson.Finite.PatternCode.checkMinimal_eq_true
#print axioms Alexander313.Carlson.Finite.RuleCertificate.sound
#print axioms Alexander313.Carlson.Finite.RuleCertificate.complete
#print axioms Alexander313.Carlson.Finite.ChainCertificate.sound
#print axioms Alexander313.Carlson.Finite.ChainCertificate.complete
#print axioms Alexander313.Carlson.Finite.GenerationCertificate.sound
#print axioms Alexander313.Carlson.Finite.GenerationCertificate.complete
#print axioms Alexander313.Carlson.Finite.checkRule_eq_true
#print axioms Alexander313.Carlson.Finite.checkRule_sound
#print axioms Alexander313.Carlson.Finite.checkRule_complete
#print axioms Alexander313.Carlson.Finite.generatingRule_iff_exists_code
#print axioms Alexander313.Carlson.Finite.checkChain_eq_true
#print axioms Alexander313.Carlson.Finite.checkChain_sound
#print axioms Alexander313.Carlson.Finite.checkChain_complete
#print axioms Alexander313.Carlson.Finite.exactlyGenerates_iff_exists_code
#print axioms Alexander313.Carlson.Finite.checkGeneration_eq_true
#print axioms Alexander313.Carlson.Finite.checkGeneration_sound
#print axioms Alexander313.Carlson.Finite.checkGeneration_complete
#print axioms Alexander313.Carlson.Finite.generates_iff_exists_code
#print axioms Alexander313.Carlson.Finite.checkRule_cofinallyValid
#print axioms Alexander313.Carlson.Finite.checkChain_cofinallyValid
#print axioms Alexander313.Carlson.Finite.checkGeneration_cofinallyValid
#print axioms Alexander313.Carlson.Finite.checkGeneration_covered
#print axioms Alexander313.Carlson.Finite.checkGeneration_le_of_coversInto
#print axioms Alexander313.Carlson.Finite.CertificateExamples.regression_suite
#print axioms Alexander313.Carlson.Finite.CertificateExamples.checked_downward_is_generating_rule
#print axioms Alexander313.Carlson.Finite.CertificateExamples.checked_chain_exactly_generates
#print axioms Alexander313.Carlson.Finite.CertificateExamples.checked_restriction_generates

#print axioms Alexander313.Carlson.FiniteRelabeling.inverse_isIso
#print axioms Alexander313.Carlson.FiniteRelabeling.justBelow_iff
#print axioms Alexander313.Carlson.FiniteRelabeling.extensionAt
#print axioms Alexander313.Carlson.FiniteRelabeling.toFin
#print axioms Alexander313.Carlson.FiniteRelabeling.toFinOfNonempty
#print axioms Alexander313.Carlson.FiniteRelabeling.toFinOfNonempty_image_univ
#print axioms Alexander313.Carlson.Str.exists_finite_code
#print axioms Alexander313.Carlson.FiniteRelabeling.downwardData
#print axioms Alexander313.Carlson.FiniteRelabeling.downward_isIso
#print axioms Alexander313.Carlson.FiniteRelabeling.upwardData
#print axioms Alexander313.Carlson.FiniteRelabeling.upward_isIso
#print axioms Alexander313.Carlson.FiniteRelabeling.arithmeticLifting
#print axioms Alexander313.Carlson.FiniteRelabeling.patternLifting
#print axioms Alexander313.Carlson.FiniteRelabeling.continuousEmbedding
#print axioms Alexander313.Carlson.FiniteRelabeling.isMinimal
#print axioms Alexander313.Carlson.Str.GeneratingRule.exists_relabeling_support
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.exists_relabeling_support
#print axioms Alexander313.Carlson.Str.Generates.exists_relabeling_support
#print axioms Alexander313.Carlson.Str.GeneratingRule.map_of_strictMono
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.map_of_strictMono
#print axioms Alexander313.Carlson.Str.Generates.map_of_strictMono
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.of_identity_isos
#print axioms Alexander313.Carlson.Str.Generates.of_identity_isos
#print axioms Alexander313.Carlson.Finite.checkRule_sound_of_labels
#print axioms Alexander313.Carlson.Finite.checkChain_sound_of_labels
#print axioms Alexander313.Carlson.Finite.checkGeneration_sound_of_labels
#print axioms Alexander313.Carlson.Finite.generatingRule_finite_complete
#print axioms Alexander313.Carlson.Finite.exactlyGenerates_finite_complete
#print axioms Alexander313.Carlson.Finite.generates_finite_complete
#print axioms Alexander313.Carlson.Finite.generatingRule_iff_finite_certificate
#print axioms Alexander313.Carlson.Finite.exactlyGenerates_iff_finite_certificate
#print axioms Alexander313.Carlson.Finite.generates_iff_finite_certificate
#print axioms Alexander313.Carlson.RelabelingExamples.rational_normalization
#print axioms Alexander313.Carlson.RelabelingExamples.empty_frame
#print axioms Alexander313.Carlson.RelabelingExamples.exact_frame
#print axioms Alexander313.Carlson.RelabelingExamples.rational_downward_data
#print axioms Alexander313.Carlson.RelabelingExamples.rational_upward_data
#print axioms Alexander313.Carlson.RelabelingExamples.rational_downward_isIso
#print axioms Alexander313.Carlson.RelabelingExamples.rational_upward_isIso
#print axioms Alexander313.Carlson.RelabelingExamples.rational_lower_copy_agrees
#print axioms Alexander313.Carlson.RelabelingExamples.off_carrier_tables
#print axioms Alexander313.Carlson.RelabelingExamples.rational_minimal_lifting
#print axioms Alexander313.Carlson.RelabelingExamples.rational_checked_downward_rule
#print axioms Alexander313.Carlson.RelabelingExamples.rational_generation_by_certificate

#print axioms Alexander313.Carlson.Str.Continuous.inclusionEmbedding
#print axioms Alexander313.Carlson.GeneratingSequence.exactlyGenerates
#print axioms Alexander313.Carlson.GeneratingSequence.finite_capture
#print axioms Alexander313.Carlson.GeneratingSequence.rel_iff
#print axioms Alexander313.Carlson.GeneratingSequence.restrict_pattern
#print axioms Alexander313.Carlson.GeneratingSequence.generates_restrict
#print axioms Alexander313.Carlson.GeneratingSequence.continuous_restrict
#print axioms Alexander313.Carlson.GeneratingSequence.bounded
#print axioms Alexander313.Carlson.GeneratingSequence.kCorrect
#print axioms Alexander313.Carlson.GeneratingSequence.rel_le
#print axioms Alexander313.Carlson.GeneratingSequence.rel_two_one
#print axioms Alexander313.Carlson.GeneratingSequence.rel_refl
#print axioms Alexander313.Carlson.GeneratingSequence.rel_trans
#print axioms Alexander313.Carlson.GeneratingSequence.rel_convex_one
#print axioms Alexander313.Carlson.GeneratingSequence.rel_respect_two
#print axioms Alexander313.Carlson.GeneratingSequence.CoveringThread.extend
#print axioms Alexander313.Carlson.GeneratingSequence.CoveringThread.map_eq
#print axioms Alexander313.Carlson.GeneratingSequence.CoveringThread.limitMap_eq
#print axioms Alexander313.Carlson.GeneratingSequence.CoveringThread.strictMono
#print axioms Alexander313.Carlson.GeneratingSequence.CoveringThread.preserves_one
#print axioms Alexander313.Carlson.GeneratingSequence.CoveringThread.preserves_two
#print axioms Alexander313.Carlson.GeneratingSequence.exists_limitCovering_extension
#print axioms Alexander313.Carlson.GeneratingSequence.wellFounded
#print axioms Alexander313.Carlson.GeneratingSequence.exists_ordinal_orderIso
#print axioms Alexander313.Carlson.GeneratingSequence.CoversIntoLimit.exists_stage
#print axioms Alexander313.Carlson.GeneratingSequence.le_of_coversIntoLimit
#print axioms Alexander313.Carlson.PatternLifting.of_source_identity_iso
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.realizes
#print axioms Alexander313.Carlson.GeneratingSequence.exists_fair
#print axioms Alexander313.Carlson.GeneratingSequence.exists_fair_with_ordinal_limit

-- ReflectionConditions
#print axioms Alexander313.Carlson.SecondCondition.firstCondition
#print axioms Alexander313.Carlson.FirstCondition.cofinalCopies
#print axioms Alexander313.Carlson.CofinalCopies.of_firstCondition
#print axioms Alexander313.Carlson.CofinalCondition.restrict_right
#print axioms Alexander313.Carlson.LinkedCondition.restrict_right
#print axioms Alexander313.Carlson.SecondCondition.respects_first
#print axioms Alexander313.Carlson.R1_iff_firstCondition
#print axioms Alexander313.Carlson.R2_iff_secondCondition

-- SemanticTransport
#print axioms Alexander313.Carlson.CoversStructure.image
#print axioms Alexander313.Carlson.coversStructure_image_iff
#print axioms Alexander313.Carlson.coversStructure_subtype_val_iff
#print axioms Alexander313.Carlson.Str.IsIso.exists_inverse
#print axioms Alexander313.Carlson.coversStructure_orderIso_iff
#print axioms Alexander313.Carlson.coversStructure_subtype_iff
#print axioms Alexander313.Carlson.CoveringCopy.orderIso
#print axioms Alexander313.Carlson.coveringCopy_orderIso_iff
#print axioms Alexander313.Carlson.FirstCondition.orderIso
#print axioms Alexander313.Carlson.firstCondition_orderIso_iff
#print axioms Alexander313.Carlson.LinkedCondition.orderIso
#print axioms Alexander313.Carlson.linkedCondition_orderIso_iff
#print axioms Alexander313.Carlson.CofinalCopies.orderIso
#print axioms Alexander313.Carlson.cofinalCopies_orderIso_iff
#print axioms Alexander313.Carlson.CofinalCondition.orderIso
#print axioms Alexander313.Carlson.cofinalCondition_orderIso_iff

-- FairDownward
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.exists_downward_copy
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.exists_limit_copy
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.firstCondition
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.linkedCondition

-- FairUpward
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.transfer_copy
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.cofinalCondition

-- FairConverse
#print axioms Alexander313.Carlson.GeneratingSequence.le_of_stage_limitCovering
#print axioms Alexander313.Carlson.GeneratingSequence.firstCondition_rel_one

-- FairSecondConverse
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.secondCondition_rel_two

-- FairSemantics
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.rel_one_iff
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.secondCondition
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.rel_two_iff

-- InitialSegmentSemantics
#print axioms Alexander313.Carlson.CoveringCopy.exists_Iio_lift
#print axioms Alexander313.Carlson.CoveringCopy.exists_Iio_extension
#print axioms Alexander313.Carlson.linkedCondition_Iio_iff
#print axioms Alexander313.Carlson.firstCondition_Iio_iff
#print axioms Alexander313.Carlson.cofinalCopies_Iio_iff
#print axioms Alexander313.Carlson.cofinalCondition_Iio_iff
#print axioms Alexander313.Carlson.secondCondition_Iio_iff
#print axioms Alexander313.Carlson.R1_Iio_iff_firstCondition
#print axioms Alexander313.Carlson.R2_Iio_iff_secondCondition

-- SemanticUniqueness
#print axioms Alexander313.Carlson.CoveringCopy.congr_below
#print axioms Alexander313.Carlson.firstCondition_congr_below
#print axioms Alexander313.Carlson.linkedCondition_congr_below
#print axioms Alexander313.Carlson.cofinalCopies_congr_below
#print axioms Alexander313.Carlson.cofinalCondition_congr_below
#print axioms Alexander313.Carlson.semantic_equations_unique
#print axioms Alexander313.Carlson.ordinalRelations_unique

-- OrdinalRealization
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.label_eq
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.toOrdinal_strictMono
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.toOrdinal_lt_bound
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.label_lt_bound
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.toOrdinal_le_of_strictMono
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_isIso
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_covering
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.label_le_covering
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_le_covering
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_isominimal
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.bound_le_iff
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.bound_eq_zero_iff
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.lt_bound_of_R1
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.lt_bound_of_R2

-- FairOrdinalRealization
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.semanticEquations_orderIso
#print axioms Alexander313.Carlson.GeneratingSequence.Fair.ordinalRealization
#print axioms Alexander313.Carlson.GeneratingSequence.exists_fair_ordinalRealization
#print axioms Alexander313.Carlson.GeneratingSequence.exists_minimal_ordinal_copy

namespace Alexander313.Carlson.SequenceExamples

/-- Off-carrier predicates are deliberately unrestricted. -/
private def emptyWild : Str ℚ := ⟨∅, fun _ _ => True, fun _ _ => True⟩

private theorem emptyWild_pattern : emptyWild.IsPattern := by
  constructor <;> simp [emptyWild]

private def emptySequence : GeneratingSequence ℚ :=
  GeneratingSequence.constant emptyWild emptyWild_pattern

/-- Arbitrary off-carrier edges must not leak into a union relation. -/
theorem off_carrier_edges_excluded :
    ¬ emptySequence.rel .one 0 0 ∧ ¬ emptySequence.rel .two 0 0 := by
  have h (k : Lvl) : ¬ emptySequence.rel k 0 0 := by
    rintro ⟨_, hx, _, _⟩
    exact Finset.notMem_empty (0 : ℚ) hx
  exact ⟨h .one, h .two⟩

/-- Fair existence includes the empty carrier with its exact presentation. -/
theorem empty_fair_start :
    ∃ S : GeneratingSequence ℚ, S.stage 0 = emptyWild ∧ S.Fair :=
  GeneratingSequence.exists_fair emptyWild emptyWild_pattern

/-- Exact ordinal realization includes the empty carrier, preserves its
off-carrier presentation, and has ordinal bound zero. -/
theorem empty_fair_ordinalRealization :
    ∃ (S : GeneratingSequence ℚ) (R : GeneratingSequence.OrdinalRealization S),
      S.stage 0 = emptyWild ∧ S.Fair ∧ R.bound = 0 := by
  have hcov : Str.Covered emptyWild := by
    refine ⟨fun _ => 0, ?_⟩
    simp [Str.CoveringR, Str.IsCovering, emptyWild]
  obtain ⟨S, hzero, hfair, ⟨R⟩⟩ :=
    GeneratingSequence.exists_fair_ordinalRealization emptyWild emptyWild_pattern hcov
  refine ⟨S, R, hzero, hfair, (R.bound_eq_zero_iff 0).mpr ?_⟩
  rw [hzero]
  rfl

end Alexander313.Carlson.SequenceExamples

#print axioms Alexander313.Carlson.SequenceExamples.off_carrier_edges_excluded
#print axioms Alexander313.Carlson.SequenceExamples.empty_fair_start
#print axioms Alexander313.Carlson.SequenceExamples.empty_fair_ordinalRealization

-- Executable rational presentations, certificate recognition and bounded search.
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr
#print axioms Alexander313.Carlson.Finite.RationalPresentation.ofDecidable
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr_ofDecidable_r₁
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr_ofDecidable_r₂
#print axioms Alexander313.Carlson.Finite.RationalPresentation.ofDecidable_iso
#print axioms Alexander313.Carlson.Finite.RationalPresentation.presentation_iso
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkIso
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkIso_eq_true
#print axioms Alexander313.Carlson.Finite.RationalWitness.check
#print axioms Alexander313.Carlson.Finite.RationalWitness.check_eq_true
#print axioms Alexander313.Carlson.Finite.acceptsBelow
#print axioms Alexander313.Carlson.Finite.acceptsBelow_eq_true
#print axioms Alexander313.Carlson.Finite.acceptsBelow_mono
#print axioms Alexander313.Carlson.Finite.exists_acceptsBelow_iff
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkCertificate
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkCertificate_eq_true
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkCertificate_encode
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkRule
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkRule_sound
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkRule_complete
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkChain
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkChain_sound
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkChain_complete
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkGeneration
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkGeneration_sound
#print axioms Alexander313.Carlson.Finite.RationalPresentation.checkGeneration_complete
#print axioms Alexander313.Carlson.Finite.RationalPresentation.generatingRule_iff_exists_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.generatingRule_iff_encoded_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.generatingRule_iff_eventually_accepts
#print axioms Alexander313.Carlson.Finite.RationalPresentation.exactlyGenerates_iff_exists_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.exactlyGenerates_iff_encoded_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.exactlyGenerates_iff_eventually_accepts
#print axioms Alexander313.Carlson.Finite.RationalPresentation.generates_iff_exists_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.generates_iff_encoded_code
#print axioms Alexander313.Carlson.Finite.RationalPresentation.generates_iff_eventually_accepts
#print axioms Alexander313.Carlson.Finite.RationalCertificateExamples.rational_nat_roundtrip
#print axioms Alexander313.Carlson.Finite.RationalCertificateExamples.regression_suite

-- Executable rational lifting: data, specifications, and kernel computations.
#print axioms Alexander313.Carlson.Str.computablePredBound
#print axioms Alexander313.Carlson.Str.computablePredBound_spec
#print axioms Alexander313.Carlson.Str.computablePlaceBelow
#print axioms Alexander313.Carlson.Str.computablePlaceBelow_empty
#print axioms Alexander313.Carlson.Str.computablePlaceBelow_spec
#print axioms Alexander313.Carlson.ArithmeticLifting.computableMap
#print axioms Alexander313.Carlson.ArithmeticLifting.computableTarget
#print axioms Alexander313.Carlson.ArithmeticLifting.computableMap_of_mem
#print axioms Alexander313.Carlson.ArithmeticLifting.computableMap_of_not_mem
#print axioms Alexander313.Carlson.ArithmeticLifting.computable_rat
#print axioms Alexander313.Carlson.ComputableArithmeticLiftingExamples.two_block_regression
#print axioms Alexander313.Carlson.ComputableArithmeticLiftingExamples.boundary_regression
#print axioms Alexander313.Carlson.Finite.RationalPresentation.map
#print axioms Alexander313.Carlson.Finite.RationalPresentation.map_U
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr_map_r₁
#print axioms Alexander313.Carlson.Finite.RationalPresentation.toStr_map_r₂
#print axioms Alexander313.Carlson.Finite.RationalPresentation.map_toStr
#print axioms Alexander313.Carlson.Finite.RationalPresentation.map_isIso
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftingCandidate
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftingCandidate_U
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftingCandidate_r₁
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftingCandidate_r₂
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftingCandidate_iso
#print axioms Alexander313.Carlson.ComputablePatternCandidateExamples.map_regression_suite
#print axioms Alexander313.Carlson.ComputablePatternCandidateExamples.candidate_regression_suite
#print axioms Alexander313.Carlson.ComputablePatternCandidateExamples.incoming_search_regression
#print axioms Alexander313.Carlson.ComputablePatternCandidateExamples.empty_regression_suite
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftMap
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftTarget
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift
#print axioms Alexander313.Carlson.Finite.RationalPresentation.liftTarget_U
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift_spec
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift_agrees
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift_card
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift_extensionAt
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift_cofinallyValid
#print axioms Alexander313.Carlson.Finite.RationalPresentation.lift_generatingRule
#print axioms Alexander313.Carlson.Finite.ComputableLiftingExamples.end_to_end_regression
#print axioms Alexander313.Carlson.Finite.ComputableLiftingExamples.stationary_regression
#print axioms Alexander313.Carlson.Finite.ComputableLiftingExamples.empty_regression

-- Executable request scheduling: finite data, acceptance, and completeness.
#print axioms Alexander313.Carlson.Finite.ComputableRequests.sourceIndex
#print axioms Alexander313.Carlson.Finite.ComputableRequests.decode
#print axioms Alexander313.Carlson.Finite.ComputableRequests.target
#print axioms Alexander313.Carlson.Finite.ComputableRequests.check
#print axioms Alexander313.Carlson.Finite.ComputableRequests.index
#print axioms Alexander313.Carlson.Finite.ComputableRequests.sourceIndex_le
#print axioms Alexander313.Carlson.Finite.ComputableRequests.sourceIndex_index
#print axioms Alexander313.Carlson.Finite.ComputableRequests.decode_index
#print axioms Alexander313.Carlson.Finite.ComputableRequests.target_index
#print axioms Alexander313.Carlson.Finite.ComputableRequests.check_index
#print axioms Alexander313.Carlson.Finite.ComputableRequests.check_of_decode_none
#print axioms Alexander313.Carlson.Finite.ComputableRequests.check_of_decode_some
#print axioms Alexander313.Carlson.Finite.ComputableRequests.check_eq_true
#print axioms Alexander313.Carlson.Finite.ComputableRequests.check_sound
#print axioms Alexander313.Carlson.Finite.ComputableRequests.complete_presentation
#print axioms Alexander313.Carlson.Finite.ComputableRequests.complete

-- Executable stage data, generating steps, minimal lifting, and fairness.
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.next
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.next_of_check
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.next_of_reject
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.next_spec
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.next_rule
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.approximation
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.approximation_zero
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.approximation_succ_agrees
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.approximation_agrees
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.approximation_step
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.stage
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.stage_zero
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.stage_agrees
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.stage_succ
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.stage_step
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.toGeneratingSequence
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.toGeneratingSequence_stage
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.toGeneratingSequence_zero
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.stage_lifting
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.fair
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.specification

-- Total bounded searches in the computed fair limit and exact relation answers.
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.containsBelow
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.containsBelow_zero
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow_zero
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.containsBelow_eq_true
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow_eq_true
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.containsBelow_mono
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow_mono
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.mem_limit_iff_eventually_contains
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.limit_rel_iff_eventually_relates
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.containsBelow_succ_iff
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow_succ_iff
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow_iff_limit_of_captured
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.relatesBelow_iff_stage_of_captured
#print axioms Alexander313.Carlson.Finite.ComputableFairSequence.ordinalRealization

-- Kernel regressions for scheduled requests, recursive stages, and finite searches.
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.scheduled_request_roundtrip
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.malformed_request_preserves
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.two_transition_rules
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.two_lifts_compute
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.early_stage_regression
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.bounded_query_regression
#print axioms Alexander313.Carlson.Finite.ComputableFairSequenceExamples.regression_suite

-- Canonical first-appearance codes and exact finite relation queries.
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.birthStage
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.value
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.encode
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.birthStage_encode
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.value_encode
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.valid
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.valid_eq_true
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.mem_birthStage
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.not_mem_before
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.birthStage_le
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.value_injective
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.firstCode
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.value_firstCode
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.valid_firstCode
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.mem_limit_iff_existsUnique
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.Label.value_injective
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.Label.instLinearOrder
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.toLimit
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.ofLimit
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.toLimit_ofLimit
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.ofLimit_toLimit
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.limitOrderIso
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.less
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.less_eq_true
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.less_labels
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.relates
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.relates_eq_true_iff_stage
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.mem_commonStage
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.relates_eq_true
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.relates_labels
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.wellFounded
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.exists_ordinalRealization

-- Kernel regressions for coded carriers, ordering, relations and empty limits.
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.first_appearance_regression
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.rational_order_regression
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.relation_regression
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.invalid_code_regression
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.empty_rejects_all
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.empty_no_label
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.label_order_regression

-- Primitive-recursive rational codes and actual arithmetic machine programs.
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_ofNat
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_negSucc
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_casesOn
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_natAbs
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_negOfNat
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_neg
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_subNatNat
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_add
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_sub
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_mul
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_nonneg
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_le
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_lt
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_sign
#print axioms Alexander313.Carlson.PrimitiveRationalData.int_edivNat
#print axioms Alexander313.Carlson.PrimitiveRationalData.nat_dvd
#print axioms Alexander313.Carlson.PrimitiveRationalData.nat_gcd
#print axioms Alexander313.Carlson.PrimitiveRationalData.nat_coprime
#print axioms Alexander313.Carlson.PrimitiveRationalData.rationalEncodable
#print axioms Alexander313.Carlson.PrimitiveRationalData.encode_rat
#print axioms Alexander313.Carlson.PrimitiveRationalData.validCode
#print axioms Alexander313.Carlson.PrimitiveRationalData.validCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalData.encode_decode_rat
#print axioms Alexander313.Carlson.PrimitiveRationalData.instPrimcodableRat
#print axioms Alexander313.Carlson.PrimitiveRationalData.rational_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_num
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_den
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_of_components
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_mkRat
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_neg
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_add
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_sub
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_mul
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_inv
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_div
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_le
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_lt
#print axioms Alexander313.Carlson.PrimitiveRationalData.exists_code
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_add_program
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_sub_program
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_mul_program
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_div_program
#print axioms Alexander313.Carlson.PrimitiveRationalData.rat_lt_program

-- Carrier convenience equations, infinitude, and full-limit regressions.
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.valid_encode_zero
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.limitOrderIso_apply
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.infinite_of_stage_first
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrier.infinite_of_initial_first
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.first_pattern
#print axioms Alexander313.Carlson.Finite.ComputableFairCarrierExamples.limit_answers_regression

-- PrimitiveListData: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitiveListData.orderedInsert
#print axioms Alexander313.Carlson.PrimitiveListData.insertionSort
#print axioms Alexander313.Carlson.PrimitiveListData.mergeSort
#print axioms Alexander313.Carlson.PrimitiveListData.list_mem
#print axioms Alexander313.Carlson.PrimitiveListData.list_nodup
#print axioms Alexander313.Carlson.PrimitiveListData.list_dedup

-- PrimitiveFiniteData: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitiveFiniteData.codeLE
#print axioms Alexander313.Carlson.PrimitiveFiniteData.codeLE_decidable
#print axioms Alexander313.Carlson.PrimitiveFiniteData.codeLE_isLinearOrder
#print axioms Alexander313.Carlson.PrimitiveFiniteData.codeLE_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteData.sortCodes
#print axioms Alexander313.Carlson.PrimitiveFiniteData.sortCodes_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteData.multisetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.multisetView_coe
#print axioms Alexander313.Carlson.PrimitiveFiniteData.coe_multisetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.mem_multisetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.length_multisetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.multisetEncodable
#print axioms Alexander313.Carlson.PrimitiveFiniteData.encode_multiset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.decode_multiset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.encode_decode_multiset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.instPrimcodableMultiset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.multiset_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveFiniteData.decode_encode_multisetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.multisetView_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteData.list_toMultiset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.multiset_nodup
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetEquiv
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetEncodable
#print axioms Alexander313.Carlson.PrimitiveFiniteData.instPrimcodableFinset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finset_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.encode_finset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finset_val
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetView_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteData.mem_finsetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.length_finsetView
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetView_nodup
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetView_toFinset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finsetView_ofList
#print axioms Alexander313.Carlson.PrimitiveFiniteData.list_toFinset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.finset_mem
#print axioms Alexander313.Carlson.PrimitiveFiniteData.decode_finset
#print axioms Alexander313.Carlson.PrimitiveFiniteData.decode_finset_encode_list
#print axioms Alexander313.Carlson.PrimitiveFiniteData.encode_decode_finset

-- PrimitiveFiniteOperations: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_card
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_filter
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_image
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.exists_mem
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.forall_mem
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_subset
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_nonempty
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_disjoint
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_union
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_inter
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_sdiff
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_insert
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_erase
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_product
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.finset_range
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.exists_program
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.rational_membership_program
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.rational_union_program
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.rational_below
#print axioms Alexander313.Carlson.PrimitiveFiniteOperations.rational_below_program

-- PrimitiveFiniteDataExamples: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.rational_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.unsorted_code_regression
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.duplicate_code_regression
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.malformed_element_regression
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.encoded_order_regression
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.sample
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.finite_operations_regression
#print axioms Alexander313.Carlson.PrimitiveFiniteDataExamples.membership_answers

-- PrimitiveRationalPresentation: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.Fields
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.ofFields
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.packCode
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.encode_presentation
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeField
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeFields
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeData
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decode_presentation
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.packCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeField_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeData_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.encoded_ofFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.encoded_decode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.instPrimcodableRationalPresentation
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.presentation_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.ofFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.mk_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.decodeData_encode_presentation
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.fields_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.carrier_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.relation₁_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.relation₂_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.carrier_mem
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.relation₁_mem
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.relation₂_mem
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.exists_code
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.presentation_decode_program
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.carrier_mem_program
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.relation₁_mem_program
#print axioms Alexander313.Carlson.PrimitiveRationalPresentation.relation₂_mem_program

-- PrimitiveRequests: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitiveRequests.packCode
#print axioms Alexander313.Carlson.PrimitiveRequests.encode_request
#print axioms Alexander313.Carlson.PrimitiveRequests.decodeFields
#print axioms Alexander313.Carlson.PrimitiveRequests.decodeData
#print axioms Alexander313.Carlson.PrimitiveRequests.ofFields
#print axioms Alexander313.Carlson.PrimitiveRequests.decode_request
#print axioms Alexander313.Carlson.PrimitiveRequests.packCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.decodeFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.decodeData_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.encoded_ofFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.encoded_decode_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.instPrimcodableRequest
#print axioms Alexander313.Carlson.PrimitiveRequests.request_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveRequests.ofFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.mk_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.decodeData_encode_request
#print axioms Alexander313.Carlson.PrimitiveRequests.fields_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.request_target_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.certificate_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.sourceIndex_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.decode_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.target_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.index_primrec
#print axioms Alexander313.Carlson.PrimitiveRequests.request_decode_program
#print axioms Alexander313.Carlson.PrimitiveRequests.schedule_decode_program
#print axioms Alexander313.Carlson.PrimitiveRequests.schedule_target_program
#print axioms Alexander313.Carlson.PrimitiveRequests.sourceIndex_program

-- PrimitivePresentationExamples: existing codes and certified finite computations.
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.empty
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.empty_code_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.noncanonical_carrier_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.malformed_components_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.duplicate_carrier_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.malformed_shape_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.request_data_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.invalid_schedule_regression
#print axioms Alexander313.Carlson.PrimitivePresentationExamples.invalid_schedule_program

-- Primitive recursive extrema and complete rational lifting data.
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_empty
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_empty
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_of_nonempty
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_of_nonempty
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_singleton
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_singleton
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_spec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_spec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_le_of_mem
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.le_maxD_of_mem
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_eq_iff
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_eq_iff
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.min_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.max_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.list_min?_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.list_max?_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.finsetView_min?_of_nonempty
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.finsetView_max?_of_nonempty
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_eq_list_min?_getD
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_eq_list_max?_getD
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_eq_foldl_of_view_cons
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_eq_foldl_of_view_cons
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.minD_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteExtrema.maxD_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableUp_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.rat_computableUp_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computablePredBound_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computablePlaceBelow_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableMap_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableTarget_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.Carriers
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computablePlaceBelow_eval_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableMap_fixed_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableTarget_fixed_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableMap_id_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableTarget_id_primrec
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableUp_program
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computablePredBound_program
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computablePlaceBelow_program
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableMap_program
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableTarget_program
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableMap_id_program
#print axioms Alexander313.Carlson.PrimitiveArithmeticLifting.computableTarget_id_program
#print axioms Alexander313.Carlson.PrimitivePatternLifting.map_primrec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.map_program
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftingCandidate_primrec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftingCandidate_program
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftMap_eval_primrec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftMap_primrec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftTarget_primrec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftMap_program
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftTarget_program
#print axioms Alexander313.Carlson.PrimitivePatternLifting.liftTarget_program_spec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.LiftInput
#print axioms Alexander313.Carlson.PrimitivePatternLifting.identity_liftTarget_primrec
#print axioms Alexander313.Carlson.PrimitivePatternLifting.identity_liftTarget_program
#print axioms Alexander313.Carlson.PrimitivePatternLifting.identity_liftMap_program
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.extrema_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.extrema_code_order_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.extrema_program_answers
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.affine
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.affine_primrec
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.affine_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.mapped_tables_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.mapped_tables_program
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.incomingAnswer
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.incomingAnswer_primrec
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.incoming_search_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.incoming_search_program
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.LiftInput
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.liftValue
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.liftValue_primrec
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.translatedInput
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.stationaryInput
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.emptyInput
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.nonpattern
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.nonpattern_not_pattern
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.nonpatternInput
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.translated_lifting_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.boundary_lifting_regression
#print axioms Alexander313.Carlson.PrimitiveLiftingExamples.lifting_program_answers

-- Uniform finite and rational certificate coding.
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeListWith
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeListWith_zero
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeListWith_succ
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeListWith_map
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeListWith_decode
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeListWith_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeVectorWith
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encode_vector
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeVectorWith_decode
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeVectorWith_map
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeVectorWith_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encode_list_map
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encodeArrowData
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encodeArrowData_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encodeArrowData_ofFn
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encode_arrow
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encodeTableData
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encodeTableData_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.encode_table
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decode_finPi
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decode_fin
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTaggedWith
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTaggedWith_map
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTaggedWith_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeArrowWith
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeArrowWith_map
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeArrowWith_decode
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeArrowWith_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTable
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTable_eq
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTable_shape
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTable_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeArrowWith
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeArrowWith_eq
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeArrowWith_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeArrow
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeArrow_eq
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeArrow_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeTable
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeTable_eq
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.normalizeTable_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.lookup
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.lookup_eq
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.lookup_primrec
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.decodeTable_program
#print axioms Alexander313.Carlson.PrimitiveFiniteFunctions.lookup_program
#print axioms Alexander313.Carlson.PrimitivePatternCode.TypedFields
#print axioms Alexander313.Carlson.PrimitivePatternCode.ofTypedFields
#print axioms Alexander313.Carlson.PrimitivePatternCode.encode_pattern
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeTypedFields
#print axioms Alexander313.Carlson.PrimitivePatternCode.decode_pattern
#print axioms Alexander313.Carlson.PrimitivePatternCode.carrierView
#print axioms Alexander313.Carlson.PrimitivePatternCode.mem_carrierView
#print axioms Alexander313.Carlson.PrimitivePatternCode.carrierView_lt
#print axioms Alexander313.Carlson.PrimitivePatternCode.encode_carrierView
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeLabel
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeLabel_eq
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeLabel_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeCarrier
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeCarrier_eq
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeCarrier_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeCarrier_bounds
#print axioms Alexander313.Carlson.PrimitivePatternCode.Data
#print axioms Alexander313.Carlson.PrimitivePatternCode.dataView
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeData
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeData_eq
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeData_encode
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeData_bounds
#print axioms Alexander313.Carlson.PrimitivePatternCode.decodeData_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.encodeData
#print axioms Alexander313.Carlson.PrimitivePatternCode.encodeData_dataView
#print axioms Alexander313.Carlson.PrimitivePatternCode.dataView_injective
#print axioms Alexander313.Carlson.PrimitivePatternCode.encodeData_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.normalize
#print axioms Alexander313.Carlson.PrimitivePatternCode.normalize_eq
#print axioms Alexander313.Carlson.PrimitivePatternCode.encode_normalize
#print axioms Alexander313.Carlson.PrimitivePatternCode.normalize_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.encoded_decode_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.instPrimcodablePatternCode
#print axioms Alexander313.Carlson.PrimitivePatternCode.pattern_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitivePatternCode.normalize_encode
#print axioms Alexander313.Carlson.PrimitivePatternCode.carrierMem
#print axioms Alexander313.Carlson.PrimitivePatternCode.carrierMem_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.carrierMem_dataView
#print axioms Alexander313.Carlson.PrimitivePatternCode.tableLookup
#print axioms Alexander313.Carlson.PrimitivePatternCode.tableLookup_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.tableLookup_ofFn
#print axioms Alexander313.Carlson.PrimitivePatternCode.relation₁
#print axioms Alexander313.Carlson.PrimitivePatternCode.relation₂
#print axioms Alexander313.Carlson.PrimitivePatternCode.relation₁_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.relation₂_primrec
#print axioms Alexander313.Carlson.PrimitivePatternCode.relation₁_dataView
#print axioms Alexander313.Carlson.PrimitivePatternCode.relation₂_dataView
#print axioms Alexander313.Carlson.PrimitivePatternCode.pattern_decode_program
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.originalCertificateEncoding
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.packCode
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.encode_witness
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeFields
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.TypedFields
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.ofTypedFields
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeTypedFields
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decode_witness
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeData
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.normalizeWitness
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeData_eq
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.normalizeWitness_eq
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.normalizeCertificate
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.normalizeCertificate_eq
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.packCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeFields_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeData_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.normalizeWitness_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.normalizeCertificate_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.encoded_decode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.instPrimcodableRationalCertificate
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.certificate_encoding_unchanged
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.size_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.witnessCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.fields
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.decodeData_encode
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.fields_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.sourceCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.targetCode_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.derivation_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.gridLabels
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.gridLabels_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.sourceData_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.targetData_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.list_pairwise
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.checkGrid
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.checkGrid_eq_true
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.checkGrid_primrec
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.certificate_decode_program
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.witness_normalize_program
#print axioms Alexander313.Carlson.PrimitiveRationalCertificate.grid_check_program
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.finite_function_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.original_arrow_encoding_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.arrow_index_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.table
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.table_decode
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.table_dimensions_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.list_components_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.malformed_boolean_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.malformed_rational_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.carrier_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.unsorted_pattern_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.malformed_pattern_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.offCarrierPattern
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.off_carrier_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.blankPattern
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.emptyWitness
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.emptyCertificate
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.emptyRaw
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.encode_emptyCertificate
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.decode_emptyRaw
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.empty_certificate_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.derivation_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.wrong_grid_size_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.malformed_witness_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.malformed_shape_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.table_machine_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.certificate_machine_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.gridCertificate
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.ascendingGrid
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.repeatedGrid
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.reversedGrid
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.grid_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.invalid_grid_data_regression
#print axioms Alexander313.Carlson.PrimitiveCertificateExamples.grid_machine_regression
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.labelAt
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.labelAt_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.labelAt_ofFn
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.entry₁
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.entry₂
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.entry₁_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.entry₂_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.entry₁_dataView
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.entry₂_dataView
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.PairCondition
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.instDecidablePairCondition
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.IsoData
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.instDecidableIsoData
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.pairCondition_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.isoData_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.mem_carrierView_iff
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.image_carrierView
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.isoData_dataView_iff
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkSource
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkTarget
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkSource_eq_true
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkTarget_eq_true
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkSource_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkTarget_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkFrame
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkFrame_eq_true
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkFrame_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.witness_check_eq
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkCertificate_primrec
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkRule_primrec_of_finite
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkChain_primrec_of_finite
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkGeneration_primrec_of_finite
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.source_check_program
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.frame_check_program
#print axioms Alexander313.Carlson.PrimitiveEndpointIso.checkRule_program_of_finite
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.ruleCertificate
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.duplicateCertificate
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.reversedCertificate
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.frame_accepts
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.frame_accepts_off_carrier_edges
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.frame_rejects_wrong_carrier
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.frame_rejects_missing_source_edge
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.frame_rejects_grid
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.missing_table_regression
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.dataView_regression
#print axioms Alexander313.Carlson.PrimitiveEndpointExamples.frame_machine_regression
