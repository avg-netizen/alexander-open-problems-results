import Alexander313.Carlson.CorePresentationExamples

open Alexander313.Carlson

-- The targets use the actual common ordinal core, not an assumed quotient.
example : ∀ a : Ordinal.{0}, a < coreBound →
    ∃ n : ℕ, ComputablePointedPresentation.label n = a :=
  ComputablePointedPresentation.label_surjective
example : ∀ a : Ordinal.{0}, a < coreBound →
    ∃! n : ℕ, CanonicalPointedCodes.Canonical n ∧ ComputablePointedPresentation.label n = a :=
  CanonicalPointedCodes.exists_unique_canonical
example : Function.Injective ComputableCoreEnumeration.value :=
  ComputableCoreEnumeration.value_injective
example : ∀ a : Ordinal.{0}, a < coreBound → ∃ n : ℕ, ComputableCoreEnumeration.value n = a :=
  ComputableCoreEnumeration.value_surjective
example : ∀ n : ℕ, ComputableCoreEnumeration.value n < coreBound :=
  ComputableCoreEnumeration.value_lt_coreBound
example : ∃ machine : Nat.Partrec.Code, ∀ m n : ℕ,
    machine.eval (Nat.pair m n) = Part.some (Encodable.encode (ComputableCoreEnumeration.compare m n)) :=
  ComputableCoreEnumeration.comparison_program
example : ∀ m n : ℕ,
    ((ComputableCoreEnumeration.compare m n).1 = true ↔ m = n) :=
  ComputableCoreEnumeration.compare_eq_iff
example : Nonempty Alexander313.OrdinalPackage := EffectiveCorePackage.package_exists

#print axioms ComputablePointedPresentation.valid_primrec
#print axioms ComputablePointedPresentation.fallback_valid
#print axioms ComputablePointedPresentation.rawData_primrec
#print axioms ComputablePointedPresentation.data_primrec
#print axioms ComputablePointedPresentation.data_valid
#print axioms ComputablePointedPresentation.data_encodePoint
#print axioms ComputablePointedPresentation.point_encodePoint
#print axioms ComputablePointedPresentation.point_surjective
#print axioms ComputablePointedPresentation.label_lt_coreBound
#print axioms ComputablePointedPresentation.label_surjective
#print axioms ComputablePointedPresentation.comparison_computable
#print axioms ComputablePointedPresentation.comparison_correct
#print axioms ComputablePointedPresentation.same_computable
#print axioms ComputablePointedPresentation.same_eq_true
#print axioms ComputablePointedPresentation.same_self
#print axioms ComputablePointedPresentation.comparison_program
#print axioms ComputablePointedPresentation.data_of_decode_none
#print axioms ComputablePointedPresentation.data_of_invalid
#print axioms CanonicalPointedCodes.find_computable
#print axioms CanonicalPointedCodes.exists_same
#print axioms CanonicalPointedCodes.representative_same
#print axioms CanonicalPointedCodes.representative_label
#print axioms CanonicalPointedCodes.representative_le
#print axioms CanonicalPointedCodes.representative_le_of_label
#print axioms CanonicalPointedCodes.representative_computable
#print axioms CanonicalPointedCodes.representative_eq_iff
#print axioms CanonicalPointedCodes.representative_canonical
#print axioms CanonicalPointedCodes.canonical_zero
#print axioms CanonicalPointedCodes.canonical_iff_no_earlier
#print axioms CanonicalPointedCodes.canonical_label_injective
#print axioms CanonicalPointedCodes.checkCanonical_computable
#print axioms CanonicalPointedCodes.checkCanonical_eq_true
#print axioms CanonicalPointedCodes.exists_unique_canonical
#print axioms CanonicalPointedCodes.toCore_bijective
#print axioms CanonicalPointedCodes.representative_program
#print axioms CanonicalPointedCodes.canonical_program
#print axioms ComputableCoreEnumeration.canonical_unbounded
#print axioms ComputableCoreEnumeration.checkNext_eq_true
#print axioms ComputableCoreEnumeration.checkNext_computable
#print axioms ComputableCoreEnumeration.exists_next
#print axioms ComputableCoreEnumeration.next_spec
#print axioms ComputableCoreEnumeration.next_le
#print axioms ComputableCoreEnumeration.next_computable
#print axioms ComputableCoreEnumeration.enumerate_canonical
#print axioms ComputableCoreEnumeration.enumerate_lt_succ
#print axioms ComputableCoreEnumeration.enumerate_strictMono
#print axioms ComputableCoreEnumeration.index_le_enumerate
#print axioms ComputableCoreEnumeration.enumerate_surjective
#print axioms ComputableCoreEnumeration.enumerate_computable
#print axioms ComputableCoreEnumeration.value_lt_coreBound
#print axioms ComputableCoreEnumeration.value_injective
#print axioms ComputableCoreEnumeration.value_surjective
#print axioms ComputableCoreEnumeration.toCore_bijective
#print axioms ComputableCoreEnumeration.compare_computable
#print axioms ComputableCoreEnumeration.compare_correct
#print axioms ComputableCoreEnumeration.compare_eq_iff
#print axioms ComputableCoreEnumeration.enumeration_program
#print axioms ComputableCoreEnumeration.comparison_program
#print axioms EffectiveCorePackage.recognizing_program
#print axioms EffectiveCorePackage.binary_recognizing_program
#print axioms EffectiveCorePackage.less_computable
#print axioms EffectiveCorePackage.first_computable
#print axioms EffectiveCorePackage.second_computable
#print axioms EffectiveCorePackage.less_correct
#print axioms EffectiveCorePackage.first_correct
#print axioms EffectiveCorePackage.second_correct
#print axioms EffectiveCorePackage.order
#print axioms EffectiveCorePackage.value_pre
#print axioms EffectiveCorePackage.presentation
#print axioms EffectiveCorePackage.presentation_bound
#print axioms EffectiveCorePackage.less_program
#print axioms EffectiveCorePackage.first_program
#print axioms EffectiveCorePackage.second_program
#print axioms EffectiveCorePackage.package_exists
#print axioms EffectiveCorePackage.package
#print axioms CorePresentationExamples.nonpattern_rejected
#print axioms CorePresentationExamples.nonpattern_replaced
#print axioms CorePresentationExamples.offCarrierPoint_seed_valid
#print axioms CorePresentationExamples.offCarrierPoint_rejected
#print axioms CorePresentationExamples.offCarrierPoint_replaced
#print axioms CorePresentationExamples.emptyCarrier_seed_valid
#print axioms CorePresentationExamples.emptyCarrier_rejected
#print axioms CorePresentationExamples.emptyCarrier_replaced
#print axioms CorePresentationExamples.offCarrierEdges_valid
#print axioms CorePresentationExamples.offCarrierEdges_preserved
#print axioms CorePresentationExamples.normalization_idempotent
#print axioms CorePresentationExamples.duplicate_normalization
#print axioms CorePresentationExamples.zero_is_first
#print axioms CorePresentationExamples.no_enumeration_duplicates
#print axioms CorePresentationExamples.strict_self_rejects
#print axioms CorePresentationExamples.first_self_accepts
#print axioms CorePresentationExamples.second_self_accepts
#print axioms CorePresentationExamples.false_program_has_empty_domain
#print axioms CorePresentationExamples.true_program_has_full_domain
