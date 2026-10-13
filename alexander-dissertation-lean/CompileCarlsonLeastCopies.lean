import Alexander313.Carlson.AmalgamationExistenceExamples
import Alexander313.Carlson.LeastCopyCompletenessExamples

open Alexander313.Carlson

-- Ambient correctness has no containment or boundedness hypothesis on T.
example {U : Finset Ordinal.{0}} (hU : IsominimalOrdinalSet U)
    (T : Finset Ordinal.{0}) :
    ∀ p x y : Ordinal.{0}, x ∈ T → y ∈ T → Str.LeastGE U x p → p < y → R1 x y →
      ∃ p', Str.LeastGE U y p' ∧ R1 p p' :=
  hU.kCorrect T .one

example {U : Finset Ordinal.{0}} (hU : IsominimalOrdinalSet U)
    (T : Finset Ordinal.{0}) :
    ∀ p x y : Ordinal.{0}, x ∈ T → y ∈ T → Str.LeastGE U x p → p < y → R2 x y →
      ∃ p', Str.LeastGE U y p' ∧ R2 p p' :=
  hU.kCorrect T .two

example {U V : Finset Ordinal.{0}} (hU : IsominimalOrdinalSet U) (hUV : U ⊆ V) :
    Str.Generates (Str.ofOrdinals U) (Str.ofOrdinals V) ↔
      ∀ z ∈ V, ∃ p ∈ U, z ≤ p :=
  hU.generates_iff hUV

example (P : Str ℚ) (hP : P.IsPattern) :
    ∃ h : ℚ → Ordinal.{0},
      Str.IsIso P (Str.ofOrdinals (P.U.image h)) h ∧
      (∀ g : ℚ → Ordinal.{0}, P.CoveringR g → ∀ x ∈ P.U, h x ≤ g x) ∧
      IsominimalOrdinalSet (P.U.image h) ∧
      (∀ (T : Finset Ordinal.{0}) (k : Lvl),
        Str.KCorrect (Str.ofOrdinals (P.U.image h)) (Str.ofOrdinals T) k) ∧
      (∀ V : Finset Ordinal.{0}, P.U.image h ⊆ V →
        (∀ z ∈ V, ∃ p ∈ P.U.image h, z ≤ p) →
        Str.Generates (Str.ofOrdinals (P.U.image h)) (Str.ofOrdinals V)) :=
  exists_complete_minimal_ordinal_copy P hP


#print axioms Alexander313.Carlson.finiteOrdinalRelabeling
#print axioms Alexander313.Carlson.Str.GeneratingRule.of_ordinal_isos
#print axioms Alexander313.Carlson.Str.ExactlyGenerates.of_ordinal_isos
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.finite_capture
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_exactlyGenerates
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_generates
#print axioms Alexander313.Carlson.GeneratingSequence.OrdinalRealization.stage_kCorrect
#print axioms Alexander313.Carlson.IsominimalOrdinalSet.kCorrect
#print axioms Alexander313.Carlson.IsominimalOrdinalSet.generates
#print axioms Alexander313.Carlson.IsominimalOrdinalSet.generates_iff
#print axioms Alexander313.Carlson.exists_complete_minimal_ordinal_copy
#print axioms Alexander313.Carlson.empty_ordinal_generates_iff
#print axioms Alexander313.Carlson.singleton_zero_kCorrect
#print axioms Alexander313.Carlson.singleton_zero_generates_iff
#print axioms Alexander313.Carlson.singleton_zero_unbounded_extension_rejected
#print axioms Alexander313.Carlson.positive_singleton_bounded_extension_rejected
#print axioms Alexander313.Carlson.exists_least_chain_generating_new_zero

-- Definition 15.8 is an explicit obligation on actual embeddings and their union.
example {n : ℕ} (P : Fin n → Str ℚ) (hP : ∀ i, (P i).IsPattern) :
    ∃ (U : Finset Ordinal.{0}) (f : Fin n → ℚ → Ordinal.{0}),
      (Str.ofOrdinals U).IsPattern ∧
      (∀ i, Str.IsIso (P i) ((Str.ofOrdinals U).restrict ((P i).U.image (f i))) (f i)) ∧
      U = Finset.univ.biUnion (fun i => (P i).U.image (f i)) ∧
      (∀ i, Str.Exact ((Str.ofOrdinals U).restrict ((P i).U.image (f i))) (Str.ofOrdinals U)) := by
  obtain ⟨U, f, a, _, _⟩ := exists_ordinal_amalgamation P hP
  exact ⟨U, f, a.pattern, a.embeddings, a.union, a.exact⟩

#print axioms Alexander313.Carlson.Str.Valid.least_copy_agrees
#print axioms Alexander313.Carlson.IsominimalOrdinalSet.of_valid
#print axioms Alexander313.Carlson.IsominimalOrdinalSet.exact
#print axioms Alexander313.Carlson.IsominimalOrdinalSet.biUnion
#print axioms Alexander313.Carlson.exists_ordinal_amalgamation

#print axioms Alexander313.Carlson.Str.Amalgamation
#print axioms Alexander313.Carlson.empty_family_amalgamation
#print axioms Alexander313.Carlson.distinct_singletons_amalgamate_to_zero
#print axioms Alexander313.Carlson.positive_singleton_not_exact_in_union
#print axioms Alexander313.Carlson.ordinary_singleton_union_not_amalgamation
#print axioms Alexander313.Carlson.downward_extension_least_copy_agrees
