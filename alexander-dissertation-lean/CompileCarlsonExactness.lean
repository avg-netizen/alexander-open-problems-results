import Alexander313.Carlson.ExactnessExamples

open Alexander313 Alexander313.Carlson

/- Independent source-shaped statements for Carlson 15.5--15.7. -/

example {α : Type*} [LinearOrder α] (P Q : Str α) (hP : P.U.Nonempty) :
    Q.initialSpan P.U = Q.restrict (Q.U.filter (fun x => x ≤ P.U.max' hP)) :=
  Str.initialSpan_eq_initialCut Q P.U hP

example {α : Type*} [LinearOrder α] {P Q : Str α} (d : Str.Generates P Q) :
    Q.IsPattern ∧
      Str.Generates P (Q.restrict (Q.U.filter (fun x => ∃ p ∈ P.U, x ≤ p))) ∧
      Str.KCorrect (Q.restrict (Q.U.filter (fun x => ∃ p ∈ P.U, x ≤ p))) Q .one ∧
      Str.IsSub P Q := by
  have h := Str.Exact.of_generates d
  exact ⟨h.pattern, h.generates, h.correct, h.isSub⟩

example {α : Type*} [LinearOrder α] {P Q R : Str α}
    (hPQ : Str.IsSub P Q) (hQR : Str.IsSub Q R)
    (h : Str.Exact P R) :
    Q.IsPattern ∧
      Str.Generates P (Q.restrict (Q.U.filter (fun x => ∃ p ∈ P.U, x ≤ p))) ∧
      Str.KCorrect (Q.restrict (Q.U.filter (fun x => ∃ p ∈ P.U, x ≤ p))) Q .one := by
  have h' := h.restrict hPQ hQR
  exact ⟨h'.pattern, h'.generates, h'.correct⟩

example (U : Finset Ordinal.{0}) (β : Ordinal.{0})
    (hminimal : ∀ T f, Str.IsIso (Str.ofOrdinals U) (Str.ofOrdinals T) f →
      (∀ z ∈ U, f z ≤ z) → T = U)
    (hcorrect : Str.KCorrect (Str.ofOrdinals (U.filter (fun x => x ≤ β)))
      (Str.ofOrdinals U) .one) :
    ∀ T f, Str.IsIso (Str.ofOrdinals (U.filter (fun x => x ≤ β)))
      (Str.ofOrdinals T) f →
      (∀ z ∈ U.filter (fun x => x ≤ β), f z ≤ z) → T = U.filter (fun x => x ≤ β) :=
  IsominimalOrdinalSet.initialCut hminimal β hcorrect

example (U : Finset Ordinal.{0}) (β : Ordinal.{0}) :
    Str.KCorrect (Str.ofOrdinals (U.filter (fun x => x ≤ β))) (Str.ofOrdinals U) .one ↔
      ∀ x ∈ U, x ≤ β → ∀ y ∈ U, R1 x y → y ≤ β :=
  Str.initialCut_correct_iff (Str.ofOrdinals U) β

example : ∃ (U : Finset Ordinal.{0}) (a : Ordinal.{0}),
    IsominimalOrdinalSet U ∧ a ∈ U ∧
      ¬IsominimalOrdinalSet (U.filter (fun x => x ≤ a)) ∧
      ¬Str.KCorrect (Str.ofOrdinals (U.filter (fun x => x ≤ a))) (Str.ofOrdinals U) .one :=
  exists_isominimal_uncorrect_cut

#print axioms Str.mem_initialCut
#print axioms Str.initialCut_isSub
#print axioms Str.mem_initialSpan
#print axioms Str.initialSpan_isSub
#print axioms Str.initialSpan_empty
#print axioms Str.initialSpan_eq_initialCut
#print axioms Str.initialSpan_eq_of_bounded
#print axioms Str.kCorrect_one_iff_no_crossing
#print axioms Str.initialCut_correct_iff
#print axioms Str.initialSpan_correct_iff
#print axioms Str.Exact.isSub
#print axioms Str.Exact.source_pattern
#print axioms Str.Exact.of_generates
#print axioms Str.Exact.refl
#print axioms Str.Exact.restrict
#print axioms exists_least_ordinal_copy
#print axioms IsominimalOrdinalSet.le_covering
#print axioms IsominimalOrdinalSet.iff_le_covering
#print axioms IsominimalOrdinalSet.union
#print axioms IsominimalOrdinalSet.of_initial_correct
#print axioms IsominimalOrdinalSet.initialCut
#print axioms empty_exact_in_pattern
#print axioms empty_ordinal_set_isominimal
#print axioms singleton_isominimal_iff_zero
#print axioms positive_of_strict_first
#print axioms exists_isominimal_uncorrect_cut
