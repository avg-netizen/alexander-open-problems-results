import Alexander313.Carlson.GenerationCharacterizationExamples

open Alexander313.Carlson

-- The extended map retains the supplied values on the old carrier.
example {α β : Type*} [LinearOrder α] [LinearOrder β]
    [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β]
    {A S : Finset α} (hAS : A ⊆ S) (f : A ↪o β) :
    ∃ g : S ↪o β, ∀ x (hx : x ∈ A), g ⟨x, hAS hx⟩ = f ⟨x, hx⟩ :=
  exists_finite_order_extension hAS f

-- This is the original existential generation relation with its actual
-- hidden endpoint and exact-generation witness, rather than a new predicate.
example {α : Type*} [LinearOrder α] [Nonempty α]
    {P Q : Str α} {P' Q' : Str ℚ} {h f : α → ℚ}
    (d : Str.Generates P Q) (e : Str.IsIso P P' h) (eplus : Str.IsIso Q Q' f)
    (hfix : ∀ x ∈ P.U, f x = h x) :
    ∃ R : Str ℚ, Str.ExactlyGenerates P' R ∧ Str.IsSub Q' R ∧ P'.U ⊆ Q'.U :=
  d.of_rational_isos e eplus hfix

-- Exactness commutes with the given finite embedding on actual least labels.
example {P Q : Str ℚ} {f : ℚ → ℚ}
    (e : Str.IsIso P (Q.restrict (P.U.image f)) f)
    (d : Str.Exact (Q.restrict (P.U.image f)) Q)
    (A : PatternRealization P) (B : PatternRealization Q) :
    ∀ x ∈ P.U, B.label (f x) = A.label x :=
  e.exact_least_copy_agrees d A B

-- Expand validity and continuity, including all covering-extension and
-- correctness obligations, independently of the new theorem's name.
example {P Q : Str ℚ} (hP : P.IsPattern) (hQ : Q.IsPattern) :
    (∃ R : Str ℚ, Str.ExactlyGenerates P R ∧ Str.IsSub Q R ∧ P.U ⊆ Q.U) ↔
      (Str.IsSub P Q ∧ ∀ h, P.CoveringR h →
        ∃ h', Q.CoveringR h' ∧ ∀ x ∈ P.U, h' x = h x) ∧
      (Str.IsSub P Q ∧ (∀ z ∈ Q.U, ∃ p ∈ P.U, z ≤ p) ∧
        Str.KCorrect P Q .one ∧ Str.KCorrect P Q .two) :=
  Str.Generates.iff_valid_continuous hP hQ

example {P Q : Str ℚ} (hsub : Str.IsSub P Q)
    (A : PatternRealization P) (B : PatternRealization Q) :
    (∃ R : Str ℚ, Str.ExactlyGenerates P R ∧ Str.IsSub Q R ∧ P.U ⊆ Q.U) ↔
      (∀ z ∈ Q.U, ∃ p ∈ P.U, z ≤ p) ∧ (∀ x ∈ P.U, B.label x = A.label x) :=
  Str.Generates.iff_bounded_and_least_copy_agrees hsub A B

#print axioms Alexander313.Carlson.PatternRealization.image_isominimal
#print axioms Alexander313.Carlson.PatternRealization.label_eq_of_isominimal_copy
#print axioms Alexander313.Carlson.Str.Exact.initialSpan_image_isominimal
#print axioms Alexander313.Carlson.Str.Exact.least_copy_agrees
#print axioms Alexander313.Carlson.Str.IsIso.exact_least_copy_agrees
#print axioms Alexander313.Carlson.exists_finite_order_extension
#print axioms Alexander313.Carlson.exists_rational_relabeling_extending
#print axioms Alexander313.Carlson.Str.IsIso.from_same_labels
#print axioms Alexander313.Carlson.Str.Generates.of_rational_isos
#print axioms Alexander313.Carlson.Str.IsIso.initialSpan
#print axioms Alexander313.Carlson.Str.Exact.of_rational_isos
#print axioms Alexander313.Carlson.Str.Generates.of_least_copy_agreement
#print axioms Alexander313.Carlson.Str.Generates.iff_bounded_and_least_copy_agrees
#print axioms Alexander313.Carlson.Str.Generates.iff_valid_continuous
#print axioms Alexander313.Carlson.Str.Generates.iff_cofinallyValid_continuous
#print axioms Alexander313.Carlson.Str.Generates.trans
#print axioms Alexander313.Carlson.finite_extension_preserves_endpoints_and_gap
#print axioms Alexander313.Carlson.finite_extension_preserves_middle_and_both_sides
#print axioms Alexander313.Carlson.reversed_endpoints_have_no_relabeling
#print axioms Alexander313.Carlson.bounded_last_singleton_not_generated
#print axioms Alexander313.Carlson.valid_empty_source_not_generated
