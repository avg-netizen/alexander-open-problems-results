import Alexander313.Alexander.DeltaEncoding
import Alexander313.Alexander.FirstOrderClosure
import Alexander313.ProofClosure

/-!
# Alexander consequence equals finite validity-certificate consequence

The closed BL theory is constructed from its matrices. To preserve a single
shared assignment across possibly open premises, Δ-formulas are made into
sentences in the language with constants indexed by the variables. Mathlib's
first-order compactness theorem then supplies a finite set of source premises.
All selected BL assumptions are discharged in ΔM, where the entire closed BL
theory holds. No proof-enumerator or completeness contract is an input.

Source: Alexander Definition 1.2.5, Theorem 1.2.6 (finite-consequence part),
Definitions 1.3.1--1.3.7 and Proposition 1.3.11.
-/

namespace Alexander313

def SemanticConsequence {Owner : Type} (axioms : Formula Owner → Prop)
    (φ : Formula Owner) : Prop :=
  ∀ (D : Type) (_ : Nonempty D) (M : ModalModel Owner D) (s : Nat → D),
    (∀ θ, axioms θ → generalTruth M θ s) → generalTruth M φ s

theorem Provable.semanticConsequence {Owner : Type} {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (h : Provable axioms φ) : SemanticConsequence axioms φ := by
  obtain ⟨c⟩ := h
  intro D hD M s hax
  exact chain_elim M c.premises φ s
    (fun θ hθ => hax θ (c.admitted θ hθ)) (c.validity D hD M s)

namespace Delta

def BLTheory (Owner : Type) : (language Owner).Theory :=
  FirstOrderClosure.universalSentence '' baseLogicMatrices Owner

theorem model_BLTheory_iff {Owner D : Type} [Nonempty D]
    (N : (language Owner).Structure D) :
    letI : (language Owner).Structure D := N
    FirstOrder.Language.Theory.Model D (BLTheory Owner) ↔ SatisfiesBL N := by
  letI : (language Owner).Structure D := N
  constructor
  · intro h σ hσ s
    have hc := h.realize_of_mem _ (⟨σ, hσ, rfl⟩)
    exact (FirstOrderClosure.universalSentence_realize σ).mp hc s
  · intro h
    refine ⟨?_⟩
    intro σ hσ
    obtain ⟨matrix, hm, rfl⟩ := hσ
    exact (FirstOrderClosure.universalSentence_realize matrix).mpr (h matrix hm)

abbrev assignmentLanguage (Owner : Type) : FirstOrder.Language :=
  (language Owner).withConstants Nat

def assignmentSentence {Owner : Type} (φ : Formula Owner) :
    (assignmentLanguage Owner).Sentence :=
  FirstOrder.Language.Formula.equivSentence (formula φ)

def sourceTheory {Owner : Type} (axioms : Formula Owner → Prop) :
    (assignmentLanguage Owner).Theory :=
  ((language Owner).lhomWithConstants Nat).onTheory (BLTheory Owner) ∪
    assignmentSentence '' {φ | axioms φ}

theorem semanticConsequence_firstOrder {Owner : Type} {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (h : SemanticConsequence axioms φ) :
    FirstOrder.Language.Theory.ModelsBoundedFormula (sourceTheory axioms)
      (assignmentSentence φ) := by
  apply FirstOrder.Language.Theory.models_sentence_iff.mpr
  intro N
  letI : (language Owner).Structure N := ((language Owner).lhomWithConstants Nat).reduct N
  have hBL : FirstOrder.Language.Theory.Model N (BLTheory Owner) := by
    refine ⟨?_⟩
    intro σ hσ
    have ht := FirstOrder.Language.Theory.realize_sentence_of_mem
      (M := N) (sourceTheory axioms)
      (Set.mem_union_left _ (⟨σ, hσ, rfl⟩))
    exact (FirstOrder.Language.LHom.realize_onSentence N _ _).mp ht
  have hmodal := (model_BLTheory_iff (inferInstance : (language Owner).Structure N)).mp hBL
  let M := modalOfStructure (inferInstance : (language Owner).Structure N) hmodal
  let assignment : Nat → N := fun x => ((language Owner).con x : N)
  have hax : ∀ θ, axioms θ → generalTruth M θ assignment := by
    intro θ hθ
    have ht := FirstOrder.Language.Theory.realize_sentence_of_mem
      (M := N) (sourceTheory axioms) (Set.mem_union_right _ (⟨θ, hθ, rfl⟩))
    have hd := (FirstOrder.Language.Formula.realize_equivSentence N (formula θ)).mp ht
    exact (formula_realize_modalOfStructure _ hmodal θ assignment).mp hd
  have ht := h N inferInstance M assignment hax
  apply (FirstOrder.Language.Formula.realize_equivSentence N (formula φ)).mpr
  exact (formula_realize_modalOfStructure _ hmodal φ assignment).mpr ht

/-- A finite first-order subtheory of the BL/source translation can always
    be covered by the whole BL theory and finitely many original premises.
    The finite choices here are proof data, not an effective axiom selector. -/
theorem finite_source_cover {Owner : Type} {axioms : Formula Owner → Prop}
    (T : Finset ((assignmentLanguage Owner).Sentence))
    (hT : (T : Set ((assignmentLanguage Owner).Sentence)) ⊆ sourceTheory axioms) :
    ∃ Γ : List (Formula Owner), (∀ θ ∈ Γ, axioms θ) ∧
      ∀ σ ∈ T,
        σ ∈ ((language Owner).lhomWithConstants Nat).onTheory (BLTheory Owner) ∨
          ∃ θ ∈ Γ, assignmentSentence θ = σ := by
  classical
  revert hT
  induction T using Finset.induction_on with
  | empty =>
    intro hT
    exact ⟨[], by simp, by simp⟩
  | @insert σ T hσ ih =>
    intro hT
    have ht : (T : Set ((assignmentLanguage Owner).Sentence)) ⊆ sourceTheory axioms :=
      fun τ hτ => hT (Finset.mem_insert_of_mem hτ)
    obtain ⟨Γ, hΓ, hcover⟩ := ih ht
    rcases hT (Finset.mem_insert_self σ T) with hBL | hsource
    · refine ⟨Γ, hΓ, ?_⟩
      intro τ hτ
      rcases Finset.mem_insert.mp hτ with rfl | hτ
      · exact Or.inl hBL
      · exact hcover τ hτ
    · obtain ⟨θ, hθ, hsentence⟩ := hsource
      refine ⟨θ :: Γ, ?_, ?_⟩
      · intro η hη
        rcases List.mem_cons.mp hη with rfl | hη
        · exact hθ
        · exact hΓ η hη
      · intro τ hτ
        rcases Finset.mem_insert.mp hτ with rfl | hτ
        · exact Or.inr ⟨θ, List.mem_cons_self, hsentence⟩
        · rcases hcover τ hτ with hb | ⟨η, hη, heq⟩
          · exact Or.inl hb
          · exact Or.inr ⟨η, List.mem_cons_of_mem _ hη, heq⟩

theorem firstOrder_finite_consequence_certificate {Owner : Type}
    {axioms : Formula Owner → Prop} {φ : Formula Owner}
    (T : Finset ((assignmentLanguage Owner).Sentence))
    (hT : (T : Set ((assignmentLanguage Owner).Sentence)) ⊆ sourceTheory axioms)
    (hφ : FirstOrder.Language.Theory.ModelsBoundedFormula
      (T : (assignmentLanguage Owner).Theory) (assignmentSentence φ)) :
    Provable axioms φ := by
  obtain ⟨Γ, hΓ, hcover⟩ := finite_source_cover T hT
  refine ⟨{ premises := Γ, admitted := hΓ, validity := ?_ }⟩
  intro D hD M s
  letI : Nonempty D := hD
  apply chain_intro
  intro hpremises
  letI : (language Owner).Structure D := structureOfModal M
  letI : (FirstOrder.Language.constantsOn Nat).Structure D :=
    FirstOrder.Language.constantsOn.structure s
  have hBL : FirstOrder.Language.Theory.Model D (BLTheory Owner) :=
    (model_BLTheory_iff (structureOfModal M)).mpr (structureOfModal_satisfiesBL M)
  have hmodel : FirstOrder.Language.Theory.Model
      D (T : (assignmentLanguage Owner).Theory) := by
    refine ⟨?_⟩
    intro σ hσ
    rcases hcover σ hσ with hbase | ⟨θ, hθ, rfl⟩
    · obtain ⟨matrix, hm, rfl⟩ := hbase
      apply (FirstOrder.Language.LHom.realize_onSentence D _ _).mpr
      exact hBL.realize_of_mem matrix hm
    · apply (FirstOrder.Language.Formula.realize_equivSentence D (formula θ)).mpr
      exact (formula_realize M θ s).mpr (hpremises θ hθ)
  letI : FirstOrder.Language.Theory.Model
      D (T : (assignmentLanguage Owner).Theory) := hmodel
  have ht := hφ.realize_sentence D
  have hd := (FirstOrder.Language.Formula.realize_equivSentence D (formula φ)).mp ht
  exact (formula_realize M φ s).mp hd

theorem provable_iff_sourceTheory_models {Owner : Type}
    (axioms : Formula Owner → Prop) (φ : Formula Owner) :
    Provable axioms φ ↔ FirstOrder.Language.Theory.ModelsBoundedFormula
      (sourceTheory axioms) (assignmentSentence φ) := by
  constructor
  · intro h
    exact semanticConsequence_firstOrder h.semanticConsequence
  · intro h
    obtain ⟨T, hT, hφ⟩ := FirstOrder.Language.Theory.models_iff_finset_models.mp h
    exact firstOrder_finite_consequence_certificate T hT hφ

theorem valid_iff_BLTheory_models {Owner : Type} (φ : Formula Owner) :
    Valid φ ↔ FirstOrder.Language.Theory.ModelsBoundedFormula (BLTheory Owner)
      (FirstOrderClosure.universalSentence (formula φ)) := by
  constructor
  · intro h
    apply FirstOrder.Language.Theory.models_sentence_iff.mpr
    intro N
    have hBL := (model_BLTheory_iff
      (inferInstance : (language Owner).Structure N)).mp N.is_model
    apply (FirstOrderClosure.universalSentence_realize (formula φ)).mpr
    exact (valid_iff_firstOrder_BL φ).mp h N inferInstance
      (inferInstance : (language Owner).Structure N) hBL
  · intro h D hD M s
    letI : Nonempty D := hD
    letI : (language Owner).Structure D := structureOfModal M
    letI : FirstOrder.Language.Theory.Model D (BLTheory Owner) :=
      (model_BLTheory_iff (structureOfModal M)).mpr (structureOfModal_satisfiesBL M)
    exact (formula_realize M φ s).mp
      ((FirstOrderClosure.universalSentence_realize (formula φ)).mp
        (h.realize_sentence D) s)

end Delta

theorem SemanticConsequence.provable {Owner : Type} {axioms : Formula Owner → Prop}
    {φ : Formula Owner} (h : SemanticConsequence axioms φ) : Provable axioms φ := by
  obtain ⟨T, hT, hφ⟩ := FirstOrder.Language.Theory.models_iff_finset_models.mp
    (Delta.semanticConsequence_firstOrder h)
  exact Delta.firstOrder_finite_consequence_certificate T hT hφ

theorem provable_iff_semanticConsequence {Owner : Type}
    (axioms : Formula Owner → Prop) (φ : Formula Owner) :
    Provable axioms φ ↔ SemanticConsequence axioms φ :=
  ⟨Provable.semanticConsequence, SemanticConsequence.provable⟩

end Alexander313
