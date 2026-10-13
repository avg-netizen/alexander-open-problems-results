import Alexander313.FullRecordedAdmissions
import Alexander313.RecordedPrefixes

/-!
# Derived own prefixes for the complete guarded recorded table

The exact finite implication chain is an actual recorded validity. Each actual
premise, including a padded guarded main row, has an admissible own-prefix row.
Literal same-label deduction distributes knowledge over that chain. No
unrestricted necessitation, erased-validity admission, ordinal reflection or
source soundness premise is used. This finite lemma does not supply the missing
prescribed-lift/retained-query or local truth verification constructions.
-/

namespace Alexander313
namespace FullRecordedAdmissions

variable {Label : Type} [LinearOrder Label] {A E : Finset Nat} {a : Nat}
    {R₁ R₂ : Label → Label → Prop} {ν δ : Label}
    {R : Nat → Nat → Prop} {C : CommonCorePresentation R}

theorem prefix_cut {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (h : FullRecordedAdmissions C A E a R₁ R₂ φ) (below : ∀ μ ∈ φ.labelSupport, μ < ν)
    (hνδ : ν < δ) :
    LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ (.know (.indexed a ν) φ) := by
  refine ⟨.«prefix» ν ha h below, ?_⟩
  intro μ hμ
  rcases Finset.mem_insert.mp hμ with rfl | hμ
  · exact hνδ
  · exact lt_trans (below μ hμ) hνδ

theorem own_validity_cut {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (hv : Valid φ) (hc : φ.Closed) (hadm : φ.RecordedAdmissible A E)
    (below : ∀ μ ∈ φ.labelSupport, μ < ν) (hνδ : ν < δ) :
    Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ) (.know (.indexed a ν) φ) := by
  have hk : (Formula.know (.indexed a ν) φ).RecordedAdmissible A E :=
    (Formula.recordedAdmissible_know_indexed A E a ν φ).mpr ⟨ha, hadm, below⟩
  have bg : RecordedBackground A E a R₁ (.know (.indexed a ν) φ) := by
    simpa only [Formula.universalClosure_eq_self_of_closed _
      (show (Formula.know (.indexed a ν) φ).Closed from hc)] using
      RecordedBackground.own_validity (A := A) (E := E) (a := a) (R₁ := R₁) ν φ hv
        ((Formula.recordedAdmissible_universalClosure A E _).mpr hk)
  apply Provable.of_axiom
  refine ⟨.background bg, ?_⟩
  intro μ hμ
  rcases Finset.mem_insert.mp hμ with rfl | hμ
  · exact hνδ
  · exact lt_trans (below μ hμ) hνδ

theorem deduction_cut (φ ψ : Formula (RecordedHead Nat Label)) (ha : a ∈ A)
    (hφ : φ.Closed) (hψ : ψ.Closed) (hadmφ : φ.RecordedAdmissible A E)
    (hadmψ : ψ.RecordedAdmissible A E)
    (belowφ : ∀ μ ∈ φ.labelSupport, μ < ν) (belowψ : ∀ μ ∈ ψ.labelSupport, μ < ν)
    (hνδ : ν < δ) : Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ)
      (.imp (.know (.indexed a ν) (.imp φ ψ))
        (.imp (.know (.indexed a ν) φ) (.know (.indexed a ν) ψ))) := by
  rw [← Formula.indexedDeduction_eq_of_closed a ν φ ψ hφ hψ]
  apply Provable.of_axiom
  refine ⟨.background (.deduction ν φ ψ
    (Formula.indexedDeduction_admissible A E a ν φ ψ ha hadmφ hadmψ belowφ belowψ)), ?_⟩
  intro μ hμ
  rw [Formula.labelSupport_indexedDeduction] at hμ
  rcases Finset.mem_insert.mp hμ with rfl | hμ
  · exact hνδ
  · exact lt_trans ((Finset.mem_union.mp hμ).elim (belowφ μ) (belowψ μ)) hνδ

/-- Note 24 §4's finite-consequence prefix lemma for the complete actual
    background/guarded-main/prefix table. Its proof uses only the finite premises and exact chain. -/
theorem prefix_of_certificate {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (c : Certificate (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) ν) φ)
    (hc : φ.Closed) (hadm : φ.RecordedAdmissible A E)
    (target : ∀ μ ∈ φ.labelSupport, μ < ν) (hνδ : ν < δ) :
    Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ) (.know (.indexed a ν) φ) := by
  have closedΓ : ∀ θ ∈ c.premises, θ.Closed := fun θ hθ => (c.admitted θ hθ).1.closed
  have admΓ : ∀ θ ∈ c.premises, θ.RecordedAdmissible A E :=
    fun θ hθ => (c.admitted θ hθ).1.admissible
  have belowΓ : ∀ θ ∈ c.premises, ∀ μ ∈ θ.labelSupport, μ < ν :=
    fun θ hθ => (c.admitted θ hθ).2
  have start : Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ)
      (.know (.indexed a ν) (Formula.chain c.premises φ)) :=
    own_validity_cut ha c.validity (Formula.chain_closed _ _ closedΓ hc)
      (Formula.recordedAdmissible_chain A E _ φ hadm admΓ)
      (Formula.labelSupport_chain_below _ φ ν target belowΓ) hνδ
  have distribute : ∀ Γ : List (Formula (RecordedHead Nat Label)),
      (∀ θ ∈ Γ, θ.Closed) → (∀ θ ∈ Γ, θ.RecordedAdmissible A E) →
      (∀ θ ∈ Γ, ∀ μ ∈ θ.labelSupport, μ < ν) →
      Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ)
        (.know (.indexed a ν) (Formula.chain Γ φ)) →
      (∀ θ ∈ Γ, Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ)
        (.know (.indexed a ν) θ)) →
      Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ) (.know (.indexed a ν) φ) := by
    intro Γ
    induction Γ with
    | nil => intro _ _ _ h _; exact h
    | cons θ Γ ih =>
      intro hclosed hadmitted hbelow hchain hknown
      have tc : ∀ η ∈ Γ, η.Closed := fun η hη => hclosed η (List.mem_cons_of_mem _ hη)
      have ta : ∀ η ∈ Γ, η.RecordedAdmissible A E :=
        fun η hη => hadmitted η (List.mem_cons_of_mem _ hη)
      have tb : ∀ η ∈ Γ, ∀ μ ∈ η.labelSupport, μ < ν :=
        fun η hη => hbelow η (List.mem_cons_of_mem _ hη)
      have hd := deduction_cut (C := C) (R₁ := R₁) (R₂ := R₂) θ (Formula.chain Γ φ) ha
        (hclosed θ List.mem_cons_self) (Formula.chain_closed _ _ tc hc)
        (hadmitted θ List.mem_cons_self) (Formula.recordedAdmissible_chain A E Γ φ hadm ta)
        (hbelow θ List.mem_cons_self) (Formula.labelSupport_chain_below Γ φ ν target tb) hνδ
      have rest := (hd.modus_ponens hchain).modus_ponens (hknown θ List.mem_cons_self)
      exact ih tc ta tb rest (fun η hη => hknown η (List.mem_cons_of_mem _ hη))
  exact distribute c.premises closedΓ admΓ belowΓ start
    (fun θ hθ => Provable.of_axiom (prefix_cut ha (c.admitted θ hθ).1 (belowΓ θ hθ) hνδ))

theorem prefix_of_provable {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (h : Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) ν) φ)
    (hc : φ.Closed) (hadm : φ.RecordedAdmissible A E)
    (target : ∀ μ ∈ φ.labelSupport, μ < ν) (hνδ : ν < δ) :
    Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) δ) (.know (.indexed a ν) φ) := by
  obtain ⟨c⟩ := h
  exact prefix_of_certificate ha c hc hadm target hνδ

end FullRecordedAdmissions
end Alexander313

