import Alexander313.RecordedAdmissions

/-!
# Derived prefixes of literal finite recorded consequences

For a certificate below ν, its own prefix at ν is derivable in every cut δ
with ν < δ. The proof admits the prefix of each actual premise, the own-prefix
of the certificate's actual valid implication chain, and literal same-label
deduction instances. It does not assume unrestricted necessitation or validity
of an erased recorded formula. This module treats the constructed background
subsystem; the guarded main rows remain unfinished.
-/

namespace Alexander313
namespace Formula

@[simp] theorem labelSupport_indexedDeduction {Label : Type} [DecidableEq Label]
    (a : Nat) (ν : Label) (φ ψ : Formula (RecordedHead Nat Label)) :
    (indexedDeduction a ν φ ψ).labelSupport = insert ν (φ.labelSupport ∪ ψ.labelSupport) := by
  simp [indexedDeduction, labelSupport, Finset.union_assoc, Finset.union_comm,
    Finset.union_left_comm]

theorem indexedDeduction_admissible {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (ν : Label) (φ ψ : Formula (RecordedHead Nat Label))
    (ha : a ∈ A) (hφ : φ.RecordedAdmissible A E) (hψ : ψ.RecordedAdmissible A E)
    (belowφ : ∀ μ ∈ φ.labelSupport, μ < ν) (belowψ : ∀ μ ∈ ψ.labelSupport, μ < ν) :
    (indexedDeduction a ν φ ψ).RecordedAdmissible A E := by
  have hi : (Formula.imp φ ψ).RecordedAdmissible A E :=
    ⟨⟨hφ.1, hψ.1⟩, hφ.2, hψ.2⟩
  have hki := (recordedAdmissible_know_indexed A E a ν (.imp φ ψ)).mpr
    ⟨ha, hi, fun μ hμ => (Finset.mem_union.mp hμ).elim (belowφ μ) (belowψ μ)⟩
  have hkφ := (recordedAdmissible_know_indexed A E a ν φ).mpr ⟨ha, hφ, belowφ⟩
  have hkψ := (recordedAdmissible_know_indexed A E a ν ψ).mpr ⟨ha, hψ, belowψ⟩
  apply (recordedAdmissible_universalClosure A E _).mpr
  exact ⟨⟨hki.1, hkφ.1, hkψ.1⟩, hki.2, hkφ.2, hkψ.2⟩

theorem indexedDeduction_eq_of_closed {Label : Type} (a : Nat) (ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) (hφ : φ.Closed) (hψ : ψ.Closed) :
    indexedDeduction a ν φ ψ =
      .imp (.know (.indexed a ν) (.imp φ ψ))
        (.imp (.know (.indexed a ν) φ) (.know (.indexed a ν) ψ)) := by
  apply universalClosure_eq_self_of_closed
  simp_all [Closed, freeVars]

end Formula
namespace RecordedAdmissions

variable {Label : Type} [LinearOrder Label] {A E : Finset Nat} {a : Nat}
    {R₁ : Label → Label → Prop} {ν δ : Label}

theorem prefix_cut {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (h : RecordedAdmissions A E a R₁ φ) (below : ∀ μ ∈ φ.labelSupport, μ < ν)
    (hνδ : ν < δ) :
    LabelCut (RecordedAdmissions A E a R₁) δ (.know (.indexed a ν) φ) := by
  refine ⟨.«prefix» ν ha h below, ?_⟩
  intro μ hμ
  rcases Finset.mem_insert.mp hμ with rfl | hμ
  · exact hνδ
  · exact lt_trans (below μ hμ) hνδ

theorem own_validity_cut {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (hv : Valid φ) (hc : φ.Closed) (hadm : φ.RecordedAdmissible A E)
    (below : ∀ μ ∈ φ.labelSupport, μ < ν) (hνδ : ν < δ) :
    Provable (LabelCut (RecordedAdmissions A E a R₁) δ) (.know (.indexed a ν) φ) := by
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
    (hνδ : ν < δ) : Provable (LabelCut (RecordedAdmissions A E a R₁) δ)
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

/-- Note 24 §4's finite-consequence prefix lemma on the actual constructed
    subsystem. Its proof uses only the finite premises and exact chain. -/
theorem prefix_of_certificate {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (c : Certificate (LabelCut (RecordedAdmissions A E a R₁) ν) φ)
    (hc : φ.Closed) (hadm : φ.RecordedAdmissible A E)
    (target : ∀ μ ∈ φ.labelSupport, μ < ν) (hνδ : ν < δ) :
    Provable (LabelCut (RecordedAdmissions A E a R₁) δ) (.know (.indexed a ν) φ) := by
  have closedΓ : ∀ θ ∈ c.premises, θ.Closed := fun θ hθ => (c.admitted θ hθ).1.closed
  have admΓ : ∀ θ ∈ c.premises, θ.RecordedAdmissible A E :=
    fun θ hθ => (c.admitted θ hθ).1.admissible
  have belowΓ : ∀ θ ∈ c.premises, ∀ μ ∈ θ.labelSupport, μ < ν :=
    fun θ hθ => (c.admitted θ hθ).2
  have start : Provable (LabelCut (RecordedAdmissions A E a R₁) δ)
      (.know (.indexed a ν) (Formula.chain c.premises φ)) :=
    own_validity_cut ha c.validity (Formula.chain_closed _ _ closedΓ hc)
      (Formula.recordedAdmissible_chain A E _ φ hadm admΓ)
      (Formula.labelSupport_chain_below _ φ ν target belowΓ) hνδ
  have distribute : ∀ Γ : List (Formula (RecordedHead Nat Label)),
      (∀ θ ∈ Γ, θ.Closed) → (∀ θ ∈ Γ, θ.RecordedAdmissible A E) →
      (∀ θ ∈ Γ, ∀ μ ∈ θ.labelSupport, μ < ν) →
      Provable (LabelCut (RecordedAdmissions A E a R₁) δ)
        (.know (.indexed a ν) (Formula.chain Γ φ)) →
      (∀ θ ∈ Γ, Provable (LabelCut (RecordedAdmissions A E a R₁) δ)
        (.know (.indexed a ν) θ)) →
      Provable (LabelCut (RecordedAdmissions A E a R₁) δ) (.know (.indexed a ν) φ) := by
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
      have hd := deduction_cut (R₁ := R₁) θ (Formula.chain Γ φ) ha
        (hclosed θ List.mem_cons_self) (Formula.chain_closed _ _ tc hc)
        (hadmitted θ List.mem_cons_self) (Formula.recordedAdmissible_chain A E Γ φ hadm ta)
        (hbelow θ List.mem_cons_self) (Formula.labelSupport_chain_below Γ φ ν target tb) hνδ
      have rest := (hd.modus_ponens hchain).modus_ponens (hknown θ List.mem_cons_self)
      exact ih tc ta tb rest (fun η hη => hknown η (List.mem_cons_of_mem _ hη))
  exact distribute c.premises closedΓ admΓ belowΓ start
    (fun θ hθ => Provable.of_axiom (prefix_cut ha (c.admitted θ hθ).1 (belowΓ θ hθ) hνδ))

theorem prefix_of_provable {φ : Formula (RecordedHead Nat Label)} (ha : a ∈ A)
    (h : Provable (LabelCut (RecordedAdmissions A E a R₁) ν) φ)
    (hc : φ.Closed) (hadm : φ.RecordedAdmissible A E)
    (target : ∀ μ ∈ φ.labelSupport, μ < ν) (hνδ : ν < δ) :
    Provable (LabelCut (RecordedAdmissions A E a R₁) δ) (.know (.indexed a ν) φ) := by
  obtain ⟨c⟩ := h
  exact prefix_of_certificate ha c hc hadm target hνδ

end RecordedAdmissions
end Alexander313
