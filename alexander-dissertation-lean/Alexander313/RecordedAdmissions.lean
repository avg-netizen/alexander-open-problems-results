import Alexander313.RecordedBackground

/-!
# Constructed recorded background with own-prefix closure

This is the actual background/contextual subsystem of note 24, including every
finite iteration of an admissible own prefix. The guarded mechanicalness and
code-image rows are not included. Generator preservation is proved from this
literal table, not supplied as an interface. Cut collapse still requires the
separate finite expanded-pattern reflection theorem.
-/

namespace Alexander313

inductive RecordedAdmissions {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (R₁ : Label → Label → Prop) :
    Formula (RecordedHead Nat Label) → Prop where
  | background {φ} : RecordedBackground A E a R₁ φ → RecordedAdmissions A E a R₁ φ
  | «prefix» {φ} (ν : Label) : a ∈ A → RecordedAdmissions A E a R₁ φ →
      (∀ μ ∈ φ.labelSupport, μ < ν) →
      RecordedAdmissions A E a R₁ (.know (.indexed a ν) φ)

namespace RecordedAdmissions

variable {Label : Type} [DecidableEq Label] [LT Label]
    {A E : Finset Nat} {a : Nat} {R₁ : Label → Label → Prop}

theorem closed {φ : Formula (RecordedHead Nat Label)}
    (h : RecordedAdmissions A E a R₁ φ) : φ.Closed := by
  induction h with
  | background h => exact h.closed
  | «prefix» ν ha h below ih => exact ih

theorem admissible {φ : Formula (RecordedHead Nat Label)}
    (h : RecordedAdmissions A E a R₁ φ) : φ.RecordedAdmissible A E := by
  induction h with
  | background h => exact h.admissible
  | «prefix» ν ha h below ih =>
    exact (Formula.recordedAdmissible_know_indexed A E a ν _).mpr ⟨ha, ih, below⟩

theorem erased_member {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    {φ : Formula (RecordedHead Nat Label)} (h : RecordedAdmissions A E a R₁ φ) :
    C.family.effective.proves a φ.erase := by
  induction h with
  | background h => exact h.erased_member C
  | «prefix» ν ha h below ih => exact C.necessity a ih

theorem erasure_of_provable {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    {φ : Formula (RecordedHead Nat Label)} (hφ : φ.Closed)
    (h : Provable (RecordedAdmissions A E a R₁) φ) :
    C.family.effective.proves a φ.erase := by
  apply (C.family.theory_closed a φ.erase ((Formula.closed_erase φ).mpr hφ)).mp
  exact h.erasure_consequences (fun θ hθ => Provable.of_axiom (hθ.erased_member C))

end RecordedAdmissions

namespace RecordedAdmissions

variable {Label : Type} [LinearOrder Label]
    {A E : Finset Nat} {a : Nat} {R₁ R₂ : Label → Label → Prop}

theorem relabel (F : Finset Label) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f)
    {φ : Formula (RecordedHead Nat Label)} (h : RecordedAdmissions A E a R₁ φ)
    (support : φ.labelSupport ⊆ F) : RecordedAdmissions A E a R₁ (φ.relabel f) := by
  revert support
  induction h with
  | background h =>
    intro support
    exact .background (h.relabel F f pattern support)
  | @«prefix» φ ν ha h below ih =>
    intro support
    have hν : ν ∈ F := support (Finset.mem_insert_self _ _)
    have inner : φ.labelSupport ⊆ F := fun μ hμ => support (Finset.mem_insert_of_mem hμ)
    refine .«prefix» (f ν) ha (ih inner) ?_
    intro μ hμ
    change μ ∈ (φ.relabel f).labelSupport at hμ
    rw [Formula.labelSupport_relabel] at hμ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hμ
    exact (pattern.2.1 η (inner hη) ν hν).mpr (below η hη)

/-- Generator invariance is discharged for this constructed subsystem. The
    ordinal finite-pattern reflection input remains explicit and unfinished. -/
theorem cut_provable_iff (A E : Finset Nat) (a : Nat)
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelCovering R₁ R₂ α β)
    (φ : Formula (RecordedHead Nat Label))
    (target : ∀ μ ∈ φ.labelSupport, μ < α) :
    Provable (LabelCut (RecordedAdmissions A E a R₁) α) φ ↔
      Provable (LabelCut (RecordedAdmissions A E a R₁) β) φ :=
  provable_labelCut_iff (RecordedAdmissions A E a R₁) R₁ R₂ hαβ reflection
    (fun F f pattern θ h support => h.relabel F f pattern support) φ target

end RecordedAdmissions
end Alexander313
