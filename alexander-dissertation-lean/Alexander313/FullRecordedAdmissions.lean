import Alexander313.RecordedMain
import Alexander313.RecordedAdmissions

/-!
# The complete literal recorded generator table

Background/contextual rows, actual guarded mechanicalness/code-image rows and
all admissible own-prefix iterations share one concrete predicate. Its source
erasure and finite-pattern preservation are proved from the actual table.
Cut collapse takes finite covering reflection as an explicit argument;
`Carlson.EffectiveCorePackage` constructs the package that supplies it.
This table alone supplies neither local truth verification nor genericity.
-/

namespace Alexander313

inductive FullRecordedAdmissions {Label : Type} [DecidableEq Label] [LT Label]
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat) (a : Nat) (R₁ R₂ : Label → Label → Prop) :
    Formula (RecordedHead Nat Label) → Prop where
  | background {φ} : RecordedBackground A E a R₁ φ →
      FullRecordedAdmissions C A E a R₁ R₂ φ
  | main {φ} : RecordedMain C A E a R₁ R₂ φ → FullRecordedAdmissions C A E a R₁ R₂ φ
  | «prefix» {φ} (ν : Label) : a ∈ A → FullRecordedAdmissions C A E a R₁ R₂ φ →
      (∀ μ ∈ φ.labelSupport, μ < ν) →
      FullRecordedAdmissions C A E a R₁ R₂ (.know (.indexed a ν) φ)

namespace FullRecordedAdmissions

variable {Label : Type} [DecidableEq Label] [LT Label]
    {R : Nat → Nat → Prop} {C : CommonCorePresentation R}
    {A E : Finset Nat} {a : Nat} {R₁ R₂ : Label → Label → Prop}

theorem closed {φ : Formula (RecordedHead Nat Label)}
    (h : FullRecordedAdmissions C A E a R₁ R₂ φ) : φ.Closed := by
  induction h with
  | background h => exact h.closed
  | main h => exact h.closed
  | «prefix» ν ha h below ih => exact ih

theorem admissible {φ : Formula (RecordedHead Nat Label)}
    (h : FullRecordedAdmissions C A E a R₁ R₂ φ) : φ.RecordedAdmissible A E := by
  induction h with
  | background h => exact h.admissible
  | main h => exact h.admissible
  | «prefix» ν ha h below ih =>
    exact (Formula.recordedAdmissible_know_indexed A E a ν _).mpr ⟨ha, ih, below⟩

theorem erased_member {φ : Formula (RecordedHead Nat Label)}
    (h : FullRecordedAdmissions C A E a R₁ R₂ φ) :
    C.family.effective.proves a φ.erase := by
  induction h with
  | background h => exact h.erased_member C
  | main h => exact h.erased_member
  | «prefix» ν ha h below ih => exact C.necessity a ih

theorem erasure_of_provable {φ : Formula (RecordedHead Nat Label)} (hφ : φ.Closed)
    (h : Provable (FullRecordedAdmissions C A E a R₁ R₂) φ) :
    C.family.effective.proves a φ.erase := by
  apply (C.family.theory_closed a φ.erase ((Formula.closed_erase φ).mpr hφ)).mp
  exact h.erasure_consequences (fun θ hθ => Provable.of_axiom hθ.erased_member)

theorem of_background_admissions {φ : Formula (RecordedHead Nat Label)}
    (h : RecordedAdmissions A E a R₁ φ) : FullRecordedAdmissions C A E a R₁ R₂ φ := by
  induction h with
  | background h => exact .background h
  | «prefix» ν ha h below ih => exact .«prefix» ν ha ih below

end FullRecordedAdmissions

namespace FullRecordedAdmissions

variable {Label : Type} [LinearOrder Label]
    {R : Nat → Nat → Prop} {C : CommonCorePresentation R}
    {A E : Finset Nat} {a : Nat} {R₁ R₂ : Label → Label → Prop}

theorem relabel (F : Finset Label) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f)
    {φ : Formula (RecordedHead Nat Label)} (h : FullRecordedAdmissions C A E a R₁ R₂ φ)
    (support : φ.labelSupport ⊆ F) : FullRecordedAdmissions C A E a R₁ R₂ (φ.relabel f) := by
  revert support
  induction h with
  | background h => intro support; exact .background (h.relabel F f pattern support)
  | main h => intro support; exact .main (h.relabel F f pattern support)
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

/-- The actual complete table discharges generator invariance. Finite expanded
    covering reflection remains an explicit argument of this general lemma. -/
theorem cut_provable_iff (C : CommonCorePresentation R) (A E : Finset Nat) (a : Nat)
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelCovering R₁ R₂ α β)
    (φ : Formula (RecordedHead Nat Label)) (target : ∀ μ ∈ φ.labelSupport, μ < α) :
    Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) α) φ ↔
      Provable (LabelCut (FullRecordedAdmissions C A E a R₁ R₂) β) φ :=
  provable_labelCut_iff (FullRecordedAdmissions C A E a R₁ R₂) R₁ R₂ hαβ reflection
    (fun F f pattern θ h support => h.relabel F f pattern support) φ target

end FullRecordedAdmissions
end Alexander313
