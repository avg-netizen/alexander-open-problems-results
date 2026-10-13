import Alexander313.RecordedStageContexts

/-!
# Background truth and literal own prefixes in the actual stage model

PA, assigned validity, own validity, deduction, introspection and reflection
are verified from the real cut consequence predicates and admission rules.
Contextual truth uses the explicit ordinal order/finite-reflection input.
All admissible background prefix iterations and their finite consequences are
then true in the constructed full-stage filtered model.

The interpretation still uses the full table's actual indexed cuts, including
guarded main rows. Truth of those mechanicalness/code rows, retained active
query recovery and full cut soundness are separate obligations; they are not
assumed or obtained from source erasure here.
-/

namespace Alexander313.RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

theorem validity_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (φ : Formula (RecordedHead Nat Label)) (hv : Valid φ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) φ s :=
  ((filteredRealization C A E R₁ R₂ P hP).truth_eq φ s).mp
    (hv Nat inferInstance (filteredRealization C A E R₁ R₂ P hP).model s)

@[simp] theorem indexed_know_iff (P : RawPredicates Nat) (a : Nat) (ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) (.know (.indexed a ν) φ) s ↔
      Provable (theory C A E R₁ R₂ a ν) (φ.close s) ∧
        filteredTruth (predicates C A E R₁ R₂ P) φ s := by
  change (cuts C A E R₁ R₂ a ν (φ.close s) ∧
    filteredTruth (predicates C A E R₁ R₂ P) φ s) ↔ _
  rw [cuts_query]

theorem own_validity_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (a : Nat) (ν : Label) (φ : Formula (RecordedHead Nat Label)) (hv : Valid φ)
    (hadm : (Formula.know (.indexed a ν) φ).RecordedAdmissible A E) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      (Formula.universalClosure (.know (.indexed a ν) φ)) s := by
  obtain ⟨ha, hφ, below⟩ := (Formula.recordedAdmissible_know_indexed A E a ν φ).mp hadm
  apply truth_universalClosure true _ _ _ s
  intro t
  exact ⟨cuts_assigned_validity C A E R₁ R₂ a ν φ t hv hφ below,
    validity_truth C A E R₁ R₂ P hP φ hv t⟩

theorem deduction_truth (P : RawPredicates Nat) (a : Nat) (ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) (Formula.indexedDeduction a ν φ ψ) s :=
  truth_universalClosure true _ _
    (filtered_deduction (predicates C A E R₁ R₂ P) (.indexed a ν)
      (fun θ η hi hp => cuts_modus_ponens C A E R₁ R₂ a ν θ η hi hp) φ ψ) s

theorem introspection_truth (P : RawPredicates Nat) (a : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (hμν : μ < ν)
    (hadm : (Formula.indexedIntrospection a μ ν φ).RecordedAdmissible A E)
    (s : Assignment) : filteredTruth (predicates C A E R₁ R₂ P)
      (Formula.indexedIntrospection a μ ν φ) s := by
  have ha := (Formula.recordedAdmissible_universalClosure A E _).mp hadm
  have pair := (Formula.recordedAdmissible_imp_iff A E _ _).mp ha
  obtain ⟨active, hφ, below⟩ :=
    (Formula.recordedAdmissible_know_indexed A E a μ φ).mp pair.1
  apply truth_universalClosure true _ _ _ s
  intro t hp
  have hclosedAdm : (φ.close t).RecordedAdmissible A E :=
    (Formula.recordedAdmissible_close A E φ t).mpr hφ
  have hclosedBelow : ∀ ξ ∈ (φ.close t).labelSupport, ξ < μ := by
    simpa only [Formula.labelSupport_close] using below
  have hprefix := cuts_prefix C A E R₁ R₂ a active hp.1 hclosedAdm hclosedBelow hμν
  exact ⟨hprefix, hp⟩

/-- The only ordinal input used by background truth is the actual order link
and finite reflection at each admitted contextual-collapse relation. -/
theorem background_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (reflection : ∀ μ ν, R₁ μ ν → μ ≤ ν ∧ FiniteLabelCovering R₁ R₂ μ ν)
    (a : Nat) {σ : Formula (RecordedHead Nat Label)}
    (h : RecordedBackground A E a R₁ σ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) σ s := by
  cases h with
  | arithmetic hp hadm => exact truth_pa_instance true _ hp s
  | assigned φ t hv hadm =>
    exact filtered_assigned_validity _ (filteredRealization C A E R₁ R₂ P hP) φ hv t s
  | own_validity ν φ hv hadm =>
    exact own_validity_truth C A E R₁ R₂ P hP a ν φ hv
      ((Formula.recordedAdmissible_universalClosure A E _).mp hadm) s
  | deduction ν φ ψ hadm => exact deduction_truth C A E R₁ R₂ P a ν φ ψ s
  | introspection μ ν φ hμν hadm =>
    exact introspection_truth C A E R₁ R₂ P a μ ν φ hμν hadm s
  | reflection b φ hadm => exact filtered_reflection _ b φ s
  | contextual c b μ ν φ hR hadm =>
    have hi := reflection μ ν hR
    exact contextualCollapse_truth C A E R₁ R₂ P c b μ ν φ hR hi.1 hi.2 hadm s

/-- Raw prefix membership is derived from the actual lower admission. Only
truth of that displayed body is needed to conclude its filtered prefix. -/
theorem admitted_prefix_truth (P : RawPredicates Nat) (a : Nat) (ν : Label)
    {φ : Formula (RecordedHead Nat Label)} (h : FullRecordedAdmissions C A E a R₁ R₂ φ)
    (below : ∀ μ ∈ φ.labelSupport, μ < ν) (s : Assignment)
    (ht : filteredTruth (predicates C A E R₁ R₂ P) φ s) :
    filteredTruth (predicates C A E R₁ R₂ P) (.know (.indexed a ν) φ) s := by
  have hp : cuts C A E R₁ R₂ a ν (φ.close s) := by
    rw [Formula.close_eq_self_of_closed φ h.closed s]
    exact cuts_of_admission C A E R₁ R₂ a ν h below
  exact ⟨hp, ht⟩

theorem backgroundAdmissions_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (reflection : ∀ μ ν, R₁ μ ν → μ ≤ ν ∧ FiniteLabelCovering R₁ R₂ μ ν)
    (a : Nat) {σ : Formula (RecordedHead Nat Label)}
    (h : RecordedAdmissions A E a R₁ σ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) σ s := by
  induction h with
  | background h => exact background_truth C A E R₁ R₂ P hP reflection a h s
  | «prefix» ν active h below ih =>
    exact admitted_prefix_truth C A E R₁ R₂ P a ν
      (FullRecordedAdmissions.of_background_admissions h) below s ih

theorem background_consequence_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (reflection : ∀ μ ν, R₁ μ ν → μ ≤ ν ∧ FiniteLabelCovering R₁ R₂ μ ν)
    (a : Nat) {φ : Formula (RecordedHead Nat Label)}
    (hp : Provable (RecordedAdmissions A E a R₁) φ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) φ s := by
  apply ((filteredRealization C A E R₁ R₂ P hP).truth_eq φ s).mp
  apply provable_sound (filteredRealization C A E R₁ R₂ P hP).model hp
  intro θ hθ t
  exact ((filteredRealization C A E R₁ R₂ P hP).truth_eq θ t).mpr
    (backgroundAdmissions_truth C A E R₁ R₂ P hP reflection a hθ t)

theorem source_background_truth
    (reflection : ∀ μ ν, R₁ μ ν → μ ≤ ν ∧ FiniteLabelCovering R₁ R₂ μ ν)
    (a : Nat) {σ : Formula (RecordedHead Nat Label)}
    (h : RecordedBackground A E a R₁ σ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves) σ s :=
  background_truth C A E R₁ R₂ _ C.family.rawAlphabetic reflection a h s

theorem source_backgroundAdmissions_truth
    (reflection : ∀ μ ν, R₁ μ ν → μ ≤ ν ∧ FiniteLabelCovering R₁ R₂ μ ν)
    (a : Nat) {σ : Formula (RecordedHead Nat Label)}
    (h : RecordedAdmissions A E a R₁ σ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves) σ s :=
  backgroundAdmissions_truth C A E R₁ R₂ _ C.family.rawAlphabetic reflection a h s

end Alexander313.RecordedStage
