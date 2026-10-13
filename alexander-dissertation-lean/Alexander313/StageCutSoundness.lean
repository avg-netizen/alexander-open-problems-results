import Alexander313.RecordedStageMainColumns
import Alexander313.StageSupport
import Alexander313.OrdinalPackage

/-!
# Soundness of every actual stage cut by label-support induction

Note 26 §5: "Prove their generators true simultaneously by support, after
establishing all syntactic lemmas and collapse truth. Empty-support generators
are handled first; for label ν, all cuts below ν are then sound from
previously verified generators."

Background rows are true by the existing verification, which uses the package
reflection only at admitted contextual-collapse rows. Own prefixes are true
because their whole body precedes their label. The guarded main rows are the
only rows whose truth needs genericity; their local truth is the explicit
`mainStep` input, which may use soundness of every cut at a label of the row.
The interpretation of live heads is an arbitrary alphabetic predicate family.
These declarations belong to the checked unconditional completion chain.
-/

namespace Alexander313.RecordedStage

variable (P : OrdinalPackage) {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat)

/-- A cut is raw-sound once every generator below it is true. -/
theorem cut_sound_of_generators (Q : RawPredicates Nat) (hQ : RawAlphabetic Q)
    (b : Nat) (ν : P.Label)
    (gens : ∀ σ, FullRecordedAdmissions C A E b P.R₁ P.R₂ σ →
      (∀ μ ∈ σ.labelSupport, μ < ν) →
      ∀ s, filteredTruth (predicates C A E P.R₁ P.R₂ Q) σ s) :
    RawSound (predicates C A E P.R₁ P.R₂ Q) (.indexed b ν) := by
  intro φ s hp
  have hcut : Provable (theory C A E P.R₁ P.R₂ b ν) (φ.close s) := hp.2
  let M := filteredRealization C A E P.R₁ P.R₂ Q hQ
  have ht := provable_sound M.model hcut
    (fun θ hθ t => (M.truth_eq θ t).mpr (gens θ hθ.1 hθ.2 t)) s
  exact (truth_close true _ φ s s).mp ((M.truth_eq _ _).mp ht)

/-- Every indexed cut of the stage model is raw-sound, given local truth of
the guarded main rows from soundness of the cuts at their own labels. -/
theorem stage_sound (Q : RawPredicates Nat) (hQ : RawAlphabetic Q)
    (mainStep : ∀ a σ, RecordedMain C A E a P.R₁ P.R₂ σ →
      (∀ b, ∀ μ ∈ σ.labelSupport, RawSound (predicates C A E P.R₁ P.R₂ Q) (.indexed b μ)) →
      ∀ s, filteredTruth (predicates C A E P.R₁ P.R₂ Q) σ s) :
    ∀ b ν, RawSound (predicates C A E P.R₁ P.R₂ Q) (.indexed b ν) := by
  classical
  let Statement := Nat × Formula (RecordedHead Nat P.Label)
  let generator : Statement → Prop := fun st =>
    FullRecordedAdmissions C A E st.1 P.R₁ P.R₂ st.2
  let support : Statement → Finset P.Label := fun st => st.2.labelSupport
  let holds : Statement → Prop := fun st =>
    ∀ s, filteredTruth (predicates C A E P.R₁ P.R₂ Q) st.2 s
  -- local truth, given the generators strictly below a bound ν
  have localTruth : ∀ (ν : P.Label), CutSound support generator holds ν →
      ∀ st : Statement, generator st → (∀ x ∈ support st, x ≤ ν) → holds st := by
    intro ν cutSound st hgen hle
    obtain ⟨a, σ⟩ := st
    have lower : ∀ b, ∀ μ ∈ σ.labelSupport,
        RawSound (predicates C A E P.R₁ P.R₂ Q) (.indexed b μ) := by
      intro b μ hμ
      apply cut_sound_of_generators P C A E Q hQ b μ
      intro θ hθ below s
      exact cutSound (b, θ) hθ (fun x hx => lt_of_lt_of_le (below x hx) (hle μ hμ)) s
    change FullRecordedAdmissions C A E a P.R₁ P.R₂ σ at hgen
    cases hgen with
    | background h =>
      intro s
      exact background_truth C A E P.R₁ P.R₂ Q hQ P.reflectionLink a h s
    | main h => exact mainStep a σ h lower
    | «prefix» ν' ha h below =>
      intro s
      have hν' : ν' ≤ ν := hle ν' (Finset.mem_insert_self _ _)
      have body : ∀ t, filteredTruth (predicates C A E P.R₁ P.R₂ Q) _ t :=
        cutSound (a, _) h (fun x hx => lt_of_lt_of_le (below x hx) hν')
      exact admitted_prefix_truth C A E P.R₁ P.R₂ Q a ν' h below s (body s)
  have all : ∀ st, generator st → holds st := by
    apply finite_support_soundness P.wf support generator holds
    · intro st hgen hempty
      obtain ⟨a, σ⟩ := st
      change FullRecordedAdmissions C A E a P.R₁ P.R₂ σ at hgen
      change σ.labelSupport = ∅ at hempty
      have lower : ∀ b, ∀ μ ∈ σ.labelSupport,
          RawSound (predicates C A E P.R₁ P.R₂ Q) (.indexed b μ) := by
        intro b μ hμ
        rw [hempty] at hμ
        exact absurd hμ (Finset.notMem_empty μ)
      cases hgen with
      | background h =>
        intro s
        exact background_truth C A E P.R₁ P.R₂ Q hQ P.reflectionLink a h s
      | main h => exact mainStep a σ h lower
      | @«prefix» φ ν' ha h below =>
        have hm : ν' ∈ (Formula.know (RecordedHead.indexed a ν') φ).labelSupport :=
          Finset.mem_insert_self _ _
        rw [hempty] at hm
        exact absurd hm (Finset.notMem_empty ν')
    · intro ν cutSound st hgen _ hle
      exact localTruth ν cutSound st hgen hle
  intro b ν
  apply cut_sound_of_generators P C A E Q hQ b ν
  intro σ hσ _ s
  exact all (b, σ) hσ s

end Alexander313.RecordedStage
