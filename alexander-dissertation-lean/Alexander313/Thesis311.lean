import Alexander313.Specification
import Alexander313.Alexander.FilteredModel
import Alexander313.Background
import Alexander313.ProofClosure
import Alexander313.SourceColumns
import Alexander313.SourceModels

/-!
# The well-founded soundness assembly for 3-1-1

This proves the hand proof's induction and finite-prefix argument. An
unconditional theorem still requires constructing the effective source
theories and arithmetic coding. Compiled columns, admissible models,
generator prefixes and background truth are derived from the remaining
presentation, rather than supplied as source inputs.
-/

namespace Alexander313

inductive BackgroundGenerator (i : Nat) : Formula Nat → Prop where
  | arithmetic {φ} : PAInstance Nat φ → BackgroundGenerator i φ
  | assigned (φ : Formula Nat) (s : Assignment) : Valid φ →
      BackgroundGenerator i (φ.close s)
  | structural {φ} : StructuralInstance i φ → BackgroundGenerator i φ
  | reflection (j : Nat) (φ : Formula Nat) : BackgroundGenerator i (reflection j φ)

structure SourceInputs311 (R : Nat → Nat → Prop) where
  arithmetic : ArithmeticCoding Nat
  family : MachineFamily
  generators : Nat → Formula Nat → Prop
  generators_exact : ∀ i σ, generators i σ ↔
    BackgroundGenerator i σ ∨ ∃ j φ, R j i ∧
      σ = codeSentence arithmetic j φ (family.unaryColumnIndex j φ)
  proofs : ∀ i θ, θ.Closed → (family.effective.proves i θ ↔
    Provable (PrefixedAxioms i (generators i)) θ)

noncomputable def SourceInputs311.index {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) : Nat → UnaryFormula Nat → Nat :=
  C.family.unaryColumnIndex

theorem SourceInputs311.columns {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (j : Nat) (φ : UnaryFormula Nat) (s : Assignment) :
    W (C.index j φ) (s φ.input) ↔ C.family.effective.proves j (φ.body.close s) :=
  C.family.unaryColumn_equation j φ s

def SourceInputs311.realization {R : Nat → Nat → Prop} (C : SourceInputs311 R) :
    FilteredRealization C.family.effective.proves :=
  C.family.filteredRealization

theorem BackgroundGenerator.closed {i : Nat} {σ : Formula Nat}
    (hσ : BackgroundGenerator i σ) : σ.Closed := by
  cases hσ with
  | arithmetic h => exact h.closed
  | assigned φ s h => exact φ.close_closed s
  | structural h => exact h.closed
  | reflection j φ => exact Formula.universalClosure_closed _

theorem SourceInputs311.background_admitted {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {σ : Formula Nat}
    (hσ : BackgroundGenerator i σ) : C.generators i σ :=
  (C.generators_exact i σ).mpr (Or.inl hσ)

theorem SourceInputs311.generators_closed {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {σ : Formula Nat}
    (hσ : C.generators i σ) : σ.Closed := by
  rcases (C.generators_exact i σ).mp hσ with hbg | ⟨j, φ, hji, rfl⟩
  · exact hbg.closed
  · exact codeSentence_closed C.arithmetic j φ (C.index j φ)

theorem SourceInputs311.prefixes {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) (σ : Formula Nat)
    (hσ : C.generators i σ) (n : Nat) (s : Assignment) :
    C.family.effective.proves i ((Formula.«prefix» i n σ).close s) := by
  have hc : (Formula.«prefix» i n σ).Closed := by
    simpa only [Formula.Closed, Formula.freeVars_prefix] using C.generators_closed i hσ
  apply (C.proofs i _ ((Formula.«prefix» i n σ).close_closed s)).mpr
  rw [Formula.close_eq_self_of_closed _ hc]
  exact Provable.of_axiom ⟨σ, n, hσ, rfl⟩

theorem SourceInputs311.background_member {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {σ : Formula Nat}
    (hσ : BackgroundGenerator i σ) : C.family.effective.proves i σ := by
  have hp := C.prefixes i σ (C.background_admitted i hσ) 0 (fun _ => 0)
  simpa only [Formula.«prefix», Formula.close_eq_self_of_closed σ hσ.closed] using hp

theorem SourceInputs311.prefixed_closed {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {θ : Formula Nat}
    (hθ : PrefixedAxioms i (C.generators i) θ) : θ.Closed := by
  obtain ⟨σ, n, hσ, rfl⟩ := hθ
  simpa only [Formula.Closed, Formula.freeVars_prefix] using C.generators_closed i hσ

theorem SourceInputs311.prefixed_known {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {θ : Formula Nat}
    (hθ : PrefixedAxioms i (C.generators i) θ) :
    C.family.effective.proves i (.know i θ) := by
  obtain ⟨σ, n, hσ, rfl⟩ := hθ
  have hc : (Formula.«prefix» i (n + 1) σ).Closed := by
    simpa only [Formula.Closed, Formula.freeVars_prefix] using C.generators_closed i hσ
  have hp := C.prefixes i σ hσ (n + 1) (fun _ => 0)
  rw [Formula.close_eq_self_of_closed _ hc] at hp
  exact hp

theorem SourceInputs311.necessity {R : Nat → Nat → Prop} (C : SourceInputs311 R)
    (i : Nat) {φ : Formula Nat} (hp : C.family.effective.proves i φ) :
    C.family.effective.proves i (.know i φ) := by
  have hc := C.family.sentences i φ hp
  obtain ⟨c⟩ := (C.proofs i φ hc).mp hp
  apply C.family.knowledge_of_certificate i c hc
    (fun θ hθ => C.prefixed_closed i hθ) (fun θ hθ => C.prefixed_known i hθ)
  · intro θ hv hθ
    have hk : (Formula.know i θ).Closed := hθ
    have hm := C.background_member i (BackgroundGenerator.structural
      (StructuralInstance.validity θ hv))
    simpa only [Formula.universalClosure_eq_self_of_closed _ hk] using hm
  · intro θ η hθ hη
    have hfθ : θ.freeVars = ∅ := hθ
    have hfη : η.freeVars = ∅ := hη
    have hk : (Formula.imp (.know i (.imp θ η))
        (.imp (.know i θ) (.know i η))).Closed := by
      simp [Formula.Closed, Formula.freeVars, hfθ, hfη]
    have hm := C.background_member i (BackgroundGenerator.structural
      (StructuralInstance.reasoning θ η))
    simpa only [Formula.universalClosure_eq_self_of_closed _ hk] using hm

/-- No source soundness hypothesis: PA, validity, reasoning, introspection
    and every agent's reflection hold already in the filtered structure. -/
theorem SourceInputs311.background_true {R : Nat → Nat → Prop}
    (C : SourceInputs311 R) (i : Nat) {σ : Formula Nat}
    (hσ : BackgroundGenerator i σ) (s : Assignment) :
    filteredTruth C.family.effective.proves σ s := by
  cases hσ with
  | arithmetic h => exact truth_pa_instance true C.family.effective.proves h s
  | assigned φ t h => exact filtered_assigned_validity _ C.realization φ h t s
  | structural h =>
    apply filtered_structural _ C.realization i _ _ _ h s
    · intro φ hv t
      exact C.background_member i (.assigned φ t hv)
    · intro φ ψ himp hφ
      exact C.family.modus_ponens i himp hφ
    · intro φ hp
      exact C.necessity i hp
  | reflection j φ => exact filtered_reflection _ j φ s

theorem source_inputs311_sound (R : Nat → Nat → Prop) (wf : WellFounded R)
    (C : SourceInputs311 R) : ∀ i, RawSound C.family.effective.proves i := by
  intro i
  induction i using wf.induction with
  | h i ih =>
    apply sound_of_true_generators C.family.effective.proves C.realization i
      (C.generators i) (C.prefixes i) (C.proofs i)
    intro σ hσ s
    rcases (C.generators_exact i σ).mp hσ with hbg | ⟨j, φ, hji, rfl⟩
    · exact C.background_true i hbg s
    · apply (codeSentence_truth C.arithmetic C.family.effective.proves true j φ
        (C.index j φ) s).mpr
      intro n
      change filteredTruth C.family.effective.proves (.know j φ.body)
        (Function.update s φ.input n) ↔ W (C.index j φ) n
      rw [filtered_know_iff C.family.effective.proves (ih j hji)]
      simpa only [Function.update_self] using
        (C.columns j φ (Function.update s φ.input n)).symm

/-- Verifies these actual target schemas from the same fixed source
    construction, rather than assuming their membership a second time.
    Known subordinate mechanicalness still needs the source base-logic
    existential-introduction proof for the constructed arithmetic template. -/
theorem source_inputs311_schemas (R : Nat → Nat → Prop) (wf : WellFounded R)
    (C : SourceInputs311 R) :
    satisfiesEA C.family ∧ knowsTruth C.family ∧
      knowsParticularCodes C.arithmetic C.family R := by
  have sound := source_inputs311_sound R wf C
  have admitted : ∀ i σ, BackgroundGenerator i σ → C.generators i σ := by
    intro i σ hσ
    exact (C.generators_exact i σ).mpr (Or.inl hσ)
  have hea : satisfiesEA C.family := by
    intro i φ hφ s
    apply (filtered_eq_actual C.family.effective.proves sound φ s).mp
    cases hφ with
    | structural hσ => exact C.background_true i (.structural hσ) s
    | known_structural hσ =>
      exact filtered_prefix C.family.effective.proves i _ s
        (fun n => C.prefixes i _ (admitted i _ (.structural hσ)) n s)
        (C.background_true i (.structural hσ) s) 1
    | truth ψ => exact C.background_true i (.reflection i ψ) s
    | arithmetic hσ => exact C.background_true i (.arithmetic hσ) s
    | known_arithmetic hσ =>
      exact filtered_prefix C.family.effective.proves i _ s
        (fun n => C.prefixes i _ (admitted i _ (.arithmetic hσ)) n s)
        (C.background_true i (.arithmetic hσ) s) 1
  have ht : knowsTruth C.family := by
    intro i j φ s
    exact ⟨C.prefixes i _ (admitted i _ (.reflection j φ)) 0 s, trivial⟩
  have hc : knowsParticularCodes C.arithmetic C.family R := by
    intro i j hji φ
    refine ⟨C.index j φ, fun s => ?_⟩
    have hgen := (C.generators_exact i _).mpr
      (Or.inr ⟨j, φ, hji, rfl⟩)
    exact ⟨C.prefixes i _ hgen 0 s, trivial⟩
  exact ⟨hea, ht, hc⟩

end Alexander313
