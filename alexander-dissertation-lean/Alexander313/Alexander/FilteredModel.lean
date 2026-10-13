import Alexander313.Alexander.BaseLogic
import Alexander313.FreeVariables

namespace Alexander313

/-- Source lemma 1.2.22 must provide this object for the source proof
    predicates. It does not assume any predicate soundness. -/
structure FilteredRealization {Owner : Type} (P : RawPredicates Owner) where
  model : ModalModel Owner Nat
  zero_correct : model.zero = 0
  succ_correct : ∀ n, model.succ n = n + 1
  add_correct : ∀ m n, model.add m n = m + n
  mul_correct : ∀ m n, model.mul m n = m * n
  modal_correct : ∀ a φ s, model.modal a φ s ↔ filteredTruth P (.know a φ) s

theorem FilteredRealization.term_eval {Owner : Type} {P : RawPredicates Owner}
    (M : FilteredRealization P) (t : Term) (s : Assignment) :
    generalTermEval M.model s t = t.eval s := by
  induction t with
  | var x => rfl
  | zero => exact M.zero_correct
  | succ t ih => simp only [generalTermEval, Term.eval, M.succ_correct, ih]
  | add t u iht ihu => simp only [generalTermEval, Term.eval, M.add_correct, iht, ihu]
  | mul t u iht ihu => simp only [generalTermEval, Term.eval, M.mul_correct, iht, ihu]

theorem FilteredRealization.truth_eq {Owner : Type} {P : RawPredicates Owner}
    (M : FilteredRealization P) (φ : Formula Owner) (s : Assignment) :
    generalTruth M.model φ s ↔ filteredTruth P φ s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => simp only [generalTruth, truth, M.term_eval]
  | imp φ ψ ihφ ihψ => simp only [generalTruth, truth, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [generalTruth, truth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [generalTruth, truth, ihφ, ihψ]
  | neg φ ih => exact not_congr (ih s)
  | all x φ ih => exact forall_congr' fun n => ih (Function.update s x n)
  | ex x φ ih => exact exists_congr fun n => ih (Function.update s x n)
  | know a φ _ => exact M.modal_correct a φ s

def FilteredRealization.toActual {Owner : Type} {P : RawPredicates Owner}
    (M : FilteredRealization P) (sound : ∀ a, RawSound P a) : ActualRealization P where
  model := M.model
  zero_correct := M.zero_correct
  succ_correct := M.succ_correct
  add_correct := M.add_correct
  mul_correct := M.mul_correct
  modal_correct := fun a φ s => (M.modal_correct a φ s).trans
    (filtered_eq_actual P sound (.know a φ) s)

def PrefixedAxioms {Owner : Type} (a : Owner) (generators : Formula Owner → Prop)
    (θ : Formula Owner) : Prop :=
  ∃ σ n, generators σ ∧ θ = Formula.«prefix» a n σ

/-- This is the finite-prefix/consequence part of the 3-1-1 soundness
    argument. It is also used by the core extension reduction. -/
theorem sound_of_true_generators {Owner : Type} (P : RawPredicates Owner)
    (M : FilteredRealization P) (a : Owner) (generators : Formula Owner → Prop)
    (membership : ∀ σ, generators σ → ∀ n s,
      P a ((Formula.«prefix» a n σ).close s))
    (proofs : ∀ θ, θ.Closed → (P a θ ↔ Provable (PrefixedAxioms a generators) θ))
    (hgen : ∀ σ, generators σ → ∀ s, filteredTruth P σ s) : RawSound P a := by
  intro φ s hp
  have hax : ∀ θ, PrefixedAxioms a generators θ →
      ∀ t, generalTruth M.model θ t := by
    intro θ hθ t
    rcases hθ with ⟨σ, n, hσ, rfl⟩
    apply (M.truth_eq _ _).mpr
    exact filtered_prefix P a σ t (fun k => membership σ hσ k t) (hgen σ hσ t) n
  have ht := provable_sound M.model ((proofs _ (φ.close_closed s)).mp hp) hax s
  exact (truth_close true P φ s s).mp ((M.truth_eq _ _).mp ht)

end Alexander313
