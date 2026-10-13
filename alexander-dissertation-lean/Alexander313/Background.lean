import Alexander313.Quantifiers
import Alexander313.SuccessorSubstitution
import Alexander313.Alexander.FilteredModel

/-!
# Background arithmetic and structural axioms

PA (including induction over arbitrary modal formulas) and filtered
reflection are verified without any source predicate soundness assumption.
Validity uses an admissible filtered realization; deduction and introspection
use explicit raw closure properties, discharged syntactically in Thesis311.
-/

namespace Alexander313

theorem PAInstance.closed {Owner : Type} {φ : Formula Owner}
    (hφ : PAInstance Owner φ) : φ.Closed := by
  cases hφ with
  | induction ψ x => exact Formula.universalClosure_closed _
  | successor_ne_zero => simp [Formula.Closed, Formula.freeVars, Term.freeVars]
  | successor_injective =>
    change (({0, 1} : Finset Nat).erase 1).erase 0 = ∅
    decide
  | add_zero => simp [Formula.Closed, Formula.freeVars, Term.freeVars]
  | add_succ =>
    change (({0, 1} : Finset Nat).erase 1).erase 0 = ∅
    decide
  | mul_zero => simp [Formula.Closed, Formula.freeVars, Term.freeVars]
  | mul_succ => simp [Formula.Closed, Formula.freeVars, Term.freeVars]

theorem StructuralInstance.closed {Owner : Type} {i : Owner} {φ : Formula Owner}
    (hφ : StructuralInstance i φ) : φ.Closed := by
  cases hφ <;> exact Formula.universalClosure_closed _

theorem truth_pa_instance {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    {φ : Formula Owner} (hφ : PAInstance Owner φ) (s : Assignment) :
    truth filtered P φ s := by
  cases hφ with
  | successor_ne_zero => simp [truth, Term.eval]
  | successor_injective => simp [truth, Term.eval]
  | add_zero => simp [truth, Term.eval]
  | add_succ => simp [truth, Term.eval, Nat.add_assoc]
  | mul_zero => simp [truth, Term.eval]
  | mul_succ => simp [truth, Term.eval, Nat.mul_succ]
  | induction ψ x =>
    apply truth_universalClosure filtered P _ _ s
    intro t hbase hstep n
    let σ : NumericalSubstitution := fun y => if y = x then some 0 else none
    have hσ : σ.override t = Function.update t x 0 := by
      funext y
      by_cases h : y = x <;> simp [σ, NumericalSubstitution.override, h]
    have hz : truth filtered P ψ (Function.update t x 0) := by
      simpa only [hσ] using (truth_subst filtered P ψ σ t).mp hbase
    have hn : ∀ m, truth filtered P ψ (Function.update t x m) := by
      intro m
      induction m with
      | zero => exact hz
      | succ m ih =>
        have hnext := (truth_substTerm_succ filtered P ψ x
          (Function.update t x m)).mp (hstep m ih)
        simpa only [Function.update_self, Function.update_idem] using hnext
    exact hn n

theorem filtered_assigned_validity {Owner : Type} (P : RawPredicates Owner)
    (M : FilteredRealization P) (φ : Formula Owner) (hφ : Valid φ)
    (s t : Assignment) : filteredTruth P (φ.close s) t := by
  apply (truth_close true P φ s t).mpr
  exact (M.truth_eq φ s).mp (hφ Nat inferInstance M.model s)

theorem filtered_structural {Owner : Type} (P : RawPredicates Owner)
    (M : FilteredRealization P) (i : Owner)
    (assigned : ∀ φ, Valid φ → ∀ s, P i (φ.close s))
    (mp : ∀ φ ψ, P i (.imp φ ψ) → P i φ → P i ψ)
    (necessity : ∀ φ, P i φ → P i (.know i φ))
    {σ : Formula Owner} (hσ : StructuralInstance i σ) (s : Assignment) :
    filteredTruth P σ s := by
  cases hσ with
  | validity φ hφ =>
    apply truth_universalClosure true P _ _ s
    intro t
    exact ⟨assigned φ hφ t, (M.truth_eq φ t).mp (hφ Nat inferInstance M.model t)⟩
  | reasoning φ ψ =>
    exact truth_universalClosure true P _ (filtered_deduction P i mp φ ψ) s
  | introspection φ =>
    exact truth_universalClosure true P _ (filtered_introspection P i necessity φ) s

end Alexander313
