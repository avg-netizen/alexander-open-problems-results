import Alexander313.Arithmetic.PositiveCertificates
import Alexander313.Alexander.AlphaClosure
import Alexander313.Alexander.VariableOpening
import Mathlib.Data.Set.Finite.Basic

/-!
# Arithmetic numeral instances and weak modal universal elimination

Arithmetic formulas admit literal numeral substitution in every arbitrary
domain. Modal universal elimination is proved using only capture-safe
variable substitution; the numerical instance is taken afterwards. This
does not assert arbitrary-term substitution under a modal operator.
-/

namespace Alexander313

def generalNumericalOverride {Owner D : Type} (M : ModalModel Owner D)
    (σ : NumericalSubstitution) (s : Nat → D) : Nat → D :=
  fun x => match σ x with
    | none => s x
    | some n => numeralValue M n

theorem generalNumericalOverride_remove_update {Owner D : Type}
    (M : ModalModel Owner D) (σ : NumericalSubstitution) (s : Nat → D)
    (x : Nat) (d : D) :
    generalNumericalOverride M (σ.remove x) (Function.update s x d) =
      Function.update (generalNumericalOverride M σ s) x d := by
  funext v
  by_cases hv : v = x
  · subst v
    simp [generalNumericalOverride, NumericalSubstitution.remove]
  · simp only [generalNumericalOverride, NumericalSubstitution.remove, if_neg hv,
      Function.update_of_ne hv]

theorem generalTermEval_numericalSubst {Owner D : Type} (M : ModalModel Owner D)
    (t : Term) (σ : NumericalSubstitution) (s : Nat → D) :
    generalTermEval M s (t.subst σ) =
      generalTermEval M (generalNumericalOverride M σ s) t := by
  induction t with
  | var x =>
    cases h : σ x <;>
      simp [Term.subst, generalTermEval, generalNumericalOverride, h,
        generalTermEval_numeralValue]
  | zero => rfl
  | succ t ih => simp only [Term.subst, generalTermEval, ih]
  | add t u iht ihu => simp only [Term.subst, generalTermEval, iht, ihu]
  | mul t u iht ihu => simp only [Term.subst, generalTermEval, iht, ihu]

theorem arithmeticTruth_numericalSubst {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (σ : NumericalSubstitution) (s : Nat → D)
    (hφ : φ.Arithmetic) :
    generalTruth M (φ.subst σ) s ↔
      generalTruth M φ (generalNumericalOverride M σ s) := by
  induction φ generalizing σ s with
  | falsum => rfl
  | equal t u =>
    simp only [Formula.subst, generalTruth, generalTermEval_numericalSubst]
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ σ s hφ.1) (ihψ σ s hφ.2)
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ σ s hφ.1) (ihψ σ s hφ.2)
  | disj φ ψ ihφ ihψ =>
    exact or_congr (ihφ σ s hφ.1) (ihψ σ s hφ.2)
  | neg φ ih => exact not_congr (ih σ s hφ)
  | all x φ ih =>
    simp only [Formula.subst, generalTruth]
    apply forall_congr'
    intro d
    simpa only [generalNumericalOverride_remove_update] using
      ih (σ.remove x) (Function.update s x d) hφ
  | ex x φ ih =>
    simp only [Formula.subst, generalTruth]
    apply exists_congr
    intro d
    simpa only [generalNumericalOverride_remove_update] using
      ih (σ.remove x) (Function.update s x d) hφ
  | know a φ ih => exact False.elim hφ

theorem arithmeticTruth_numericalClose {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (hφ : φ.Arithmetic) (s : Assignment) (t : Nat → D) :
    generalTruth M (φ.close s) t ↔
      generalTruth M φ (fun x => numeralValue M (s x)) :=
  arithmeticTruth_numericalSubst M φ (fun x => some (s x)) t hφ

/-- Coherence identifies a closed arithmetic query with the literal query
    having the same two numeral values, even in a nonstandard domain. -/
theorem arithmetic_member_close_valid {Owner : Type} (A : ArithmeticCoding Owner)
    (C : CoherentArithmeticCoding A) (e x n : Nat) (s : Assignment)
    (hx : s x = n) :
    Valid (.iff ((A.member (Term.numeral e) (.var x)).close s)
      (A.member (Term.numeral e) (Term.numeral n))) := by
  intro D hD M t
  have hleft := (arithmeticTruth_numericalClose M
    (A.member (Term.numeral e) (.var x)) (A.arithmetic _ _) s t).trans
      (C.coherent M (Term.numeral e) (.var x) (fun v => numeralValue M (s v)))
  have hright := C.coherent M (Term.numeral e) (Term.numeral n) t
  have h : generalTruth M ((A.member (Term.numeral e) (.var x)).close s) t ↔
      generalTruth M (A.member (Term.numeral e) (Term.numeral n)) t := by
    simp only [generalTermEval_numeralValue, generalTermEval, hx] at hleft hright
    exact hleft.trans hright.symm
  exact ⟨h.mp, h.mpr⟩

theorem valid_all_variable_instance {Owner : Type} (φ : Formula Owner) (x y : Nat)
    (h : φ.VarSubstitutable x y) : Valid (.imp (.all x φ) (φ.substVar x y)) := by
  intro D hD M s hall
  exact (generalTruth_substVar M φ x y s h).mpr (hall (s y))

/-- Assigned Validity is enough to instantiate a modal universal at a
    numeral. The chosen fresh variable occurs only in the valid source
    formula, before its numerical closure is admitted. -/
theorem MachineFamily.all_numerical_instance (F : MachineFamily) (i x : Nat)
    (φ : Formula Nat) (s : Assignment) (n : Nat)
    (assigned : ∀ θ t, Valid θ → F.effective.proves i (θ.close t))
    (hp : F.effective.proves i ((Formula.all x φ).close s)) :
    F.effective.proves i (φ.close (Function.update s x n)) := by
  obtain ⟨y, hy⟩ := (φ.boundVars ∪ φ.freeVars).exists_notMem
  have hybound : y ∉ φ.boundVars := fun h => hy (Finset.mem_union_left _ h)
  have hyfree : y ∉ φ.freeVars := fun h => hy (Finset.mem_union_right _ h)
  have hsub := φ.varSubstitutable_of_notMem_boundVars x y hybound
  let t := Function.update s y n
  have ht : t y = n := Function.update_self y n s
  have hinst := assigned (.imp (.all x φ) (φ.substVar x y)) t
    (valid_all_variable_instance φ x y hsub)
  have hall : (Formula.all x φ).close t = (Formula.all x φ).close s := by
    apply Formula.close_eq_of_agree
    intro v hv
    have hvy : v ≠ y := by
      intro heq
      subst v
      exact hyfree (Finset.mem_erase.mp hv).2
    exact Function.update_of_ne hvy n s
  have hresult : F.effective.proves i ((φ.substVar x y).close t) :=
    F.modus_ponens i (by
      change F.effective.proves i
        (.imp ((Formula.all x φ).close t) ((φ.substVar x y).close t)) at hinst
      simpa only [hall] using hinst) hp
  rw [Formula.close_substVar φ x y t hsub] at hresult
  have htarget : φ.close (Function.update t x (t y)) =
      φ.close (Function.update s x n) := by
    apply Formula.close_eq_of_agree
    intro v hv
    by_cases hvx : v = x
    · subst v
      simp only [Function.update_self, ht]
    · have hvy : v ≠ y := by
        intro heq
        subst v
        exact hyfree hv
      simp only [Function.update_of_ne hvx, t, Function.update_of_ne hvy]
  simpa only [htarget] using hresult

end Alexander313
