import Alexander313.FreeVariables

/-!
# The syntactic successor instance used in modal PA induction

After numeral closure, replacing x by successor(x) literally gives the
numeral instance with x increased by one. This specific statement is valid
under the weak modal semantics. It is not an arbitrary-term substitution law.
-/

namespace Alexander313

theorem Term.substTerm_succ_subst (t : Term) (x : Nat)
    (σ : NumericalSubstitution) (n : Nat) (hx : σ x = some n) :
    (Term.substTerm x (.succ (.var x)) t).subst σ =
      t.subst (Function.update σ x (some (n + 1))) := by
  induction t with
  | var y =>
    by_cases h : y = x
    · subst y
      simp [substTerm, subst, hx, numeral]
    · simp [substTerm, subst, h]
  | zero => rfl
  | succ t ih => simp only [substTerm, subst, ih]
  | add t u iht ihu => simp only [substTerm, subst, iht, ihu]
  | mul t u iht ihu => simp only [substTerm, subst, iht, ihu]

theorem Formula.substTerm_succ_subst {Owner : Type} (φ : Formula Owner) (x : Nat)
    (σ : NumericalSubstitution) (n : Nat) (hx : σ x = some n) :
    (φ.substTerm x (.succ (.var x))).subst σ =
      φ.subst (Function.update σ x (some (n + 1))) := by
  induction φ generalizing σ with
  | falsum => rfl
  | equal t u =>
    simp only [substTerm, subst, Term.substTerm_succ_subst t x σ n hx,
      Term.substTerm_succ_subst u x σ n hx]
  | imp φ ψ ihφ ihψ => simp only [substTerm, subst, ihφ σ hx, ihψ σ hx]
  | conj φ ψ ihφ ihψ => simp only [substTerm, subst, ihφ σ hx, ihψ σ hx]
  | disj φ ψ ihφ ihψ => simp only [substTerm, subst, ihφ σ hx, ihψ σ hx]
  | neg φ ih => simp only [substTerm, subst, ih σ hx]
  | know a φ ih => simp only [substTerm, subst, ih σ hx]
  | all z φ ih =>
    by_cases hzx : z = x
    · subst z
      simp only [substTerm, ite_true, subst, NumericalSubstitution.remove_update_self]
    · have hxz : x ≠ z := Ne.symm hzx
      have hx' : σ.remove z x = some n := by
        simp [NumericalSubstitution.remove, hxz, hx]
      simp only [substTerm, if_neg hzx, subst,
        NumericalSubstitution.remove_update_of_ne σ x z _ hxz, ih (σ.remove z) hx']
  | ex z φ ih =>
    by_cases hzx : z = x
    · subst z
      simp only [substTerm, ite_true, subst, NumericalSubstitution.remove_update_self]
    · have hxz : x ≠ z := Ne.symm hzx
      have hx' : σ.remove z x = some n := by
        simp [NumericalSubstitution.remove, hxz, hx]
      simp only [substTerm, if_neg hzx, subst,
        NumericalSubstitution.remove_update_of_ne σ x z _ hxz, ih (σ.remove z) hx']

theorem Formula.close_substTerm_succ {Owner : Type} (φ : Formula Owner)
    (x : Nat) (s : Assignment) :
    (φ.substTerm x (.succ (.var x))).close s =
      φ.close (Function.update s x (s x + 1)) := by
  have hσ : Function.update (fun y => some (s y)) x (some (s x + 1)) =
      (fun y => some (Function.update s x (s x + 1) y)) := by
    funext y
    by_cases h : y = x <;> simp [h]
  simpa only [close, hσ] using
    substTerm_succ_subst φ x (fun y => some (s y)) (s x) rfl

theorem truth_substTerm_succ {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (φ : Formula Owner) (x : Nat) (s : Assignment) :
    truth filtered P (φ.substTerm x (.succ (.var x))) s ↔
      truth filtered P φ (Function.update s x (s x + 1)) := by
  calc
    truth filtered P (φ.substTerm x (.succ (.var x))) s ↔
        truth filtered P ((φ.substTerm x (.succ (.var x))).close s) s :=
      (truth_close filtered P _ s s).symm
    _ ↔ truth filtered P (φ.close (Function.update s x (s x + 1))) s := by
      rw [Formula.close_substTerm_succ]
    _ ↔ truth filtered P φ (Function.update s x (s x + 1)) := truth_close filtered P _ _ _

end Alexander313
