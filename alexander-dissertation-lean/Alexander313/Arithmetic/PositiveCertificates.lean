import Alexander313.ProofClosure
import Alexander313.Arithmetic.Template

/-!
# PA certificates for finite positive arithmetic computations

Only the four defining equations for addition and multiplication are used.
Every true positive existential arithmetic numeral instance has a finite
Alexander-base-logic certificate from these PA axioms. Existential witnesses
are the interpretations of actual numerals; there is no appeal to a standard
model assumption, modal term substitution, or an unproved PA-completeness
package.

This covers finite pairing and beta-entry certificates. It is not a proof
that the universal computation trace has already been arithmetized.
-/

namespace Alexander313

def numeralValue {Owner D : Type} (M : ModalModel Owner D) : Nat → D
  | 0 => M.zero
  | n + 1 => M.succ (numeralValue M n)

@[simp] theorem numeralValue_zero {Owner D : Type} (M : ModalModel Owner D) :
    numeralValue M 0 = M.zero := rfl

@[simp] theorem numeralValue_succ {Owner D : Type} (M : ModalModel Owner D) (n : Nat) :
    numeralValue M (n + 1) = M.succ (numeralValue M n) := rfl

theorem generalTermEval_numeralValue {Owner D : Type} (M : ModalModel Owner D)
    (s : Nat → D) (n : Nat) :
    generalTermEval M s (Term.numeral n) = numeralValue M n := by
  induction n <;> simp_all [Term.numeral, generalTermEval, numeralValue]

structure ArithmeticRecurrences {Owner D : Type} (M : ModalModel Owner D) : Prop where
  add_zero : ∀ a, M.add a M.zero = a
  add_succ : ∀ a b, M.add a (M.succ b) = M.succ (M.add a b)
  mul_zero : ∀ a, M.mul a M.zero = M.zero
  mul_succ : ∀ a b, M.mul a (M.succ b) = M.add (M.mul a b) a

namespace ArithmeticRecurrences

theorem add_numeral {Owner D : Type} {M : ModalModel Owner D}
    (h : ArithmeticRecurrences M) (a b : Nat) :
    M.add (numeralValue M a) (numeralValue M b) = numeralValue M (a + b) := by
  induction b with
  | zero => simpa only [numeralValue_zero, Nat.add_zero] using h.add_zero (numeralValue M a)
  | succ b ih => simp only [Nat.add_succ, numeralValue_succ, h.add_succ, ih]

theorem mul_numeral {Owner D : Type} {M : ModalModel Owner D}
    (h : ArithmeticRecurrences M) (a b : Nat) :
    M.mul (numeralValue M a) (numeralValue M b) = numeralValue M (a * b) := by
  induction b with
  | zero => simpa only [numeralValue_zero, Nat.mul_zero] using h.mul_zero (numeralValue M a)
  | succ b ih =>
    simp only [Nat.mul_succ, numeralValue_succ, h.mul_succ, ih, h.add_numeral]

theorem term_value {Owner D : Type} {M : ModalModel Owner D}
    (h : ArithmeticRecurrences M) (t : Term) (s : Assignment) :
    generalTermEval M (fun v => numeralValue M (s v)) t = numeralValue M (t.eval s) := by
  induction t with
  | var x => rfl
  | zero => rfl
  | succ t ih => simp only [generalTermEval, Term.eval, numeralValue_succ, ih]
  | add t u iht ihu => simp only [generalTermEval, Term.eval, iht, ihu, h.add_numeral]
  | mul t u iht ihu => simp only [generalTermEval, Term.eval, iht, ihu, h.mul_numeral]

end ArithmeticRecurrences

namespace Formula

def PositiveExistential {Owner : Type} : Formula Owner → Prop
  | .equal _ _ => True
  | .conj φ ψ => φ.PositiveExistential ∧ ψ.PositiveExistential
  | .disj φ ψ => φ.PositiveExistential ∧ ψ.PositiveExistential
  | .ex _ φ => φ.PositiveExistential
  | _ => False

theorem positiveExistential_arithmetic {Owner : Type} (φ : Formula Owner)
    (h : φ.PositiveExistential) : φ.Arithmetic := by
  induction φ <;> simp_all [PositiveExistential, Arithmetic]

theorem positiveExistential_subst {Owner : Type} (φ : Formula Owner)
    (h : φ.PositiveExistential) (σ : NumericalSubstitution) :
    (φ.subst σ).PositiveExistential := by
  induction φ generalizing σ <;> simp_all [PositiveExistential, subst]

end Formula

/-- A true finite witness in the natural-number interpretation remains
    true when every value is replaced by its numeral in a PA recurrence
    model. No injectivity or standardness of those numerals is required. -/
theorem positiveExistential_numeral_transfer {Owner D : Type}
    (M : ModalModel Owner D) (hM : ArithmeticRecurrences M)
    (φ : Formula Owner) (hφ : φ.PositiveExistential) (s : Assignment)
    (h : truth false (fun _ _ => False) φ s) :
    generalTruth M φ (fun v => numeralValue M (s v)) := by
  induction φ generalizing s with
  | falsum => exact False.elim hφ
  | equal t u =>
    change generalTermEval M _ t = generalTermEval M _ u
    rw [hM.term_value, hM.term_value]
    exact congrArg (numeralValue M) h
  | imp φ ψ ihφ ihψ => exact False.elim hφ
  | conj φ ψ ihφ ihψ => exact ⟨ihφ hφ.1 s h.1, ihψ hφ.2 s h.2⟩
  | disj φ ψ ihφ ihψ =>
    rcases h with h | h
    · exact Or.inl (ihφ hφ.1 s h)
    · exact Or.inr (ihψ hφ.2 s h)
  | neg φ ih => exact False.elim hφ
  | all x φ ih => exact False.elim hφ
  | ex x φ ih =>
    obtain ⟨n, hn⟩ := h
    refine ⟨numeralValue M n, ?_⟩
    have hs : (fun v => numeralValue M ((Function.update s x n) v)) =
        Function.update (fun v => numeralValue M (s v)) x (numeralValue M n) := by
      funext v
      by_cases hv : v = x <;> simp [hv]
    simpa only [hs] using ih hφ (Function.update s x n) hn
  | know a φ ih => exact False.elim hφ

def recurrenceAxioms (Owner : Type) : List (Formula Owner) := [
  .all 0 (.equal (.add (.var 0) .zero) (.var 0)),
  .all 0 (.all 1 (.equal (.add (.var 0) (.succ (.var 1)))
    (.succ (.add (.var 0) (.var 1))))),
  .all 0 (.equal (.mul (.var 0) .zero) .zero),
  .all 0 (.all 1 (.equal (.mul (.var 0) (.succ (.var 1)))
    (.add (.mul (.var 0) (.var 1)) (.var 0))))]

theorem recurrenceAxioms_pa {Owner : Type} (φ : Formula Owner)
    (hφ : φ ∈ recurrenceAxioms Owner) : PAInstance Owner φ := by
  simp only [recurrenceAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl
  · exact PAInstance.add_zero
  · exact PAInstance.add_succ
  · exact PAInstance.mul_zero
  · exact PAInstance.mul_succ

theorem recurrenceAxioms_model {Owner D : Type} (M : ModalModel Owner D)
    (s : Nat → D) (h : ∀ φ ∈ recurrenceAxioms Owner, generalTruth M φ s) :
    ArithmeticRecurrences M := by
  have h0 := h (.all 0 (.equal (.add (.var 0) .zero) (.var 0)))
    (by simp [recurrenceAxioms])
  have h1 := h (.all 0 (.all 1 (.equal (.add (.var 0) (.succ (.var 1)))
    (.succ (.add (.var 0) (.var 1)))))) (by simp [recurrenceAxioms])
  have h2 := h (.all 0 (.equal (.mul (.var 0) .zero) .zero))
    (by simp [recurrenceAxioms])
  have h3 := h (.all 0 (.all 1 (.equal (.mul (.var 0) (.succ (.var 1)))
    (.add (.mul (.var 0) (.var 1)) (.var 0))))) (by simp [recurrenceAxioms])
  exact {
    add_zero := by simpa [generalTruth, generalTermEval] using h0
    add_succ := by simpa [generalTruth, generalTermEval] using h1
    mul_zero := by simpa [generalTruth, generalTermEval] using h2
    mul_succ := by simpa [generalTruth, generalTermEval] using h3 }

/-- A real finite base-logic certificate from PA for every true positive
    existential arithmetic numeral instance. -/
theorem pa_proves_positive_numeral_instance {Owner : Type} (φ : Formula Owner)
    (hφ : φ.PositiveExistential) (s : Assignment)
    (h : truth false (fun _ _ => False) φ s) :
    Provable (PAInstance Owner) (φ.close s) := by
  refine ⟨{
    premises := recurrenceAxioms Owner
    admitted := fun θ hθ => recurrenceAxioms_pa θ hθ
    validity := ?_ }⟩
  intro D hD M t
  apply chain_intro
  intro hΓ
  have hM := recurrenceAxioms_model M t hΓ
  have hclose : truth false (fun _ _ => False) (φ.close s) (fun _ => 0) :=
    (truth_close false (fun _ _ => False) φ s (fun _ => 0)).mpr h
  have ht := positiveExistential_numeral_transfer M hM (φ.close s)
    (φ.positiveExistential_subst hφ (fun v => some (s v))) (fun _ => 0) hclose
  apply (generalTruth_eq_of_agree M (φ.close s)
    (fun _ => numeralValue M 0) t ?_).mp ht
  intro v hv
  have hc := φ.close_closed s
  rw [hc] at hv
  simp at hv

end Alexander313
