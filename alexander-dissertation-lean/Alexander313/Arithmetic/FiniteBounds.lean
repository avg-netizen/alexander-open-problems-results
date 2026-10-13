import Alexander313.Arithmetic.UniversalExecution

/-!
# Finite numeral bounds in arbitrary PA structures

One explicit PA induction instance proves that every domain element is
zero or a successor. With successor separation/injectivity and the
addition recurrences, an element below a fixed numeral must equal one
of that numeral's finitely many standard predecessors. No standardness
of the entire arithmetic domain is assumed.
-/

namespace Alexander313

structure FiniteArithmetic {Owner D : Type} (M : ModalModel Owner D) : Prop
    extends ArithmeticRecurrences M where
  successor_ne_zero : ∀ a, M.succ a ≠ M.zero
  successor_injective : Function.Injective M.succ
  zero_or_successor : ∀ a, a = M.zero ∨ ∃ b, a = M.succ b

namespace FiniteArithmetic

theorem below_numeral {Owner D : Type} {M : ModalModel Owner D}
    (h : FiniteArithmetic M) (N : Nat) (a z : D)
    (heq : numeralValue M N = M.add a (M.succ z)) :
    ∃ m, m < N ∧ a = numeralValue M m := by
  induction N generalizing a z with
  | zero =>
    have hz : M.succ (M.add a z) = M.zero := by
      simpa only [numeralValue_zero, h.add_succ] using heq.symm
    exact False.elim (h.successor_ne_zero _ hz)
  | succ N ih =>
    have hprev : numeralValue M N = M.add a z :=
      h.successor_injective (by simpa only [numeralValue_succ, h.add_succ] using heq)
    rcases h.zero_or_successor z with hz | ⟨w, hz⟩
    · rw [hz, h.add_zero] at hprev
      exact ⟨N, Nat.lt_succ_self N, hprev.symm⟩
    · rw [hz] at hprev
      obtain ⟨m, hm, ha⟩ := ih a w hprev
      exact ⟨m, Nat.lt_succ_of_lt hm, ha⟩

end FiniteArithmetic

def predecessorBody (Owner : Type) : Formula Owner :=
  .disj (.equal (.var 0) .zero) (.ex 1 (.equal (.var 0) (.succ (.var 1))))

def predecessorInduction (Owner : Type) : Formula Owner :=
  Formula.universalClosure (.imp
    ((predecessorBody Owner).subst (fun y => if y = 0 then some 0 else none))
    (.imp (.all 0 (.imp (predecessorBody Owner)
      ((predecessorBody Owner).substTerm 0 (.succ (.var 0)))))
      (.all 0 (predecessorBody Owner))))

theorem predecessorInduction_pa (Owner : Type) : PAInstance Owner (predecessorInduction Owner) :=
  PAInstance.induction (predecessorBody Owner) 0

theorem predecessorInduction_model {Owner D : Type} (M : ModalModel Owner D)
    (s : Nat → D) (h : generalTruth M (predecessorInduction Owner) s) :
    ∀ a, a = M.zero ∨ ∃ b, a = M.succ b := by
  have hi :
      (M.zero = M.zero ∨ ∃ b, M.zero = M.succ b) →
      (∀ a, (a = M.zero ∨ ∃ b, a = M.succ b) →
        (M.succ a = M.zero ∨ ∃ b, M.succ a = M.succ b)) →
      ∀ a, a = M.zero ∨ ∃ b, a = M.succ b := by
    simpa [predecessorInduction, predecessorBody, Formula.universalClosure,
      Formula.subst, Term.subst, NumericalSubstitution.remove, Term.numeral,
      Formula.substTerm, Term.substTerm, Formula.freeVars, Term.freeVars,
      generalTruth, generalTermEval, Function.update_apply,
      Finset.erase_insert_of_ne, Finset.erase_singleton] using h
  exact hi (Or.inl rfl) (fun a _ => Or.inr ⟨a, rfl⟩)

def successorSeparation (Owner : Type) : Formula Owner :=
  .all 0 (.neg (.equal (.succ (.var 0)) .zero))

def successorInjectivity (Owner : Type) : Formula Owner :=
  .all 0 (.all 1 (.imp (.equal (.succ (.var 0)) (.succ (.var 1)))
    (.equal (.var 0) (.var 1))))

def finiteArithmeticAxioms (Owner : Type) : List (Formula Owner) :=
  recurrenceAxioms Owner ++
    [successorSeparation Owner, successorInjectivity Owner, predecessorInduction Owner]

theorem finiteArithmeticAxioms_pa {Owner : Type} (φ : Formula Owner)
    (hφ : φ ∈ finiteArithmeticAxioms Owner) : PAInstance Owner φ := by
  rcases List.mem_append.mp hφ with hφ | hφ
  · exact recurrenceAxioms_pa φ hφ
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact PAInstance.successor_ne_zero
    · exact PAInstance.successor_injective
    · exact predecessorInduction_pa Owner

theorem finiteArithmeticAxioms_model {Owner D : Type} (M : ModalModel Owner D)
    (s : Nat → D) (h : ∀ φ ∈ finiteArithmeticAxioms Owner, generalTruth M φ s) :
    FiniteArithmetic M := by
  have hrec := recurrenceAxioms_model M s (fun φ hφ =>
    h φ (List.mem_append_left _ hφ))
  have hsep := h (successorSeparation Owner) (by simp [finiteArithmeticAxioms])
  have hinj := h (successorInjectivity Owner) (by simp [finiteArithmeticAxioms])
  have hind := h (predecessorInduction Owner) (by simp [finiteArithmeticAxioms])
  exact {
    toArithmeticRecurrences := hrec
    successor_ne_zero := by
      simpa [successorSeparation, generalTruth, generalTermEval] using hsep
    successor_injective := by
      simpa [successorInjectivity, generalTruth, generalTermEval, Function.Injective] using hinj
    zero_or_successor := predecessorInduction_model M s hind }

def numeralAssignment {Owner D : Type} (M : ModalModel Owner D) (s : Assignment) : Nat → D :=
  fun x => numeralValue M (s x)

theorem numeralAssignment_update {Owner D : Type} (M : ModalModel Owner D)
    (s : Assignment) (x n : Nat) :
    numeralAssignment M (Function.update s x n) =
      Function.update (numeralAssignment M s) x (numeralValue M n) := by
  funext v
  by_cases h : v = x <;> simp [numeralAssignment, h]

namespace ArithmeticGraphs

theorem existsVariables_positive {Owner : Type} (xs : List Nat) (φ : Formula Owner)
    (hφ : φ.PositiveExistential) : (existsVariables xs φ).PositiveExistential := by
  induction xs <;> simp_all [existsVariables, Formula.PositiveExistential]

def sequenceRecordBody (Owner : Type) : Formula Owner :=
  existsVariables [10, 11, 12, 13, 14]
    (.conj (beta Owner (.var 2) (.var 3) (.var 9) (.var 14))
      (.conj (record Owner (.var 10) (.var 11) (.var 12) (.var 13) (.var 14))
        ((localExecution Owner).renameVariables executionPorts)))

theorem sequenceRecordBody_positive (Owner : Type) :
    (sequenceRecordBody Owner).PositiveExistential :=
  existsVariables_positive _ _ ⟨beta_positive _ _ _ _ _,
    ⟨record_positive _ _ _ _ _ _, (localExecution Owner).positiveExistential_renameVariables
      (localExecution_positive Owner) _⟩⟩

theorem sequenceExecution_numeral_transfer {Owner D : Type}
    (M : ModalModel Owner D) (hM : FiniteArithmetic M) (s : Assignment)
    (h : truth false (fun _ _ => False) (sequenceExecution Owner) s) :
    generalTruth M (sequenceExecution Owner) (numeralAssignment M s) := by
  change ∀ d, generalTruth M (less Owner (.var 9) (.var 4))
      (Function.update (numeralAssignment M s) 9 d) →
    generalTruth M (sequenceRecordBody Owner) (Function.update (numeralAssignment M s) 9 d)
  intro d hless
  have hbound : ∃ z, numeralValue M (s 4) = M.add d (M.succ z) := by
    simpa [less, Term.termsBound, Term.variableBound, generalTruth, generalTermEval,
      numeralAssignment, Function.update_apply] using hless
  obtain ⟨z, hz⟩ := hbound
  obtain ⟨m, hm, rfl⟩ := hM.below_numeral (s 4) d z hz
  have hstandard : truth false (fun _ _ => False) (sequenceRecordBody Owner)
      (Function.update s 9 m) := by
    apply h m
    apply (less_truth false (fun _ _ => False) (.var 9) (.var 4) _).mpr
    simpa [Term.eval, Function.update_apply] using hm
  have ht := positiveExistential_numeral_transfer M hM.toArithmeticRecurrences
    (sequenceRecordBody Owner) (sequenceRecordBody_positive Owner) (Function.update s 9 m) hstandard
  change generalTruth M (sequenceRecordBody Owner)
    (numeralAssignment M (Function.update s 9 m)) at ht
  simpa only [numeralAssignment_update] using ht

theorem existsVariables_numeral_transfer {Owner D : Type}
    (M : ModalModel Owner D) (xs : List Nat) (φ : Formula Owner)
    (hφ : ∀ s, truth false (fun _ _ => False) φ s →
      generalTruth M φ (numeralAssignment M s)) :
    ∀ s, truth false (fun _ _ => False) (existsVariables xs φ) s →
      generalTruth M (existsVariables xs φ) (numeralAssignment M s) := by
  induction xs with
  | nil => exact hφ
  | cons x xs ih =>
    intro s h
    obtain ⟨n, hn⟩ := h
    refine ⟨numeralValue M n, ?_⟩
    simpa only [← numeralAssignment_update] using ih (Function.update s x n) hn

theorem universalExecution_numeral_transfer {Owner D : Type}
    (M : ModalModel Owner D) (hM : FiniteArithmetic M) (s : Assignment)
    (h : truth false (fun _ _ => False) (universalExecution Owner) s) :
    generalTruth M (universalExecution Owner) (numeralAssignment M s) := by
  apply existsVariables_numeral_transfer M [2, 3, 4, 5, 6, 7, 8] _ _ s h
  intro t ht
  exact ⟨positiveExistential_numeral_transfer M hM.toArithmeticRecurrences _
      (less_positive _ _ _) t ht.1,
    ⟨positiveExistential_numeral_transfer M hM.toArithmeticRecurrences _
      (beta_positive _ _ _ _ _) t ht.2.1,
      ⟨positiveExistential_numeral_transfer M hM.toArithmeticRecurrences _
        (record_positive _ _ _ _ _ _) t ht.2.2.1,
        sequenceExecution_numeral_transfer M hM t ht.2.2.2⟩⟩⟩

end ArithmeticGraphs

/-- Actual finite PA certification of each accepted universal computation.
    The finite bounded universal prefix is valid in every model of the
    seven displayed PA premises, including nonstandard models. -/
theorem canonicalArithmeticCoding_pa {Owner : Type} (e n : Nat) (hW : W e n) :
    Provable (PAInstance Owner)
      ((canonicalArithmeticCoding Owner).member (Term.numeral e) (Term.numeral n)) := by
  refine ⟨{
    premises := finiteArithmeticAxioms Owner
    admitted := fun φ hφ => finiteArithmeticAxioms_pa φ hφ
    validity := ?_ }⟩
  intro D hD M t
  apply chain_intro
  intro hΓ
  have hM := finiteArithmeticAxioms_model M t hΓ
  apply ((universalExecutionTemplate Owner).member_coherent M (Term.numeral e)
    (Term.numeral n) t).mpr
  rw [generalTermEval_numeralValue, generalTermEval_numeralValue]
  let s : Assignment := fun v => if v = 0 then e else if v = 1 then n else 0
  have hs : truth false (fun (_ : Owner) _ => False)
      (ArithmeticGraphs.universalExecution Owner) s := by
    apply (ArithmeticGraphs.universalExecution_truth false (fun _ _ => False) s).mpr
    simpa [s] using hW
  have ht := ArithmeticGraphs.universalExecution_numeral_transfer M hM s hs
  change generalTruth M (ArithmeticGraphs.universalExecution Owner)
    (fun v => if v = 0 then numeralValue M e else if v = 1 then numeralValue M n else M.zero)
  have hassign : numeralAssignment M s =
      (fun v => if v = 0 then numeralValue M e else if v = 1 then numeralValue M n else M.zero) := by
    funext v
    by_cases hv0 : v = 0
    · simp [numeralAssignment, s, hv0]
    · by_cases hv1 : v = 1 <;> simp [numeralAssignment, s, hv0, hv1]
  simpa only [hassign] using ht

end Alexander313
