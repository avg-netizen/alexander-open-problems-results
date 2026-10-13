import Alexander313.Arithmetic.Template

/-!
# Source-valid existential introduction for a particular machine code

The existential witness is the interpretation of the numeral in the
outside first-order structure. Inside the modal subformula only the
assignment to an irrelevant variable changes. The argument therefore uses
Alexander's free-independence condition, without numeral substitution or
arbitrary-term substitution underneath knowledge.
-/

namespace Alexander313

theorem generalTermEval_numeral {Owner D : Type} (M : ModalModel Owner D)
    (s t : Nat → D) (e : Nat) :
    generalTermEval M s (Term.numeral e) = generalTermEval M t (Term.numeral e) := by
  induction e with
  | zero => rfl
  | succ e ih => simpa only [Term.numeral, generalTermEval] using congrArg M.succ ih

/-- A validity of Alexander's weak base logic, rather than a theorem
    restricted to the standard natural-number interpretation. -/
theorem code_to_mechanical_valid {Owner : Type} (A : ArithmeticCoding Owner)
    (C : CoherentArithmeticCoding A) (j : Owner) (φ : UnaryFormula Owner) (e : Nat) :
    Valid (.imp (codeSentence A j φ e) (mechanicalSentence A j φ)) := by
  intro D hD M s hcode
  let w := generalTermEval M s (Term.numeral e)
  refine ⟨w, ?_⟩
  intro n
  let t := Function.update s φ.input n
  let u := Function.update (Function.update s (φ.input + 1) w) φ.input n
  have hne : φ.input + 1 ≠ φ.input := by omega
  have hmodal : M.modal j φ.body u ↔ M.modal j φ.body t := by
    apply M.free_independence
    intro v hv
    have hvx : v = φ.input := by
      simpa only [φ.freeVars_exact, Finset.mem_singleton] using hv
    subst v
    simp [u, t]
  have hmember : generalTruth M
      (A.member (.var (φ.input + 1)) (.var φ.input)) u ↔
      generalTruth M (A.member (Term.numeral e) (.var φ.input)) t := by
    rw [C.coherent, C.coherent, generalTermEval_numeral M t s e]
    simp [generalTermEval, u, t, w, hne]
  have h := hcode n
  change (M.modal j φ.body t → generalTruth M
      (A.member (Term.numeral e) (.var φ.input)) t) ∧
    (generalTruth M (A.member (Term.numeral e) (.var φ.input)) t →
      M.modal j φ.body t) at h
  change (M.modal j φ.body u → generalTruth M
      (A.member (.var (φ.input + 1)) (.var φ.input)) u) ∧
    (generalTruth M (A.member (.var (φ.input + 1)) (.var φ.input)) u →
      M.modal j φ.body u)
  exact ⟨fun hk => hmember.mpr (h.1 (hmodal.mp hk)),
    fun hm => hmodal.mpr (h.2 (hmember.mp hm))⟩

end Alexander313
