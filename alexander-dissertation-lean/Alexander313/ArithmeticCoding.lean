import Alexander313.Computability

/-!
# The required arithmetic representation of program domains

This contract must be *constructed*. It is not a new global axiom, and
there is no supplied instance. In particular the original modal language
has not been extended with a primitive halting predicate.
-/

namespace Alexander313

def Formula.Arithmetic {Owner : Type} : Formula Owner → Prop
  | .falsum => True
  | .equal _ _ => True
  | .imp φ ψ => φ.Arithmetic ∧ ψ.Arithmetic
  | .conj φ ψ => φ.Arithmetic ∧ ψ.Arithmetic
  | .disj φ ψ => φ.Arithmetic ∧ ψ.Arithmetic
  | .neg φ => φ.Arithmetic
  | .all _ φ => φ.Arithmetic
  | .ex _ φ => φ.Arithmetic
  | .know _ _ => False

structure ArithmeticCoding (Owner : Type) where
  member : Term → Term → Formula Owner
  arithmetic : ∀ e x, (member e x).Arithmetic
  «variables» : ∀ e x, (member e x).freeVars ⊆ e.freeVars ∪ x.freeVars
  correct : ∀ e x (P : RawPredicates Owner) filtered s,
    truth filtered P (member e x) s ↔ W (e.eval s) (x.eval s)

def codeSentence {Owner : Type} (A : ArithmeticCoding Owner) (j : Owner)
    (φ : UnaryFormula Owner) (e : Nat) : Formula Owner :=
  .all φ.input (Formula.iff (.know j φ.body)
    (A.member (Term.numeral e) (.var φ.input)))

def mechanicalSentence {Owner : Type} (A : ArithmeticCoding Owner) (j : Owner)
    (φ : UnaryFormula Owner) : Formula Owner :=
  .ex (φ.input + 1) (.all φ.input (Formula.iff (.know j φ.body)
    (A.member (.var (φ.input + 1)) (.var φ.input))))

theorem codeSentence_closed {Owner : Type} (A : ArithmeticCoding Owner)
    (j : Owner) (φ : UnaryFormula Owner) (e : Nat) : (codeSentence A j φ e).Closed := by
  have hm : (A.member (Term.numeral e) (.var φ.input)).freeVars ⊆ {φ.input} := by
    simpa only [Term.freeVars_numeral, Term.freeVars, Finset.empty_union] using
      A.variables (Term.numeral e) (.var φ.input)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hb := Finset.mem_erase.mp hv
  have hbody : v ∈ φ.body.freeVars → v = φ.input := by
    intro h
    simpa only [φ.freeVars_exact, Finset.mem_singleton] using h
  have hmember : v ∈ (A.member (Term.numeral e) (.var φ.input)).freeVars →
      v = φ.input := fun h => Finset.mem_singleton.mp (hm h)
  have hh := hb.2
  simp only [Formula.iff, Formula.freeVars, Finset.mem_union] at hh
  rcases hh with (h | h) | (h | h)
  · exact hb.1 (hbody h)
  · exact hb.1 (hmember h)
  · exact hb.1 (hmember h)
  · exact hb.1 (hbody h)

theorem mechanicalSentence_closed {Owner : Type} (A : ArithmeticCoding Owner)
    (j : Owner) (φ : UnaryFormula Owner) : (mechanicalSentence A j φ).Closed := by
  have hm : (A.member (.var (φ.input + 1)) (.var φ.input)).freeVars ⊆
      {φ.input + 1} ∪ {φ.input} := A.variables _ _
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hf := Finset.mem_erase.mp hv
  have hx := Finset.mem_erase.mp hf.2
  have hbody : v ∈ φ.body.freeVars → False := by
    intro h
    exact hx.1 (by simpa only [φ.freeVars_exact, Finset.mem_singleton] using h)
  have hmember : v ∈ (A.member (.var (φ.input + 1)) (.var φ.input)).freeVars → False := by
    intro h
    rcases Finset.mem_union.mp (hm h) with h | h
    · exact hf.1 (Finset.mem_singleton.mp h)
    · exact hx.1 (Finset.mem_singleton.mp h)
  have hh := hx.2
  simp only [Formula.iff, Formula.freeVars, Finset.mem_union] at hh
  rcases hh with (h | h) | (h | h)
  · exact hbody h
  · exact hmember h
  · exact hmember h
  · exact hbody h

theorem codeSentence_truth {Owner : Type} (A : ArithmeticCoding Owner)
    (P : RawPredicates Owner) (filtered : Bool) (j : Owner)
    (φ : UnaryFormula Owner) (e : Nat) (s : Assignment) :
    truth filtered P (codeSentence A j φ e) s ↔
      ∀ n, (truth filtered P (.know j φ.body) (Function.update s φ.input n) ↔ W e n) := by
  simp only [codeSentence, Formula.iff, truth]
  apply forall_congr'
  intro n
  rw [A.correct]
  simp only [Term.eval, Term.eval_numeral, Function.update_self]
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · intro h
    exact ⟨h.mp, h.mpr⟩

end Alexander313
