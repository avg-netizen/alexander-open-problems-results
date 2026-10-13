import Alexander313.Alexander.DeltaEncoding
import Alexander313.Alexander.SourceLabelFormation
import Mathlib.Tactic.FinCases

/-!
# Effective symbols of the actual Δ language

A relation symbol stores an owner and an actual source formula; its arity is
the computed cardinality of that formula's free variables. The sigma type of
all relation symbols is therefore equivalent to the concrete product of
owners and formulas. These instances retain those literal product codes.
-/

namespace Alexander313.Delta

noncomputable instance relationPrimcodable (n : Nat) : Primcodable (Relation Nat n) :=
  Primcodable.subtype
    (Primrec.eq.comp (Formula.freeVariableCard_primrec.comp Primrec.snd)
      (Primrec.const n))

def relationSigmaEquiv : (Σ n, Relation Nat n) ≃ Nat × Formula Nat where
  toFun := fun r => r.2.val
  invFun := fun q => ⟨q.2.freeVars.card, ⟨q, rfl⟩⟩
  left_inv := by
    rintro ⟨n, ⟨q, hq⟩⟩
    cases hq
    rfl
  right_inv := fun _ => rfl

noncomputable instance relationSigmaPrimcodable : Primcodable (Σ n, Relation Nat n) :=
  Primcodable.ofEquiv (Nat × Formula Nat) relationSigmaEquiv

/- The generic sigma encoder would store the already determined arity again.
   Select the encoder belonging to the displayed primitive coding instead. -/
noncomputable instance (priority := 1100) relationSigmaEncodable :
    Encodable (Σ n, Relation Nat n) := relationSigmaPrimcodable.toEncodable

@[simp] theorem relation_encode (n : Nat) (r : Relation Nat n) :
    Encodable.encode r = Nat.pair r.val.1 (r.val.2.code id) := rfl

@[simp] theorem relationSigma_encode (r : Σ n, Relation Nat n) :
    Encodable.encode r = Nat.pair r.2.val.1 (r.2.val.2.code id) := rfl

theorem relationSigma_label_primrec : Primrec relationSigmaEquiv :=
  Primrec.of_equiv

theorem relationSigma_arity_primrec : Primrec (fun r : Σ n, Relation Nat n => r.1) := by
  have h := Formula.freeVariableCard_primrec.comp
    (Primrec.snd.comp relationSigma_label_primrec)
  exact h.of_eq (fun r => r.2.property)

def arithmeticSigmaEquiv : (Σ n, ArithmeticSymbol n) ≃ Fin 4 where
  toFun := fun r => match r with
    | ⟨_, .zero⟩ => 0
    | ⟨_, .succ⟩ => 1
    | ⟨_, .add⟩ => 2
    | ⟨_, .mul⟩ => 3
  invFun := fun i => match i.val with
    | 0 => ⟨0, .zero⟩
    | 1 => ⟨1, .succ⟩
    | 2 => ⟨2, .add⟩
    | _ + 3 => ⟨2, .mul⟩
  left_inv := by
    rintro ⟨n, f⟩
    cases f <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

instance arithmeticSigmaPrimcodable : Primcodable (Σ n, ArithmeticSymbol n) :=
  Primcodable.ofEquiv (Fin 4) arithmeticSigmaEquiv

theorem arithmeticSigma_arity_primrec :
    Primrec (fun f : Σ n, ArithmeticSymbol n => f.1) := by
  have he : Primrec (fun f : Σ n, ArithmeticSymbol n =>
      (arithmeticSigmaEquiv f).val) := Primrec.fin_val.comp Primrec.of_equiv
  have h : Primrec (fun f : Σ n, ArithmeticSymbol n =>
      cond ((arithmeticSigmaEquiv f).val == 0) 0
        (cond ((arithmeticSigmaEquiv f).val == 1) 1 2)) :=
    (Primrec.beq.comp he (Primrec.const 0)).cond (Primrec.const 0)
      ((Primrec.beq.comp he (Primrec.const 1)).cond (Primrec.const 1) (Primrec.const 2))
  exact h.of_eq (by rintro ⟨n, f⟩; cases f <;> rfl)

end Alexander313.Delta
