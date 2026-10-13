import Alexander313.Effective.AlphaFormation
import Alexander313.Effective.WeakVariableFormation
import Alexander313.Effective.SchemaGenerators
import Alexander313.Alexander.EffectiveDelta

/-!
# Literal BL candidate data and effective native BL matrices

Both branches use the actual source alpha and weak-variable tests. Matrix
formation preserves the exact native BL definitions, including native free
variable relabeling on the right of BL2. Source modal labels remain opaque
under that native relabeling.
-/

noncomputable section

namespace Alexander313.Delta

namespace NativeFormula

theorem iff_primrec (n : Nat) : Primrec₂
    (fun φ ψ : Syntax n => φ.iff ψ) := by
  have imp := imp_primrec n
  have neg : Primrec (fun φ : Syntax n => φ.not) :=
    imp.comp Primrec.id (Primrec.const (.falsum : Syntax n))
  have hl : Primrec (fun p : Syntax n × Syntax n => p.1.imp p.2) :=
    imp.comp Primrec.fst Primrec.snd
  have hr : Primrec (fun p : Syntax n × Syntax n => p.2.imp p.1) :=
    imp.comp Primrec.snd Primrec.fst
  exact (neg.comp (imp.comp hl (neg.comp hr))).to₂

def relabelVariableCode (x y c : Nat) : Nat :=
  substCode x (EncodedSyntax.node 0 (Nat.pair 0 y)) c

theorem relabelVariableCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => relabelVariableCode p.1.1 p.1.2 p.2) := by
  have hx : Primrec (fun p : (Nat × Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hy : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht := EncodedSyntax.node_primrec.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 0) hy)
  exact substCode_primrec.comp ((hx.pair ht).pair Primrec.snd)

@[simp] theorem relabelVariableCode_code (x y : Nat) (φ : Syntax 0) :
    relabelVariableCode x y (code φ) =
      code (FirstOrder.Language.Formula.relabel (replaceVar x y) φ) := by
  apply rewriteCode_relabel 0 (x, EncodedSyntax.node 0 (Nat.pair 0 y))
    (Sum.inl ∘ replaceVar x y)
  intro n t
  apply NativeTerm.rewriteCode_relabel
  intro v
  cases v with
  | inl z =>
    by_cases h : z = x
    · simp [NativeTerm.substVariableCode, NativeTerm.variableCode,
        replaceVar, FirstOrder.Language.BoundedFormula.relabelAux,
        Function.comp_def, h, NativeTerm.code_var, Nat.unpair_pair,
        EncodedSyntax.node]
    · have hb : (z == x) = false := beq_eq_false_iff_ne.mpr h
      simp [NativeTerm.substVariableCode, NativeTerm.variableCode,
        replaceVar, FirstOrder.Language.BoundedFormula.relabelAux,
        Function.comp_def, h, hb, NativeTerm.code_var, Nat.unpair_pair,
        EncodedSyntax.node]
  | inr i =>
    simp [NativeTerm.substVariableCode, NativeTerm.variableCode,
      FirstOrder.Language.BoundedFormula.relabelAux, Function.comp_def,
      NativeTerm.code_var, Nat.unpair_pair, EncodedSyntax.node]

theorem relabelVariable_primrec : Primrec
    (fun p : (Nat × Nat) × Syntax 0 =>
      FirstOrder.Language.Formula.relabel (replaceVar p.1.1 p.1.2) p.2) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, relabelVariableCode_code] using
    relabelVariableCode_primrec.comp
      (Primrec.fst.pair ((code_primrec 0).comp Primrec.snd))

end NativeFormula

theorem BL1_primrec : Primrec
    (fun p : Nat × (Formula Nat × Formula Nat) => BL1 p.1 p.2.1 p.2.2) := by
  have ha := (Primrec.fst : Primrec (Prod.fst : Nat × (Formula Nat × Formula Nat) → _))
  have hφ : Primrec (fun p : Nat × (Formula Nat × Formula Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hψ : Primrec (fun p : Nat × (Formula Nat × Formula Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (NativeFormula.iff_primrec 0).comp
    (formula_primrec.comp (Formula.know_primrec.comp ha hφ))
    (formula_primrec.comp (Formula.know_primrec.comp ha hψ))

theorem BL2_primrec : Primrec
    (fun p : Nat × (Formula Nat × (Nat × Nat)) => BL2 p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ha := (Primrec.fst : Primrec (Prod.fst : Nat × (Formula Nat × (Nat × Nat)) → _))
  have hφ : Primrec (fun p : Nat × (Formula Nat × (Nat × Nat)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : Nat × (Formula Nat × (Nat × Nat)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy : Primrec (fun p : Nat × (Formula Nat × (Nat × Nat)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsub := Formula.substTerm_primrec.comp ((hx.pair (Term.var_primrec.comp hy)).pair hφ)
  have hl := formula_primrec.comp (Formula.know_primrec.comp ha hsub)
  have hr := NativeFormula.relabelVariable_primrec.comp
    ((hx.pair hy).pair (formula_primrec.comp (Formula.know_primrec.comp ha hφ)))
  exact (NativeFormula.iff_primrec 0).comp hl hr

namespace BLCandidate

abbrev Data := (Nat × (Formula Nat × Formula Nat)) ⊕
  (Nat × (Formula Nat × (Nat × Nat)))

def data : BLCandidate Nat → Data
  | .alphabetic a φ ψ => .inl (a, φ, ψ)
  | .weakVariable a φ x y => .inr (a, φ, x, y)

def ofData : Data → BLCandidate Nat
  | .inl (a, φ, ψ) => .alphabetic a φ ψ
  | .inr (a, φ, x, y) => .weakVariable a φ x y

def dataEquiv : BLCandidate Nat ≃ Data where
  toFun := data
  invFun := ofData
  left_inv := by intro c; cases c <;> rfl
  right_inv := by intro d; rcases d with ⟨a, φ, ψ⟩ | ⟨a, φ, x, y⟩ <;> rfl

instance literalPrimcodable : Primcodable (BLCandidate Nat) :=
  Primcodable.ofEquiv Data dataEquiv

theorem data_primrec : Primrec data := Primrec.of_equiv (e := dataEquiv)
theorem ofData_primrec : Primrec ofData := Primrec.of_equiv_symm (e := dataEquiv)

def accepted : BLCandidate Nat → Bool
  | .alphabetic _ φ ψ => decide (φ.AlphaEquivalent ψ)
  | .weakVariable _ φ x y => φ.variableSubstitutable? x y

theorem accepted_primrec : Primrec accepted := by
  have hl : Primrec (fun d : Nat × (Formula Nat × Formula Nat) =>
      decide (d.2.1.AlphaEquivalent d.2.2)) :=
    Formula.alphaEquivalent_primrec.decide.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun d : Nat × (Formula Nat × (Nat × Nat)) =>
      d.2.1.variableSubstitutable? d.2.2.1 d.2.2.2) :=
    Formula.variableSubstitutable?_primrec.comp
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd))
  exact (Primrec.sumCasesOn data_primrec (hl.comp Primrec.snd).to₂
    (hr.comp Primrec.snd).to₂).of_eq (by intro c; cases c <;> rfl)

def matrix : BLCandidate Nat → (language Nat).Formula Nat
  | .alphabetic a φ ψ => BL1 a φ ψ
  | .weakVariable a φ x y => BL2 a φ x y

theorem matrix_primrec : Primrec matrix :=
  (Primrec.sumCasesOn data_primrec (BL1_primrec.comp Primrec.snd).to₂
    (BL2_primrec.comp Primrec.snd).to₂).of_eq (by intro c; cases c <;> rfl)

theorem accepted_matrix (c : BLCandidate Nat) (h : c.accepted = true) :
    c.matrix ∈ baseLogicMatrices Nat := by
  cases c with
  | alphabetic a φ ψ =>
    exact Or.inl ⟨a, φ, ψ, of_decide_eq_true h, rfl⟩
  | weakVariable a φ x y =>
    exact Or.inr ⟨a, φ, x, y, (Formula.variableSubstitutable?_eq_true x y φ).mp h, rfl⟩

theorem exists_accepted_matrix_iff (σ : (language Nat).Formula Nat) :
    (∃ c : BLCandidate Nat, c.accepted = true ∧ c.matrix = σ) ↔
      σ ∈ baseLogicMatrices Nat := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact accepted_matrix c hc
  · rintro (⟨a, φ, ψ, ha, rfl⟩ | ⟨a, φ, x, y, hv, rfl⟩)
    · exact ⟨.alphabetic a φ ψ, by simp [accepted, ha], rfl⟩
    · exact ⟨.weakVariable a φ x y,
        (Formula.variableSubstitutable?_eq_true x y φ).mpr hv, rfl⟩

end BLCandidate
end Alexander313.Delta
