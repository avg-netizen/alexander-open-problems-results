import Alexander313.Effective.FormulaSubstitution

/-!
# Uniform real programs for unary numeral-instance consequence columns

The compiler uses the actual joint program, owner number, formula code and
input-variable number as data. Its instance transform is primitive recursive,
including quantifier shadowing. One universal kernel followed by s-m-n
produces every column program; no oracle for formulas or consequence is used.
-/

namespace Alexander313

abbrev InstanceParameters := ((Program × Nat) × Nat) × Nat

def instanceParameterKey (p : InstanceParameters) : Nat :=
  Nat.pair (Encodable.encode p.1.1.1) (Nat.pair p.1.1.2 (Nat.pair p.1.2 p.2))

theorem instanceParameterKey_primrec : Primrec instanceParameterKey :=
  Primrec₂.natPair.comp
    (Primrec.encode.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

def unaryInstanceEvaluation (key m : Nat) : Part Nat :=
  let c := Nat.Partrec.Code.ofNatCode key.unpair.1
  let data := key.unpair.2
  c.eval (Nat.pair data.unpair.1
    (Formula.substCode data.unpair.2.unpair.2 m data.unpair.2.unpair.1))

theorem unaryInstanceEvaluation_partrec : Partrec₂ unaryInstanceEvaluation := by
  have hkey : Primrec (fun p : Nat × Nat => p.1.unpair) :=
    Primrec.unpair.comp Primrec.fst
  have hc : Computable (fun p : Nat × Nat =>
      Nat.Partrec.Code.ofNatCode p.1.unpair.1) :=
    (Computable.ofNat Program).comp (Primrec.fst.comp hkey).to_comp
  have hdata := Primrec.unpair.comp (Primrec.snd.comp hkey)
  have hj := Primrec.fst.comp hdata
  have hbody := Primrec.unpair.comp (Primrec.snd.comp hdata)
  have hx := Primrec.snd.comp hbody
  have hφ := Primrec.fst.comp hbody
  have hinstance := Formula.substCode_primrec.comp ((hx.pair Primrec.snd).pair hφ)
  exact (Nat.Partrec.Code.eval_part.comp hc (Primrec₂.natPair.comp hj hinstance).to_comp).to₂

theorem unaryInstanceCompiler_exists :
    ∃ compiler : InstanceParameters → Program, Primrec compiler ∧
      ∀ p m, (compiler p).eval m = p.1.1.1.eval
        (Nat.pair p.1.1.2 (Formula.substCode p.2 m p.1.2)) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr unaryInstanceEvaluation_partrec)
  refine ⟨fun p => Nat.Partrec.Code.curry kernel (instanceParameterKey p),
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) instanceParameterKey_primrec,
    ?_⟩
  intro p m
  rw [Nat.Partrec.Code.eval_curry, hkernel]
  have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode p.1.1.1) = p.1.1.1 :=
    Denumerable.ofNat_encode p.1.1.1
  simp [Nat.unpaired, unaryInstanceEvaluation, instanceParameterKey, Nat.unpair_pair, hc]

/-- The compiler works for all owners and unrestricted unary modal
    formulas at once, with exact numeral syntax in the query sent to `c`. -/
theorem program_unary_columns (c : Program) :
    ∃ index : Nat → UnaryFormula Nat → Nat, ∀ j φ s,
      W (index j φ) (s φ.input) ↔
        c.domain (Nat.pair j ((φ.body.close s).code id)) := by
  obtain ⟨compiler, hcompiler, heval⟩ := unaryInstanceCompiler_exists
  let params (j : Nat) (φ : UnaryFormula Nat) : InstanceParameters :=
    (((c, j), φ.body.code id), φ.input)
  refine ⟨fun j φ => Encodable.encode (compiler (params j φ)), ?_⟩
  intro j φ s
  have hdecode : Nat.Partrec.Code.ofNatCode (Encodable.encode (compiler (params j φ))) =
      compiler (params j φ) := Denumerable.ofNat_encode (compiler (params j φ))
  rw [W, hdecode, heval]
  change (c.eval (Nat.pair j
      (Formula.substCode φ.input (s φ.input) (φ.body.code id)))).Dom ↔ _
  rw [← φ.close_code s]
  rfl

/-- Canonical effective families have actual uniform unary-column indices.
    This constructs the `columns` part of the 3-1-1 source contract once
    its joint source family itself has been constructed. -/
theorem EffectiveFamily.unary_columns (F : EffectiveFamily Nat)
    (howners : ∀ i, F.encodeOwner i = i) :
    ∃ index : Nat → UnaryFormula Nat → Nat, ∀ j φ s,
      W (index j φ) (s φ.input) ↔ F.proves j (φ.body.close s) := by
  have hownerFunction : F.encodeOwner = id := funext howners
  have hformula (θ : Formula Nat) : F.encodeFormula θ = θ.code id := by
    rw [F.formula_coding θ, hownerFunction]
  obtain ⟨index, hindex⟩ := program_unary_columns F.recognizes
  refine ⟨index, fun j φ s => (hindex j φ s).trans ?_⟩
  simpa only [howners j, hformula (φ.body.close s)] using
    F.recognizes_correct j (φ.body.close s)

end Alexander313
