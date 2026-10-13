import Alexander313.Specification
import Alexander313.Effective.UnaryColumns

/-!
# Canonical compiled unary columns of an effective sentence family

The universal unary-instance kernel and its primitive-recursive compiler
were constructed in `Effective.UnaryColumns`. Choose that compiler once,
then pass the joint program, owner and exact syntax as its data. No column
correctness equation is an assumed source-presentation field here.
-/

namespace Alexander313

noncomputable def unaryColumnCompiler : InstanceParameters → Program :=
  Classical.choose unaryInstanceCompiler_exists

theorem unaryColumnCompiler_primrec : Primrec unaryColumnCompiler :=
  (Classical.choose_spec unaryInstanceCompiler_exists).1

theorem unaryColumnCompiler_eval (p : InstanceParameters) (m : Nat) :
    (unaryColumnCompiler p).eval m = p.1.1.1.eval
      (Nat.pair p.1.1.2 (Formula.substCode p.2 m p.1.2)) :=
  (Classical.choose_spec unaryInstanceCompiler_exists).2 p m

noncomputable def MachineFamily.unaryColumnIndex (F : MachineFamily)
    (j : Nat) (φ : UnaryFormula Nat) : Nat :=
  Encodable.encode (unaryColumnCompiler (((F.effective.recognizes, j),
    φ.body.code id), φ.input))

theorem MachineFamily.unaryColumn_equation (F : MachineFamily)
    (j : Nat) (φ : UnaryFormula Nat) (s : Assignment) :
    W (F.unaryColumnIndex j φ) (s φ.input) ↔
      F.effective.proves j (φ.body.close s) := by
  have hdecode : Nat.Partrec.Code.ofNatCode (F.unaryColumnIndex j φ) =
      unaryColumnCompiler (((F.effective.recognizes, j), φ.body.code id), φ.input) :=
    Denumerable.ofNat_encode
      (unaryColumnCompiler (((F.effective.recognizes, j), φ.body.code id), φ.input))
  rw [W, hdecode, unaryColumnCompiler_eval]
  change (F.effective.recognizes.eval (Nat.pair j
    (Formula.substCode φ.input (s φ.input) (φ.body.code id)))).Dom ↔ _
  rw [← φ.close_code s]
  have hownerFunction : F.effective.encodeOwner = id := funext F.canonical_owners
  have hformula : F.effective.encodeFormula (φ.body.close s) =
      (φ.body.close s).code id := by
    rw [F.effective.formula_coding, hownerFunction]
  simpa only [F.canonical_owners j, hformula, Program.domain] using
    F.effective.recognizes_correct j (φ.body.close s)

end Alexander313
