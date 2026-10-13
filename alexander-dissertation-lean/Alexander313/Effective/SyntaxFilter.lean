import Alexander313.Effective.FormulaSyntax

/-!
# An actual uniform compiler excluding nonsyntactic inputs

The compiler inserts the primitive-recursive formula recognizer before an
arbitrary joint partial program. One fixed universal checking program is
obtained from mathlib's proved code-representation theorem; s-m-n then gives
the primitive-recursive compiler. Thus the parameter program is effective
data, not an assumed semantic predicate or a decidability oracle.

The resulting `EffectiveFamily` need not be sentence- or consequence-closed.
Those separate properties require the actual source generator/proof program.
-/

namespace Alexander313

def syntaxCheckedEvaluation (e n : Nat) : Part Nat :=
  cond (Formula.isCode n.unpair.2)
    ((Nat.Partrec.Code.ofNatCode e).eval n) Part.none

theorem syntaxCheckedEvaluation_partrec : Partrec₂ syntaxCheckedEvaluation := by
  have htest : Computable (fun p : Nat × Nat => Formula.isCode p.2.unpair.2) :=
    Formula.isCode_primrec.to_comp.comp
      (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd))
  have heval : Partrec (fun p : Nat × Nat =>
      (Nat.Partrec.Code.ofNatCode p.1).eval p.2) :=
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat Program).comp Computable.fst) Computable.snd
  exact (Partrec.cond htest heval Partrec.none).to₂

/-- The compiler is primitive recursive and has its exact evaluator
    equation. Its one fixed kernel is supplied by the proved universal
    program representation theorem, rather than a project axiom. -/
theorem syntaxFilterCompiler_exists :
    ∃ compiler : Program → Program, Primrec compiler ∧
      ∀ c n, (compiler c).eval n =
        cond (Formula.isCode n.unpair.2) (c.eval n) Part.none := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr syntaxCheckedEvaluation_partrec)
  refine ⟨fun c => Nat.Partrec.Code.curry kernel (Encodable.encode c),
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_⟩
  intro c n
  rw [Nat.Partrec.Code.eval_curry, hkernel]
  have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c :=
    Denumerable.ofNat_encode c
  simp [Nat.unpaired, syntaxCheckedEvaluation, hc]

/-- Any supplied joint program has a concrete, uniformly r.e. family of
    formula memberships after the compiler removes invalid syntax. -/
theorem effectiveFamily_from_program (c : Program) :
    ∃ F : EffectiveFamily Nat,
      (∀ i φ, F.proves i φ ↔ c.domain (Nat.pair i (φ.code id))) ∧
      (∀ i, F.encodeOwner i = i) := by
  obtain ⟨compiler, hcompiler, heval⟩ := syntaxFilterCompiler_exists
  have hdomain (n : Nat) : (compiler c).domain n ↔
      Formula.isCode n.unpair.2 = true ∧ c.domain n := by
    change ((compiler c).eval n).Dom ↔ _
    rw [heval]
    cases h : Formula.isCode n.unpair.2 <;> simp [h, Program.domain]
  let F : EffectiveFamily Nat := {
    encodeOwner := id
    encodeFormula := Formula.code id
    owner_injective := Function.injective_id
    formula_injective := Formula.code_injective id Function.injective_id
    formula_coding := fun _ => rfl
    recognizes := compiler c
    proves := fun i φ => c.domain (Nat.pair i (φ.code id))
    recognizes_correct := by
      intro i φ
      rw [hdomain]
      simp only [Nat.unpair_pair, Formula.isCode_code, true_and, id_eq]
    recognizes_only_syntax := by
      intro n hn
      have hsyntax := (hdomain n).mp hn
      obtain ⟨φ, hφ⟩ := Formula.isCode_sound n.unpair.2 hsyntax.1
      refine ⟨n.unpair.1, φ, ?_⟩
      rw [hφ]
      exact (Nat.pair_unpair n).symm }
  exact ⟨F, fun _ _ => Iff.rfl, fun _ => rfl⟩

end Alexander313
