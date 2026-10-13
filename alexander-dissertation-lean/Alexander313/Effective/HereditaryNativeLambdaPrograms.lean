import Alexander313.Wilken.HereditaryNativeLambda
import Alexander313.Computability

/-!
# Actual Programs for the epsilon/high-root lambda branch

The source Program executes the constructed lambda, including the genuine
zeta search. Its exact input guard is ORIGINAL normal theta-zero admission
and actual nonzero cardinal high part. A positive input Program has the same
guard. The complete literal output graph executes the producer and checks
its returned numeral, including zero. Only finite input/column compilers are
claimed PR; the producer and graph are Partrec. Definition 2.45's other lambda
branches and Lemma 2.46 naturality/coverage are not claimed here.
All proofs are uncompiled candidates.
-/

namespace Alexander313.HereditaryNativeLambdaProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

def evaluation (query : Nat) : Part Nat := Lambda.execute query.unpair.1 query.unpair.2

theorem evaluation_partrec : Partrec evaluation :=
  Lambda.execute_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (s a : Nat) : program.eval (Nat.pair s a) = Lambda.execute s a := by
  simpa only [evaluation, Nat.unpair_pair] using
    Classical.choose_spec program_exists (Nat.pair s a)

theorem program_domain (s a : Nat) : program.domain (Nat.pair s a) ↔ Lambda.inputCheck s a = true := by
  rw [Program.domain, program_eval, Lambda.execute_domain]

theorem program_spec (s a out : Nat) (ho : out ∈ program.eval (Nat.pair s a)) :
    Lambda.inputCheck s a = true ∧ Comparison.acceptedCode (Iota.alphaCode s a) out = true ∧
      interpretation (Iota.alphaCode s a) out =
        interpretation (Iota.alphaCode s a) (Iota.literalCode s a (Lambda.deltaCode a)) +
          SourceZeta.sourceValue s a :=
  Lambda.execute_spec s a out (by simpa only [program_eval] using ho)

noncomputable def sourceColumn (s : Nat) : Program := program.column s

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_eval (s a : Nat) : (sourceColumn s).eval a = Lambda.execute s a := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (s a : Nat) : (sourceColumn s).domain a ↔ Lambda.inputCheck s a = true := by
  rw [sourceColumn, Program.column_domain, program_domain]

theorem sourceColumn_spec (s a out : Nat) (ho : out ∈ (sourceColumn s).eval a) :
    Lambda.inputCheck s a = true ∧ Comparison.acceptedCode (Iota.alphaCode s a) out = true ∧
      interpretation (Iota.alphaCode s a) out =
        interpretation (Iota.alphaCode s a) (Iota.literalCode s a (Lambda.deltaCode a)) +
          SourceZeta.sourceValue s a :=
  Lambda.execute_spec s a out (by simpa only [sourceColumn_eval] using ho)

theorem sourceColumn_unique (s a : Nat) (ha : Lambda.inputCheck s a = true) :
    ∃! out, out ∈ (sourceColumn s).eval a := by
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((sourceColumn_domain s a).mpr ha)
  exact ⟨out, ho, fun other he => Part.mem_unique he ho⟩

def inputEvaluation (query : Nat) : Part Nat :=
  cond (Lambda.inputCheck query.unpair.1 query.unpair.2) (Part.some 0) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (Lambda.inputCheck_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
    (Computable.const 0).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (s a : Nat) : inputProgram.domain (Nat.pair s a) ↔ Lambda.inputCheck s a = true := by
  rw [Program.domain, Classical.choose_spec inputProgram_exists]
  simp only [inputEvaluation, Nat.unpair_pair]
  cases h : Lambda.inputCheck s a <;> simp [h]

noncomputable def inputColumn (s : Nat) : Program := inputProgram.column s

theorem inputColumn_primrec : Primrec inputColumn :=
  Program.column_primrec.comp (Primrec.const inputProgram) Primrec.id

theorem inputColumn_domain (s a : Nat) : (inputColumn s).domain a ↔ Lambda.inputCheck s a = true := by
  rw [inputColumn, Program.column_domain, inputProgram_domain]

def graphEvaluation (query : Nat) : Part Nat :=
  (evaluation query.unpair.1).bind (fun out =>
    cond (query.unpair.2 == out) (Part.some 0) Part.none)

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hp := evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have he : Computable (fun p : Nat × Nat => p.1.unpair.2 == p.2) :=
    (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd).to_comp
  have hb := Partrec.cond he (Computable.const 0).partrec Partrec.none
  exact Partrec.bind hp hb.to₂

theorem graphEvaluation_domain (s a out : Nat) :
    (graphEvaluation (Nat.pair (Nat.pair s a) out)).Dom ↔ out ∈ Lambda.execute s a := by
  simp only [graphEvaluation, Nat.unpair_pair, evaluation, Part.dom_iff_mem]
  constructor
  · rintro ⟨result, hm⟩
    obtain ⟨value, hv, he⟩ := Part.mem_bind_iff.mp hm
    by_cases h : out = value
    · subst value; exact hv
    · simp [h, Part.notMem_none] at he
  · intro ho
    exact ⟨0, Part.mem_bind_iff.mpr ⟨out, ho, by simp⟩⟩

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (s a out : Nat) : graphProgram.domain
    (Nat.pair (Nat.pair s a) out) ↔ out ∈ program.eval (Nat.pair s a) := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists, graphEvaluation_domain, program_eval]

noncomputable def graphColumn (s a : Nat) : Program := graphProgram.column (Nat.pair s a)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (s a out : Nat) : (graphColumn s a).domain out ↔
    out ∈ (sourceColumn s).eval a := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]

end Alexander313.HereditaryNativeLambdaProgram
