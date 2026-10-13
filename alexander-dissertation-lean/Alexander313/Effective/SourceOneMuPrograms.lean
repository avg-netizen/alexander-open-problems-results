import Alexander313.Wilken.SourceOneNativeMu
import Alexander313.Computability

/-!
# Genuine original-source-one normal/raw mu Programs

Modes zero and one execute the actual original source-one normal/raw mu
producer. The guard retains the original source dictionary; every actual
alpha-context caller is derived by that producer. Invalid modes or inputs
have no output. Genuine chosen Programs, primitive mode/output columns and
complete numerical graphs retain output zero. No Program or graph oracle.
Uncompiled source candidates.
-/

namespace Alexander313.SourceOneMuProgram

open Wilken.RelativeTerm.Hereditary

def inputCheck (query : Nat) : Bool := cond (query.unpair.1 == 0)
  (SourceOneIota.Mu.inputCheck query.unpair.2)
  (cond (query.unpair.1 == 1) (SourceOneIota.Mu.Raw.inputCheck query.unpair.2) false)

theorem inputCheck_primrec : Primrec inputCheck := by
  have hm := Primrec.fst.comp Primrec.unpair
  have ha := Primrec.snd.comp Primrec.unpair
  exact (Primrec.beq.comp hm (Primrec.const 0)).cond
    (SourceOneIota.Mu.inputCheck_primrec.comp ha)
    ((Primrec.beq.comp hm (Primrec.const 1)).cond
      (SourceOneIota.Mu.Raw.inputCheck_primrec.comp ha) (Primrec.const false))

theorem inputCheck_exact (mode a : Nat) : inputCheck (Nat.pair mode a) = true ↔
    (mode = 0 ∧ SourceOneIota.Mu.inputCheck a = true) ∨
      (mode = 1 ∧ SourceOneIota.Mu.Raw.inputCheck a = true) := by
  by_cases h0 : mode = 0
  · subst mode; simp [inputCheck, Nat.unpair_pair]
  · by_cases h1 : mode = 1
    · subst mode; simp [inputCheck, Nat.unpair_pair]
    · simp [inputCheck, Nat.unpair_pair, h0, h1]

def outputCode (query : Nat) : Nat := cond (query.unpair.1 == 0)
  (SourceOneIota.Mu.muCode query.unpair.2)
  (cond (query.unpair.1 == 1) (SourceOneIota.Mu.Raw.muCode query.unpair.2) 0)

theorem outputCode_primrec : Primrec outputCode := by
  have hm := Primrec.fst.comp Primrec.unpair
  have ha := Primrec.snd.comp Primrec.unpair
  exact (Primrec.beq.comp hm (Primrec.const 0)).cond
    (SourceOneIota.Mu.muCode_primrec.comp ha)
    ((Primrec.beq.comp hm (Primrec.const 1)).cond
      (SourceOneIota.Mu.Raw.muCode_primrec.comp ha) (Primrec.const 0))

def evaluation (query : Nat) : Part Nat :=
  cond (inputCheck query) (Part.some (outputCode query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond inputCheck_primrec.to_comp outputCode_primrec.to_comp.partrec Partrec.none

theorem evaluation_normal (a : Nat) : evaluation (Nat.pair 0 a) = SourceOneIota.Mu.execute a := by
  simp only [evaluation, inputCheck, outputCode, Nat.unpair_pair, beq_self_eq_true,
    Bool.cond_true, SourceOneIota.Mu.execute]

theorem evaluation_raw (a : Nat) : evaluation (Nat.pair 1 a) = SourceOneIota.Mu.Raw.execute a := by
  simp [evaluation, inputCheck, outputCode, Nat.unpair_pair, SourceOneIota.Mu.Raw.execute]

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔ inputCheck query = true := by
  cases h : inputCheck query <;> simp [evaluation, h]

theorem evaluation_graph (query out : Nat) : out ∈ evaluation query ↔
    inputCheck query = true ∧ out = outputCode query := by
  cases h : inputCheck query <;> simp [evaluation, h]

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (query : Nat) : program.eval query = evaluation query :=
  Classical.choose_spec program_exists query

theorem program_domain (mode a : Nat) : program.domain (Nat.pair mode a) ↔
    (mode = 0 ∧ SourceOneIota.Mu.inputCheck a = true) ∨
      (mode = 1 ∧ SourceOneIota.Mu.Raw.inputCheck a = true) := by
  rw [Program.domain, program_eval, evaluation_domain, inputCheck_exact]

theorem program_normal_spec (a out : Nat) (ho : out ∈ program.eval (Nat.pair 0 a)) :
    SourceOneIota.Mu.inputCheck a = true ∧ NativeContext.lowCheckCode (SourceOneIota.alphaCode a) out = true ∧
      NativeContext.Comparison.acceptedCode (SourceOneIota.alphaCode a) out = true ∧
        NativeContext.interpretation (SourceOneIota.alphaCode a) out = SourceOneIota.Mu.sourceValue a :=
  SourceOneIota.Mu.execute_spec a out (by simpa only [program_eval, evaluation_normal] using ho)

theorem program_raw_spec (a out : Nat) (ho : out ∈ program.eval (Nat.pair 1 a)) :
    SourceOneIota.Mu.Raw.inputCheck a = true ∧ NativeContext.lowCheckCode (SourceOneIota.Mu.Raw.outputContext a) out = true ∧
      NativeContext.Comparison.acceptedCode (SourceOneIota.Mu.Raw.outputContext a) out = true ∧
        NativeContext.interpretation (SourceOneIota.Mu.Raw.outputContext a) out =
          SourceOneIota.Mu.sourceValue (SourceOneIota.Mu.Raw.normalizedRoot a) :=
  SourceOneIota.Mu.Raw.execute_spec a out (by simpa only [program_eval, evaluation_raw] using ho)

theorem program_graph (query out : Nat) : out ∈ program.eval query ↔
    inputCheck query = true ∧ out = outputCode query := by
  rw [program_eval, evaluation_graph]

noncomputable def sourceColumn (mode : Nat) : Program := program.column mode

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_eval (mode a : Nat) :
    (sourceColumn mode).eval a = evaluation (Nat.pair mode a) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_graph (mode a out : Nat) : out ∈ (sourceColumn mode).eval a ↔
    inputCheck (Nat.pair mode a) = true ∧ out = outputCode (Nat.pair mode a) := by
  rw [sourceColumn_eval, evaluation_graph]

def graphCheck (query : Nat) : Bool :=
  inputCheck query.unpair.1 && (query.unpair.2 == outputCode query.unpair.1)

theorem graphCheck_primrec : Primrec graphCheck :=
  Primrec.and.comp (inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
      (outputCode_primrec.comp (Primrec.fst.comp Primrec.unpair)))

theorem graphCheck_exact (query out : Nat) : graphCheck (Nat.pair query out) = true ↔
    out ∈ program.eval query := by
  simp only [graphCheck, Nat.unpair_pair, Bool.and_eq_true, beq_iff_eq, program_graph]

def graphEvaluation (query : Nat) : Part Nat := cond (graphCheck query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphCheck_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (query out : Nat) : graphProgram.domain (Nat.pair query out) ↔
    out ∈ program.eval query := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  have he := graphCheck_exact query out
  cases h : graphCheck (Nat.pair query out) <;> simp [graphEvaluation, h] at he ⊢ <;> exact he

noncomputable def graphColumn (mode a : Nat) : Program := graphProgram.column (Nat.pair mode a)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem graphColumn_domain (mode a out : Nat) : (graphColumn mode a).domain out ↔
    out ∈ (sourceColumn mode).eval a := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]

end Alexander313.SourceOneMuProgram
