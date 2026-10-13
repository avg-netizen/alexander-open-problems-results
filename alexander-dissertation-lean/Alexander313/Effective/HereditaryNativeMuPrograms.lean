import Alexander313.Wilken.HereditaryNativeMu
import Alexander313.Computability

/-!
# Actual normal/raw mu Programs and complete numerical graphs

Modes zero and one execute the constructed original normal/raw native mu.
The actual finite producer, original guards, complete numerical graph and
literal column compilation are primitive recursive. Chosen universal
Programs implement the genuine producers and graph checkers on all inputs;
invalid modes and guards have no output. Zero numerical output is retained
in the complete graph. No supplied Program or graph oracle. Uncompiled.
-/

namespace Alexander313.HereditaryNativeMuProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

def inputCheck (query : Nat) : Bool := cond (query.unpair.1 == 0)
  (Mu.inputCheck query.unpair.2.unpair.1 query.unpair.2.unpair.2)
  (cond (query.unpair.1 == 1)
    (Mu.Raw.inputCheck query.unpair.2.unpair.1 query.unpair.2.unpair.2) false)

theorem inputCheck_primrec : Primrec inputCheck := by
  have hm := Primrec.fst.comp Primrec.unpair
  have hs := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have ha := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact (Primrec.beq.comp hm (Primrec.const 0)).cond
    (Mu.inputCheck_primrec.comp hs ha)
    ((Primrec.beq.comp hm (Primrec.const 1)).cond
      (Mu.Raw.inputCheck_primrec.comp hs ha) (Primrec.const false))

theorem inputCheck_exact (mode s a : Nat) :
    inputCheck (Nat.pair mode (Nat.pair s a)) = true ↔
      (mode = 0 ∧ Mu.inputCheck s a = true) ∨
        (mode = 1 ∧ Mu.Raw.inputCheck s a = true) := by
  by_cases h0 : mode = 0
  · subst mode; simp [inputCheck, Nat.unpair_pair]
  · by_cases h1 : mode = 1
    · subst mode; simp [inputCheck, Nat.unpair_pair]
    · simp [inputCheck, Nat.unpair_pair, h0, h1]

def outputCode (query : Nat) : Nat := cond (query.unpair.1 == 0)
  (Mu.muCode query.unpair.2.unpair.1 query.unpair.2.unpair.2)
  (cond (query.unpair.1 == 1)
    (Mu.Raw.muCode query.unpair.2.unpair.1 query.unpair.2.unpair.2) 0)

theorem outputCode_primrec : Primrec outputCode := by
  have hm := Primrec.fst.comp Primrec.unpair
  have hs := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have ha := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact (Primrec.beq.comp hm (Primrec.const 0)).cond
    (Mu.muCode_primrec.comp hs ha)
    ((Primrec.beq.comp hm (Primrec.const 1)).cond
      (Mu.Raw.muCode_primrec.comp hs ha) (Primrec.const 0))

def evaluation (query : Nat) : Part Nat :=
  cond (inputCheck query) (Part.some (outputCode query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond inputCheck_primrec.to_comp outputCode_primrec.to_comp.partrec Partrec.none

theorem evaluation_normal (s a : Nat) : evaluation (Nat.pair 0 (Nat.pair s a)) = Mu.execute s a := by
  simp only [evaluation, inputCheck, outputCode, Nat.unpair_pair, beq_self_eq_true,
    Bool.cond_true, Mu.execute]

theorem evaluation_raw (s a : Nat) : evaluation (Nat.pair 1 (Nat.pair s a)) = Mu.Raw.execute s a := by
  simp [evaluation, inputCheck, outputCode, Nat.unpair_pair, Mu.Raw.execute]

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

theorem program_domain (mode s a : Nat) : program.domain (Nat.pair mode (Nat.pair s a)) ↔
    (mode = 0 ∧ Mu.inputCheck s a = true) ∨ (mode = 1 ∧ Mu.Raw.inputCheck s a = true) := by
  rw [Program.domain, program_eval, evaluation_domain, inputCheck_exact]

theorem program_normal_spec (s a out : Nat) (ho : out ∈ program.eval (Nat.pair 0 (Nat.pair s a))) :
    Mu.inputCheck s a = true ∧ lowCheckCode (Iota.alphaCode s a) out = true ∧
      Comparison.acceptedCode (Iota.alphaCode s a) out = true ∧
        interpretation (Iota.alphaCode s a) out = Mu.sourceValue s a :=
  Mu.execute_spec s a out (by simpa only [program_eval, evaluation_normal] using ho)

theorem program_raw_spec (s a out : Nat) (ho : out ∈ program.eval (Nat.pair 1 (Nat.pair s a))) :
    Mu.Raw.inputCheck s a = true ∧ lowCheckCode (Mu.Raw.outputContext s a) out = true ∧
      Comparison.acceptedCode (Mu.Raw.outputContext s a) out = true ∧
        interpretation (Mu.Raw.outputContext s a) out = Mu.sourceValue s (Mu.Raw.normalizedRoot s a) :=
  Mu.Raw.execute_spec s a out (by simpa only [program_eval, evaluation_raw] using ho)

/-- Every numerical output, including zero, occurs exactly on its real
original-domain literal row. There is no separate positive-output filter. -/
theorem program_graph (query out : Nat) : out ∈ program.eval query ↔
    inputCheck query = true ∧ out = outputCode query := by
  rw [program_eval, evaluation_graph]

noncomputable def sourceColumn (mode s : Nat) : Program := (program.column mode).column s

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (mode s a : Nat) :
    (sourceColumn mode s).eval a = evaluation (Nat.pair mode (Nat.pair s a)) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_graph (mode s a out : Nat) : out ∈ (sourceColumn mode s).eval a ↔
    inputCheck (Nat.pair mode (Nat.pair s a)) = true ∧ out = outputCode (Nat.pair mode (Nat.pair s a)) := by
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

noncomputable def graphColumn (mode s a : Nat) : Program :=
  graphProgram.column (Nat.pair mode (Nat.pair s a))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (mode s a out : Nat) : (graphColumn mode s a).domain out ↔
    out ∈ (sourceColumn mode s).eval a := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]

end Alexander313.HereditaryNativeMuProgram
