import Alexander313.Wilken.SourceOneNativeBoundedContextMuPublic
import Alexander313.Computability

/-!
# Genuine source-one outer intermediate mu Programs and complete graphs

Literal modes zero and one execute actual native and canonical public mu
under the original source-zero outer guard. The real compiler supplies
source/root and output graph columns, including numerical output zero.
The public output uses the returned beta's own endpoint, derived by the
actual source-one mu translation. No Program, return or graph oracle.
Source candidates remain uncompiled.
-/

namespace Alexander313.SourceOneBoundedContextMuProgram

open Wilken.RelativeTerm.Hereditary
open SourceOneIota.BoundedContextReturn

def context (query : Nat) : MuPublic.Context := query.unpair.2.unpair

theorem context_primrec : Primrec context :=
  Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)

def inputCheck (query : Nat) : Bool :=
  ((query.unpair.1 == 0) || (query.unpair.1 == 1)) &&
    MuPublic.inputCheck (context query).1 (context query).2

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp
    (Primrec.or.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
      (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)))
    (Primrec.comp MuPublic.inputCheck_primrec context_primrec)

theorem inputCheck_exact (mode a b : Nat) : inputCheck (Nat.pair mode (Nat.pair a b)) = true ↔
    (mode = 0 ∨ mode = 1) ∧ MuPublic.inputCheck a b = true := by
  simp only [inputCheck, context, Nat.unpair_pair, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

def outputCode (query : Nat) : Nat :=
  let p := context query
  cond (query.unpair.1 == 0) (MuPublic.muCode p.1 p.2)
    (cond (query.unpair.1 == 1) (MuPublic.publicCode p.1 p.2 (MuPublic.muCode p.1 p.2)) 0)

theorem outputCode_primrec : Primrec outputCode := by
  have hn := Primrec.comp MuPublic.muCode_primrec context_primrec
  have hp := MuPublic.publicCode_primrec.comp context_primrec hn
  exact (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).cond hn
    ((Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).cond hp (Primrec.const 0))

def evaluation (query : Nat) : Part Nat := cond (inputCheck query) (Part.some (outputCode query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond inputCheck_primrec.to_comp outputCode_primrec.to_comp.partrec Partrec.none

theorem evaluation_native (a b : Nat) :
    evaluation (Nat.pair 0 (Nat.pair a b)) = MuPublic.nativeExecute a b := by
  simp only [evaluation, inputCheck, outputCode, context, Nat.unpair_pair,
    beq_self_eq_true, Bool.true_or, Bool.true_and, Bool.cond_true, MuPublic.nativeExecute]

theorem evaluation_public (a b : Nat) :
    evaluation (Nat.pair 1 (Nat.pair a b)) = MuPublic.execute a b := by
  cases h : MuPublic.inputCheck a b <;>
    simp [evaluation, inputCheck, outputCode, context, Nat.unpair_pair,
      MuPublic.execute, MuPublic.nativeExecute, h]

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

theorem program_domain (mode a b : Nat) : program.domain (Nat.pair mode (Nat.pair a b)) ↔
    (mode = 0 ∨ mode = 1) ∧ MuPublic.inputCheck a b = true := by
  rw [Program.domain, program_eval, evaluation_domain, inputCheck_exact]

theorem program_native_spec (a b out : Nat) (ho : out ∈ program.eval (Nat.pair 0 (Nat.pair a b))) :
    MuPublic.inputCheck a b = true ∧
      NativeContext.lowCheckCode (NativeContext.PublicEpsilonIota.betaCode (SourceOneIota.alphaCode a) b) out = true ∧
      NativeContext.Comparison.acceptedCode (NativeContext.PublicEpsilonIota.betaCode (SourceOneIota.alphaCode a) b) out = true ∧
      NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (SourceOneIota.alphaCode a) b) out =
        NativeContext.PublicEpsilonIota.Mu.sourceValue (SourceOneIota.alphaCode a) b :=
  MuPublic.nativeExecute_spec a b out (by simpa only [program_eval, evaluation_native] using ho)

theorem program_public_spec (a b out : Nat) (ho : out ∈ program.eval (Nat.pair 1 (Nat.pair a b))) :
    MuPublic.inputCheck a b = true ∧ Canonical.check out = true ∧
      unionInterpretation out = NativeContext.PublicEpsilonIota.Mu.sourceValue (SourceOneIota.alphaCode a) b :=
  MuPublic.execute_spec a b out (by simpa only [program_eval, evaluation_public] using ho)

theorem program_graph (query out : Nat) : out ∈ program.eval query ↔
    inputCheck query = true ∧ out = outputCode query := by rw [program_eval, evaluation_graph]

noncomputable def sourceColumn (mode a : Nat) : Program := (program.column mode).column a

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (mode a b : Nat) :
    (sourceColumn mode a).eval b = evaluation (Nat.pair mode (Nat.pair a b)) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (mode a b : Nat) : (sourceColumn mode a).domain b ↔
    (mode = 0 ∨ mode = 1) ∧ MuPublic.inputCheck a b = true := by
  rw [Program.domain, sourceColumn_eval, evaluation_domain, inputCheck_exact]

theorem sourceColumn_graph (mode a b out : Nat) : out ∈ (sourceColumn mode a).eval b ↔
    inputCheck (Nat.pair mode (Nat.pair a b)) = true ∧ out = outputCode (Nat.pair mode (Nat.pair a b)) := by
  rw [sourceColumn_eval, evaluation_graph]

def graphCheck (query : Nat) : Bool := inputCheck query.unpair.1 && (query.unpair.2 == outputCode query.unpair.1)

theorem graphCheck_primrec : Primrec graphCheck :=
  Primrec.and.comp (inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair) (outputCode_primrec.comp (Primrec.fst.comp Primrec.unpair)))

theorem graphCheck_exact (query out : Nat) : graphCheck (Nat.pair query out) = true ↔ out ∈ program.eval query := by
  simp only [graphCheck, Nat.unpair_pair, Bool.and_eq_true, beq_iff_eq, program_graph]

def graphEvaluation (query : Nat) : Part Nat := cond (graphCheck query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphCheck_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (query out : Nat) : graphProgram.domain (Nat.pair query out) ↔ out ∈ program.eval query := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  have he := graphCheck_exact query out
  cases h : graphCheck (Nat.pair query out) <;> simp [graphEvaluation, h] at he ⊢ <;> exact he

noncomputable def graphColumn (mode a b : Nat) : Program := graphProgram.column (Nat.pair mode (Nat.pair a b))

theorem graphColumn_primrec : Primrec (fun p : Nat × MuPublic.Context => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (mode a b out : Nat) : (graphColumn mode a b).domain out ↔ out ∈ (sourceColumn mode a).eval b := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]

end Alexander313.SourceOneBoundedContextMuProgram
