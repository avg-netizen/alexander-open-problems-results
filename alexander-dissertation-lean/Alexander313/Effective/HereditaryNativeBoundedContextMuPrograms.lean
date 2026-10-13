import Alexander313.Wilken.HereditaryNativeBoundedContextMuPublic
import Alexander313.Computability

/-!
# Genuine bounded intermediate mu Programs and complete numerical graphs

Two literal numerical modes execute actual native and canonical public mu.
Every source/root/output column is compiled by the real s-m-n operation.
The original bounded intermediate guard supplies every actual native and
returned-beta public caller. The full graph includes numerical zero, and
invalid modes or original guards reject. No supplied Program or graph
oracle is used. Source-only uncompiled candidates.
-/

namespace Alexander313.HereditaryBoundedContextMuProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext

def context (query : Nat) : BoundedContextIota.Context :=
  (query.unpair.2.unpair.1.unpair, query.unpair.2.unpair.2)

theorem context_primrec : Primrec context := by
  have htail := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  exact (Primrec.unpair.comp (Primrec.fst.comp htail)).pair (Primrec.snd.comp htail)

def inputCheck (query : Nat) : Bool :=
  ((query.unpair.1 == 0) || (query.unpair.1 == 1)) &&
    BoundedContextIota.Mu.inputCheck (context query).1.1 (context query).1.2 (context query).2

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp
    (Primrec.or.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
      (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)))
    (BoundedContextIota.Mu.inputCheck_primrec.comp context_primrec)

theorem inputCheck_exact (mode s a root : Nat) :
    inputCheck (Nat.pair mode (Nat.pair (Nat.pair s a) root)) = true ↔
      (mode = 0 ∨ mode = 1) ∧ BoundedContextIota.Mu.inputCheck s a root = true := by
  simp only [inputCheck, context, Nat.unpair_pair, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

def outputCode (query : Nat) : Nat :=
  let p := context query
  cond (query.unpair.1 == 0) (BoundedContextIota.Mu.muCode p.1.1 p.1.2 p.2)
    (cond (query.unpair.1 == 1)
      (BoundedContextIota.Mu.Public.publicCode p.1.1 p.1.2 p.2
        (BoundedContextIota.Mu.muCode p.1.1 p.1.2 p.2)) 0)

theorem outputCode_primrec : Primrec outputCode := by
  have hn := BoundedContextIota.Mu.muCode_primrec.comp context_primrec
  have hp := BoundedContextIota.Mu.Public.publicCode_primrec.comp context_primrec hn
  exact (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).cond hn
    ((Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).cond hp
      (Primrec.const 0))

def evaluation (query : Nat) : Part Nat :=
  cond (inputCheck query) (Part.some (outputCode query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond inputCheck_primrec.to_comp outputCode_primrec.to_comp.partrec Partrec.none

theorem evaluation_native (s a root : Nat) :
    evaluation (Nat.pair 0 (Nat.pair (Nat.pair s a) root)) = BoundedContextIota.Mu.execute s a root := by
  simp only [evaluation, inputCheck, outputCode, context, Nat.unpair_pair,
    beq_self_eq_true, Bool.true_or, Bool.true_and, Bool.cond_true, BoundedContextIota.Mu.execute]

theorem evaluation_public (s a root : Nat) :
    evaluation (Nat.pair 1 (Nat.pair (Nat.pair s a) root)) =
      BoundedContextIota.Mu.Public.execute s a root := by
  cases h : BoundedContextIota.Mu.inputCheck s a root <;>
    simp [evaluation, inputCheck, outputCode, context, Nat.unpair_pair,
      BoundedContextIota.Mu.Public.execute, BoundedContextIota.Mu.execute, h]

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

theorem program_domain (mode s a root : Nat) :
    program.domain (Nat.pair mode (Nat.pair (Nat.pair s a) root)) ↔
      (mode = 0 ∨ mode = 1) ∧ BoundedContextIota.Mu.inputCheck s a root = true := by
  rw [Program.domain, program_eval, evaluation_domain, inputCheck_exact]

theorem program_native_spec (s a root out : Nat)
    (ho : out ∈ program.eval (Nat.pair 0 (Nat.pair (Nat.pair s a) root))) :
    BoundedContextIota.Mu.inputCheck s a root = true ∧
      lowCheckCode (BoundedContextIota.betaCode s a root) out = true ∧
      Comparison.acceptedCode (BoundedContextIota.betaCode s a root) out = true ∧
      interpretation (BoundedContextIota.betaCode s a root) out = BoundedContextIota.Mu.sourceValue s a root :=
  BoundedContextIota.Mu.execute_spec s a root out
    (by simpa only [program_eval, evaluation_native] using ho)

theorem program_public_spec (s a root out : Nat)
    (ho : out ∈ program.eval (Nat.pair 1 (Nat.pair (Nat.pair s a) root))) :
    BoundedContextIota.Mu.inputCheck s a root = true ∧ Canonical.check out = true ∧
      unionInterpretation out = BoundedContextIota.Mu.sourceValue s a root :=
  BoundedContextIota.Mu.Public.execute_spec s a root out
    (by simpa only [program_eval, evaluation_public] using ho)

theorem program_graph (query out : Nat) : out ∈ program.eval query ↔
    inputCheck query = true ∧ out = outputCode query := by
  rw [program_eval, evaluation_graph]

noncomputable def sourceColumn (mode s a : Nat) : Program :=
  (program.column mode).column (Nat.pair s a)

theorem sourceColumn_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => sourceColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const program) Primrec.fst)
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem sourceColumn_eval (mode s a root : Nat) :
    (sourceColumn mode s a).eval root = evaluation (Nat.pair mode (Nat.pair (Nat.pair s a) root)) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (mode s a root : Nat) : (sourceColumn mode s a).domain root ↔
    (mode = 0 ∨ mode = 1) ∧ BoundedContextIota.Mu.inputCheck s a root = true := by
  rw [Program.domain, sourceColumn_eval, evaluation_domain, inputCheck_exact]

theorem sourceColumn_graph (mode s a root out : Nat) : out ∈ (sourceColumn mode s a).eval root ↔
    inputCheck (Nat.pair mode (Nat.pair (Nat.pair s a) root)) = true ∧
      out = outputCode (Nat.pair mode (Nat.pair (Nat.pair s a) root)) := by
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

noncomputable def graphColumn (mode s a root : Nat) : Program :=
  graphProgram.column (Nat.pair mode (Nat.pair (Nat.pair s a) root))

theorem graphColumn_primrec : Primrec
    (fun p : Nat × BoundedContextIota.Context => graphColumn p.1 p.2.1.1 p.2.1.2 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (mode s a root out : Nat) : (graphColumn mode s a root).domain out ↔
    out ∈ (sourceColumn mode s a).eval root := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry]

end Alexander313.HereditaryBoundedContextMuProgram
