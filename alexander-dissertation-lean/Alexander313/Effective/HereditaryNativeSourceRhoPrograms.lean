import Alexander313.Wilken.HereditaryNativeSourceRho

/-!
# Actual rho Programs and executing literal output graph

The producer executes the actual canonical logarithm/decomposition searches,
finite chi and dotted-right-subtraction kernels, and real multiplication.
Its exact domain is EVERY original native LOW input in contextCode s. The
positive numerical graph executes that producer and checks its literal chosen
output, including zero. It is Partrec; no total graph-decision or global PR
search bound is asserted. All source/graph column compilers are genuine PR.
These are uncompiled proof candidates; source3.12's height claim is absent.
-/

namespace Alexander313.HereditaryNativeSourceRhoProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext (SourceRho)

def evaluation (query : Nat) : Part Nat := SourceRho.rho query.unpair.1 query.unpair.2

theorem evaluation_partrec : Partrec evaluation :=
  SourceRho.rho_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (s c : Nat) : program.eval (Nat.pair s c) = SourceRho.rho s c := by
  simpa only [evaluation, Nat.unpair_pair] using Classical.choose_spec program_exists (Nat.pair s c)

theorem program_domain (s c : Nat) : program.domain (Nat.pair s c) ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  rw [Program.domain, program_eval, SourceRho.rho_domain]
  rfl

theorem program_spec (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    SourceRho.inputCheck s c = true ∧ NativeContext.LowArithmetic.lowInput s out = true ∧
      NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) out = true ∧
      ∃ p, SourceRho.Prepared s c p ∧ NativeContext.interpretation (NativePublicBridge.contextCode s) out =
        NativeContext.base (NativePublicBridge.contextCode s) * Wilken.OrdinalRightSubtraction.rightSubtract
          (unionInterpretation (SourceRho.logCode p)) (SourceRho.chiNat s p : Ordinal.{0}) := by
  rw [program_eval] at ho
  exact SourceRho.rho_spec s c out ho

theorem program_definition_3_11 (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    SourceRho.inputCheck s c = true ∧ NativeContext.LowArithmetic.lowInput s out = true ∧
    NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) out = true ∧ ∃ p,
      SourceRho.Prepared s c p ∧
      LogEnd.SourceLogSpec true (NativeContext.interpretation (NativePublicBridge.contextCode s) c)
        (unionInterpretation (SourceRho.logCode p)) ∧
      NativeContext.LowArithmetic.lowInput s (SourceRho.lambdaCode s p) = true ∧
      NativeContext.Comparison.acceptedCode (NativePublicBridge.contextCode s) (SourceRho.lambdaCode s p) = true ∧
      (NativeContext.interpretation (NativePublicBridge.contextCode s) (SourceRho.lambdaCode s p) = 0 ∨
        _root_.Order.IsSuccLimit (NativeContext.interpretation (NativePublicBridge.contextCode s) (SourceRho.lambdaCode s p))) ∧
      unionInterpretation (SourceRho.logCode p) =
        NativeContext.interpretation (NativePublicBridge.contextCode s) (SourceRho.lambdaCode s p) +
          (SourceRho.remainder p : Ordinal.{0}) ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) out =
        NativeContext.base (NativePublicBridge.contextCode s) * Wilken.OrdinalRightSubtraction.rightSubtract
          (unionInterpretation (SourceRho.logCode p)) (SourceRho.chiNat s p : Ordinal.{0}) := by
  rw [program_eval] at ho
  exact SourceRho.source_definition_3_11 s c out ho

theorem program_bound (s c out : Nat) (ho : out ∈ program.eval (Nat.pair s c)) :
    ∃ p, SourceRho.Prepared s c p ∧ NativeContext.interpretation (NativePublicBridge.contextCode s) out ≤
      NativeContext.base (NativePublicBridge.contextCode s) * unionInterpretation (SourceRho.logCode p) := by
  rw [program_eval] at ho
  exact SourceRho.source_lemma_3_12_bound s c out ho

theorem program_returns (s c : Nat) (hc : SourceRho.inputCheck s c = true) :
    ∃ out, out ∈ program.eval (Nat.pair s c) := by
  rw [program_eval]
  exact SourceRho.rho_returns s c hc

theorem program_output_unique (s c out out' : Nat)
    (ho : out ∈ program.eval (Nat.pair s c)) (ho' : out' ∈ program.eval (Nat.pair s c)) : out = out' :=
  Part.mem_unique ho ho'

theorem program_output_invariant (s c d out out' : Nat)
    (ho : out ∈ program.eval (Nat.pair s c)) (ho' : out' ∈ program.eval (Nat.pair s d))
    (hv : NativeContext.interpretation (NativePublicBridge.contextCode s) c =
      NativeContext.interpretation (NativePublicBridge.contextCode s) d) : out = out' := by
  rw [program_eval] at ho ho'
  exact SourceRho.rho_output_invariant s c d out out' ho ho' hv

noncomputable def sourceColumn (s : Nat) : Program := program.column s

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_eval (s c : Nat) : (sourceColumn s).eval c = SourceRho.rho s c := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_domain (s c : Nat) : (sourceColumn s).domain c ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  simp only [sourceColumn, Program.column_domain]
  exact program_domain s c

def inputEvaluation (query : Nat) : Part Nat := cond
  (SourceRho.inputCheck query.unpair.1 query.unpair.2) (Part.some 1) Part.none

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.cond (SourceRho.inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp (Computable.const 1).partrec Partrec.none

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.eval query = inputEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_eval (s c : Nat) : inputProgram.eval (Nat.pair s c) =
    cond (SourceRho.inputCheck s c) (Part.some 1) Part.none := by
  simpa only [inputEvaluation, Nat.unpair_pair] using Classical.choose_spec inputProgram_exists (Nat.pair s c)

theorem inputProgram_domain (s c : Nat) : inputProgram.domain (Nat.pair s c) ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  rw [Program.domain, inputProgram_eval]
  change (cond (SourceRho.inputCheck s c) (Part.some 1) Part.none).Dom ↔ SourceRho.inputCheck s c = true
  cases h : SourceRho.inputCheck s c <;> simp [h, Part.none, Part.some]

noncomputable def inputColumn (s : Nat) : Program := inputProgram.column s

theorem inputColumn_primrec : Primrec inputColumn :=
  Program.column_primrec.comp (Primrec.const inputProgram) Primrec.id

theorem inputColumn_domain (s c : Nat) : (inputColumn s).domain c ↔
    NativeContext.lowCheckCode (NativePublicBridge.contextCode s) c = true := by
  simp only [inputColumn, Program.column_domain]
  exact inputProgram_domain s c

def graph (s c out : Nat) : Part Nat := (SourceRho.rho s c).bind
  (fun actual => cond (actual == out) (Part.some 1) Part.none)

theorem graph_partrec : Partrec (fun p : Nat × (Nat × Nat) => graph p.1 p.2.1 p.2.2) := by
  have hr := SourceRho.rho_partrec.comp Computable.fst (Computable.fst.comp Computable.snd)
  have he : Computable (fun p : (Nat × (Nat × Nat)) × Nat =>
      p.2 == p.1.2.2) := (Primrec.beq.comp Primrec.snd
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to_comp
  exact hr.bind (Partrec.cond he (Computable.const 1).partrec Partrec.none).to₂

theorem graph_domain (s c out : Nat) : (graph s c out).Dom ↔ out ∈ SourceRho.rho s c := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨answer, ha⟩
    obtain ⟨actual, hr, ht⟩ := Part.mem_bind_iff.mp ha
    cases he : actual == out with
    | false => simp only [he, Bool.cond_false, Part.notMem_none] at ht
    | true => exact (beq_iff_eq.mp he) ▸ hr
  · intro ho
    exact ⟨1, Part.mem_bind_iff.mpr ⟨out, ho, by simp only [beq_self_eq_true, Bool.cond_true]; exact Part.mem_some 1⟩⟩

def graphEvaluation (query : Nat) : Part Nat := graph query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  graph_partrec.comp ((Primrec.fst.comp Primrec.unpair).pair
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (s c out : Nat) : graphProgram.eval (Nat.pair s (Nat.pair c out)) = graph s c out := by
  simpa only [graphEvaluation, Nat.unpair_pair] using
    Classical.choose_spec graphProgram_exists (Nat.pair s (Nat.pair c out))

theorem graphProgram_domain (s c out : Nat) : graphProgram.domain (Nat.pair s (Nat.pair c out)) ↔
    out ∈ SourceRho.rho s c := by
  rw [Program.domain, graphProgram_eval, graph_domain]

noncomputable def graphColumn (s c : Nat) : Program := (graphProgram.column s).column c

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Program.column_primrec.comp (Primrec.const graphProgram) Primrec.fst) Primrec.snd).to₂

theorem graphColumn_eval (s c out : Nat) : (graphColumn s c).eval out = graph s c out := by
  simp only [graphColumn, Nat.Partrec.Code.eval_curry, graphProgram_eval]

theorem graphColumn_domain (s c out : Nat) : (graphColumn s c).domain out ↔ out ∈ SourceRho.rho s c := by
  simp only [graphColumn, Program.column_domain]
  exact graphProgram_domain s c out

end Alexander313.HereditaryNativeSourceRhoProgram
