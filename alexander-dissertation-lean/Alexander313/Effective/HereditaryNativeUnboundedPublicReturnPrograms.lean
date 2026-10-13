import Alexander313.Wilken.HereditaryNativeUnboundedPublicReturn
import Alexander313.Computability

/-!
# Actual Programs for unbounded SAME-value public return

The original positive source high-root and the WHOLE original RAW LOW
alpha interval form the exact executing domain. Actual finite payload
return, normalized sum and complete same-index scalar recursion derive all
hidden callers. The genuine public producer and complete graph retain
output zero. Every source/root/output column uses the actual s-m-n compiler.
No endpoint, target Normality, supplied Program or return oracle. Uncompiled.
-/

namespace Alexander313.NativeUnboundedPublicReturnProgram

open Wilken.RelativeTerm.Hereditary.NativeContext
open Wilken.RelativeTerm.Hereditary.NativeContext.UnboundedPublicReturn

def queryGuard (query : Nat) : Bool :=
  inputCheck query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

def queryOutput (query : Nat) : Nat :=
  publicCode query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

theorem queryGuard_primrec : Primrec queryGuard :=
  inputCheck_primrec.comp ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))

theorem queryOutput_primrec : Primrec queryOutput :=
  publicCode_primrec.comp ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))

def evaluation (query : Nat) : Part Nat :=
  cond (queryGuard query) (Part.some (queryOutput query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond queryGuard_primrec.to_comp queryOutput_primrec.to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (s a c : Nat) : program.eval (Nat.pair (Nat.pair s a) c) = execute s a c := by
  simpa only [evaluation, queryGuard, queryOutput, Nat.unpair_pair, execute] using
    Classical.choose_spec program_exists (Nat.pair (Nat.pair s a) c)

theorem program_domain (s a c : Nat) : program.domain (Nat.pair (Nat.pair s a) c) ↔
    inputCheck s a c = true := by
  rw [Program.domain, program_eval, execute_dom]

theorem program_domain_original (s a c : Nat) : program.domain (Nat.pair (Nat.pair s a) c) ↔
    Iota.rootCheck s a = true ∧ lowCheckCode (Iota.alphaCode s a) c = true := by
  rw [program_domain, inputCheck_exact]

theorem program_graph (s a c out : Nat) : out ∈ program.eval (Nat.pair (Nat.pair s a) c) ↔
    inputCheck s a c = true ∧ out = publicCode s a c := by
  rw [program_eval, execute_graph]

theorem program_spec (s a c out : Nat) (ho : out ∈ program.eval (Nat.pair (Nat.pair s a) c)) :
    Wilken.RelativeTerm.Hereditary.Canonical.check out = true ∧
      Wilken.RelativeTerm.Hereditary.unionInterpretation out = interpretation (Iota.alphaCode s a) c := by
  rw [program_eval] at ho
  exact execute_spec s a c out ho

noncomputable def sourceColumn (s a : Nat) : Program := program.column (Nat.pair s a)

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem sourceColumn_graph (s a c out : Nat) : out ∈ (sourceColumn s a).eval c ↔
    inputCheck s a c = true ∧ out = publicCode s a c := by
  rw [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph s a c out

theorem sourceColumn_spec (s a c out : Nat) (ho : out ∈ (sourceColumn s a).eval c) :
    Wilken.RelativeTerm.Hereditary.Canonical.check out = true ∧
      Wilken.RelativeTerm.Hereditary.unionInterpretation out = interpretation (Iota.alphaCode s a) c := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph s a c out).mp ho
  exact publicCode_spec s a c hi

def graphBool (query : Nat) : Bool :=
  queryGuard query.unpair.1 && (query.unpair.2 == queryOutput query.unpair.1)

theorem graphBool_primrec : Primrec graphBool :=
  Primrec.and.comp (queryGuard_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.beq.comp (Primrec.snd.comp Primrec.unpair)
      (queryOutput_primrec.comp (Primrec.fst.comp Primrec.unpair)))

def graphEvaluation (query : Nat) : Part Nat := cond (graphBool query) (Part.some 0) Part.none

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.cond graphBool_primrec.to_comp (Computable.const 0).partrec Partrec.none

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (s a c out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair (Nat.pair s a) c) out) ↔
      inputCheck s a c = true ∧ out = publicCode s a c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, queryGuard, queryOutput, Nat.unpair_pair]
  cases h : inputCheck s a c <;> cases he : out == publicCode s a c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq] at *

noncomputable def graphColumn (s a c : Nat) : Program := graphProgram.column (Nat.pair (Nat.pair s a) c)

theorem graphColumn_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => graphColumn p.1.1 p.1.2 p.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem graphColumn_domain (s a c out : Nat) : (graphColumn s a c).domain out ↔
    out ∈ (sourceColumn s a).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_graph]


end Alexander313.NativeUnboundedPublicReturnProgram
