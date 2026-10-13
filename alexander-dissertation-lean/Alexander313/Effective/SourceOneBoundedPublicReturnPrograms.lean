import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnCodes
import Alexander313.Computability

/-!
# Programs for the original source-one bounded SAME-value return

This actual finite producer accepts exactly original raw alpha LOW inputs
below original source alpha-plus. It returns a canonical public code at the
SAME ordinal value. Genuine normal/raw lambda and mu outputs supply the
caller. Numerical graphs and fixed-root/output columns retain output zero.
No native parser at base one or supplied translation interface. Uncompiled.
-/

namespace Alexander313.SourceOneBoundedPublicReturnProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn

/-- The actual binary source-one guard on a numerical pair. -/
def queryGuard (query : Nat) : Bool := inputCheck query.unpair.1 query.unpair.2

def queryOutput (query : Nat) : Nat := publicCode query.unpair.1 query.unpair.2

theorem queryGuard_primrec : Primrec queryGuard := inputCheck_primrec.comp Primrec.unpair

theorem queryOutput_primrec : Primrec queryOutput := publicCode_primrec.comp Primrec.unpair

def evaluation (query : Nat) : Part Nat :=
  cond (queryGuard query) (Part.some (queryOutput query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond queryGuard_primrec.to_comp queryOutput_primrec.to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (a c : Nat) : program.eval (Nat.pair a c) = execute a c := by
  simpa only [evaluation, queryGuard, queryOutput, Nat.unpair_pair, execute] using
    Classical.choose_spec program_exists (Nat.pair a c)

theorem program_domain (a c : Nat) : program.domain (Nat.pair a c) ↔ inputCheck a c = true := by
  rw [Program.domain, program_eval, execute_dom]

theorem program_domain_original (a c : Nat) : program.domain (Nat.pair a c) ↔
    SourceOneIota.rootCheck a = true ∧ NativeContext.lowCheckCode (SourceOneIota.alphaCode a) c = true ∧
      NativeContext.interpretation (SourceOneIota.alphaCode a) c < SourceOneIota.Enclosure.sourceAlphaPlus a := by
  rw [program_domain, inputCheck_exact]

theorem program_graph (a c out : Nat) : out ∈ program.eval (Nat.pair a c) ↔
    inputCheck a c = true ∧ out = publicCode a c := by
  rw [program_eval, execute_graph]

theorem program_spec (a c out : Nat) (ho : out ∈ program.eval (Nat.pair a c)) :
    Canonical.check out = true ∧
      unionInterpretation out = NativeContext.interpretation (SourceOneIota.alphaCode a) c := by
  rw [program_eval] at ho
  exact execute_spec a c out ho

noncomputable def sourceColumn (a : Nat) : Program := program.column a

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_domain (a c : Nat) : (sourceColumn a).domain c ↔ inputCheck a c = true := by
  rw [sourceColumn, Program.column_domain]
  exact program_domain a c

theorem sourceColumn_graph (a c out : Nat) : out ∈ (sourceColumn a).eval c ↔
    inputCheck a c = true ∧ out = publicCode a c := by
  rw [sourceColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph a c out

theorem sourceColumn_spec (a c out : Nat) (ho : out ∈ (sourceColumn a).eval c) :
    Canonical.check out = true ∧
      unionInterpretation out = NativeContext.interpretation (SourceOneIota.alphaCode a) c := by
  obtain ⟨hi, rfl⟩ := (sourceColumn_graph a c out).mp ho
  exact publicCode_spec a c hi

/-- The complete numerical graph includes output zero. -/
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

theorem graphProgram_domain (a c out : Nat) : graphProgram.domain (Nat.pair (Nat.pair a c) out) ↔
    inputCheck a c = true ∧ out = publicCode a c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, queryGuard, queryOutput, Nat.unpair_pair]
  cases h : inputCheck a c <;> cases he : out == publicCode a c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq] at *

noncomputable def graphColumn (a c : Nat) : Program := graphProgram.column (Nat.pair a c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem graphColumn_domain (a c out : Nat) : (graphColumn a c).domain out ↔
    out ∈ (sourceColumn a).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn_graph]

theorem lambda_program_caller (a out : Nat) (ho : out ∈ SourceOneIota.Lambda.execute a) :
    publicCode a out ∈ (sourceColumn a).eval out :=
  (sourceColumn_graph a out _).mpr ⟨lambda_caller a out ho, rfl⟩

theorem raw_lambda_program_caller (a out : Nat) (ho : out ∈ SourceOneIota.Lambda.Raw.execute a) :
    publicCode (SourceOneIota.Lambda.Raw.normalizedRoot a) out ∈
      (sourceColumn (SourceOneIota.Lambda.Raw.normalizedRoot a)).eval out :=
  (sourceColumn_graph _ out _).mpr ⟨raw_lambda_caller a out ho, rfl⟩

theorem mu_program_caller (a out : Nat) (ho : out ∈ SourceOneIota.Mu.execute a) :
    publicCode a out ∈ (sourceColumn a).eval out :=
  (sourceColumn_graph a out _).mpr ⟨mu_caller a out ho, rfl⟩

theorem raw_mu_program_caller (a out : Nat) (ho : out ∈ SourceOneIota.Mu.Raw.execute a) :
    publicCode (SourceOneIota.Mu.Raw.normalizedRoot a) out ∈
      (sourceColumn (SourceOneIota.Mu.Raw.normalizedRoot a)).eval out :=
  (sourceColumn_graph _ out _).mpr ⟨raw_mu_caller a out ho, rfl⟩

end Alexander313.SourceOneBoundedPublicReturnProgram
