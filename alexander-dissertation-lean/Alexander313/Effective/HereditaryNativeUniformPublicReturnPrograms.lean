import Alexander313.Wilken.HereditaryNativeUniformPublicReturn
import Alexander313.Computability

/-!
# Actual Programs for the whole coded-epsilon LOW public return

Every original raw LOW code at every admitted coded epsilon, including
noncanonical base spellings, has the genuine canonical SAME-value public
output. The actual original check alone is the complete executing domain.
Concrete s-m-n base/input columns and complete output graphs retain zero.
No endpoint, Normality, finite-level, supplied Program or return oracle.
These source-only candidates are uncompiled.
-/

namespace Alexander313.NativeUniformPublicReturnProgram

open Wilken.RelativeTerm.Hereditary.NativeContext
open Wilken.RelativeTerm.Hereditary.NativeContext.UniformPublicReturn

def queryGuard (query : Nat) : Bool := inputCheck query.unpair.1 query.unpair.2

def queryOutput (query : Nat) : Nat := publicCode query.unpair.1 query.unpair.2

theorem queryGuard_primrec : Primrec queryGuard :=
  inputCheck_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem queryOutput_primrec : Primrec queryOutput :=
  publicCode_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

def evaluation (query : Nat) : Part Nat :=
  cond (queryGuard query) (Part.some (queryOutput query)) Part.none

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.cond queryGuard_primrec.to_comp queryOutput_primrec.to_comp.partrec Partrec.none

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (q c : Nat) : program.eval (Nat.pair q c) = execute q c := by
  simpa only [evaluation, queryGuard, queryOutput, Nat.unpair_pair, execute] using
    Classical.choose_spec program_exists (Nat.pair q c)

/-- EVERY original raw LOW input at ANY coded epsilon is accepted, with
the original base spelling retained and no successor endpoint guard. -/
theorem program_domain (q c : Nat) : program.domain (Nat.pair q c) ↔ lowCheckCode q c = true := by
  rw [Program.domain, program_eval, execute_domain]

theorem program_graph (q c out : Nat) : out ∈ program.eval (Nat.pair q c) ↔
    lowCheckCode q c = true ∧ out = publicCode q c := by
  rw [program_eval, execute_graph]

theorem program_spec (q c out : Nat) (ho : out ∈ program.eval (Nat.pair q c)) :
    Wilken.RelativeTerm.Hereditary.Canonical.check out = true ∧
      Wilken.RelativeTerm.Hereditary.unionInterpretation out = interpretation q c := by
  rw [program_eval] at ho
  exact execute_spec q c out ho

/-- Literal canonical public output independence follows from the genuine
SAME-value producer, including different admitted coded-epsilon contexts. -/
theorem program_output_invariant (q v c d out other : Nat)
    (ho : out ∈ program.eval (Nat.pair q c))
    (hp : other ∈ program.eval (Nat.pair v d))
    (he : interpretation q c = interpretation v d) : out = other := by
  obtain ⟨hc, rfl⟩ := (program_graph q c out).mp ho
  obtain ⟨hd, rfl⟩ := (program_graph v d other).mp hp
  exact publicCode_value_invariant q v c d ((inputCheck_exact q c).mpr hc)
    ((inputCheck_exact v d).mpr hd) he

noncomputable def baseColumn (q : Nat) : Program := program.column q

theorem baseColumn_primrec : Primrec baseColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem baseColumn_graph (q c out : Nat) : out ∈ (baseColumn q).eval c ↔
    lowCheckCode q c = true ∧ out = publicCode q c := by
  rw [baseColumn, Nat.Partrec.Code.eval_curry]
  exact program_graph q c out

theorem baseColumn_spec (q c out : Nat) (ho : out ∈ (baseColumn q).eval c) :
    Wilken.RelativeTerm.Hereditary.Canonical.check out = true ∧
      Wilken.RelativeTerm.Hereditary.unionInterpretation out = interpretation q c := by
  obtain ⟨hc, rfl⟩ := (baseColumn_graph q c out).mp ho
  exact publicCode_spec q c ((inputCheck_exact q c).mpr hc)

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

theorem graphProgram_domain (q c out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair q c) out) ↔
      lowCheckCode q c = true ∧ out = publicCode q c := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists]
  simp only [graphEvaluation, graphBool, queryGuard, queryOutput, Nat.unpair_pair]
  cases h : inputCheck q c <;> cases he : out == publicCode q c <;>
    simp [h, he, Bool.eq_iff_iff, beq_iff_eq, ← inputCheck_exact] at *

noncomputable def graphColumn (q c : Nat) : Program := graphProgram.column (Nat.pair q c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem graphColumn_domain (q c out : Nat) : (graphColumn q c).domain out ↔
    out ∈ (baseColumn q).eval c := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, baseColumn_graph]

end Alexander313.NativeUniformPublicReturnProgram
