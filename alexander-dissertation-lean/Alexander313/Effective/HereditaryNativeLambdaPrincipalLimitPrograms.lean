import Alexander313.Wilken.HereditaryNativeLambdaPrincipalLimitDecision
import Alexander313.Computability

/-!
# Actual normal/raw principal-limit decision Programs

Mode0 runs the genuine original normal-root decision; mode1 runs the genuine
original raw-root decision. Invalid roots and all other modes return numerical
zero. Every valid root returns one exactly for membership in the ORIGINAL
source class L. The chosen actual Program is total, has literal mode/source
columns, and its complete numerical graph includes both zero and one outputs.
No ordinal, branch, decision or execution oracle is a premise. Uncompiled.
-/

namespace Alexander313.HereditaryNativeLambdaPrincipalLimitProgram

open Wilken.RelativeTerm.Hereditary
open NativeContext
open NativePublicBridge (contextCode)

/-- The exact original guard and source class recognized by the executing
mode:0 is original normal admission;1 is original raw admission. -/
def Recognizes (mode s a : Nat) : Prop :=
  ((mode = 0 ∧ Lambda.Branches.inputCheck s a = true) ∨
    (mode = 1 ∧ Lambda.Branches.Raw.inputCheck s a = true)) ∧
      Lambda.PrincipalLimits.PrincipalLimit (interpretation (contextCode s) a)

def answer (query : Nat) : Bool := cond (query.unpair.1 == 0)
  (Lambda.PrincipalLimits.check query.unpair.2.unpair.1 query.unpair.2.unpair.2)
  (cond (query.unpair.1 == 1)
    (Lambda.PrincipalLimits.rawCheck query.unpair.2.unpair.1 query.unpair.2.unpair.2) false)

theorem answer_computable : Computable answer := by
  have hm := Primrec.fst.comp Primrec.unpair
  have hs := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have ha := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact ((Primrec.beq.comp hm (Primrec.const 0)).to_comp.cond
    (Lambda.PrincipalLimits.check_computable.comp hs.to_comp ha.to_comp)
    ((Primrec.beq.comp hm (Primrec.const 1)).to_comp.cond
      (Lambda.PrincipalLimits.rawCheck_computable.comp hs.to_comp ha.to_comp)
      (Computable.const false)))

theorem answer_exact (mode s a : Nat) :
    answer (Nat.pair mode (Nat.pair s a)) = true ↔ Recognizes mode s a := by
  by_cases h0 : mode = 0
  · subst mode
    simp [answer, Recognizes, Nat.unpair_pair, Lambda.PrincipalLimits.check_exact]
  · by_cases h1 : mode = 1
    · subst mode
      simp [answer, Recognizes, Nat.unpair_pair, Lambda.PrincipalLimits.rawCheck_exact]
    · simp [answer, Recognizes, Nat.unpair_pair, h0, h1]

def value (query : Nat) : Nat := cond (answer query) 1 0

theorem value_computable : Computable value :=
  answer_computable.cond (Computable.const 1) (Computable.const 0)

def evaluation (query : Nat) : Part Nat := Part.some (value query)

theorem evaluation_partrec : Partrec evaluation := value_computable.partrec

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (mode s a : Nat) : program.eval (Nat.pair mode (Nat.pair s a)) =
    Part.some (value (Nat.pair mode (Nat.pair s a))) :=
  Classical.choose_spec program_exists _

theorem program_total (query : Nat) : program.domain query := by
  rw [Program.domain, Classical.choose_spec program_exists]
  exact Part.some_dom _

/-- COMPLETE numerical graph: both recognized1 and rejected/non-L0 outputs
are retained. Invalid original roots and invalid modes are genuine0 outputs. -/
theorem program_graph (mode s a out : Nat) : out ∈ program.eval (Nat.pair mode (Nat.pair s a)) ↔
    (out = 1 ∧ Recognizes mode s a) ∨ (out = 0 ∧ ¬ Recognizes mode s a) := by
  rw [program_eval, Part.mem_some_iff]
  have hx := answer_exact mode s a
  by_cases hb : answer (Nat.pair mode (Nat.pair s a)) = true
  · have hyes := hx.mp hb
    simp only [value, hb, Bool.cond_true, hyes, and_true, not_true_eq_false,
      and_false, or_false]
  · have hf := Bool.eq_false_of_not_eq_true hb
    have hnot : ¬ Recognizes mode s a := fun h => hb (hx.mpr h)
    simp only [value, hf, Bool.cond_false, hnot, false_and, and_false, not_false_eq_true,
      and_true, false_or]

theorem program_one (mode s a : Nat) : 1 ∈ program.eval (Nat.pair mode (Nat.pair s a)) ↔
    Recognizes mode s a := by
  simp only [program_graph, one_ne_zero, false_and, or_false, true_and]

theorem program_zero (mode s a : Nat) : 0 ∈ program.eval (Nat.pair mode (Nat.pair s a)) ↔
    ¬ Recognizes mode s a := by
  simp only [program_graph, zero_ne_one, false_and, false_or, true_and]

noncomputable def sourceColumn (mode s : Nat) : Program := (program.column mode).column s

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const program) Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (mode s a : Nat) : (sourceColumn mode s).eval a =
    Part.some (value (Nat.pair mode (Nat.pair s a))) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

theorem sourceColumn_graph (mode s a out : Nat) : out ∈ (sourceColumn mode s).eval a ↔
    (out = 1 ∧ Recognizes mode s a) ∨ (out = 0 ∧ ¬ Recognizes mode s a) := by
  simp only [sourceColumn, Nat.Partrec.Code.eval_curry, program_graph]

/-- The numerical graph checker always emits0 on a matching COMPLETE graph
row, including rows where the decision Program's actual output itself is0. -/
def graphEvaluation (query : Nat) : Part Nat :=
  (evaluation query.unpair.1).bind (fun out =>
    cond (query.unpair.2 == out) (Part.some 0) Part.none)

theorem graphEvaluation_partrec : Partrec graphEvaluation := by
  have hp := evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have he : Computable (fun p : Nat × Nat => p.1.unpair.2 == p.2) :=
    (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd).to_comp
  exact Partrec.bind hp (Partrec.cond he (Computable.const 0).partrec Partrec.none).to₂

theorem graphEvaluation_domain (query out : Nat) :
    (graphEvaluation (Nat.pair query out)).Dom ↔ out ∈ evaluation query := by
  simp only [graphEvaluation, Nat.unpair_pair, Part.dom_iff_mem]
  constructor
  · rintro ⟨result, hm⟩
    obtain ⟨actual, hv, he⟩ := Part.mem_bind_iff.mp hm
    by_cases h : out = actual
    · subst actual; exact hv
    · simp [h, Part.notMem_none] at he
  · intro ho
    exact ⟨0, Part.mem_bind_iff.mpr ⟨out, ho, by simp⟩⟩

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (mode s a out : Nat) : graphProgram.domain
    (Nat.pair (Nat.pair mode (Nat.pair s a)) out) ↔
      (out = 1 ∧ Recognizes mode s a) ∨ (out = 0 ∧ ¬ Recognizes mode s a) := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists, graphEvaluation_domain]
  have he : evaluation (Nat.pair mode (Nat.pair s a)) =
      program.eval (Nat.pair mode (Nat.pair s a)) :=
    (Classical.choose_spec program_exists _).symm
  rw [he, program_graph]

noncomputable def graphColumn (mode s a : Nat) : Program :=
  graphProgram.column (Nat.pair mode (Nat.pair s a))

theorem graphColumn_primrec : Primrec (fun p : Nat × Nat × Nat => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (mode s a out : Nat) : (graphColumn mode s a).domain out ↔
    (out = 1 ∧ Recognizes mode s a) ∨ (out = 0 ∧ ¬ Recognizes mode s a) := by
  rw [graphColumn, Program.column_domain, graphProgram_domain]

end Alexander313.HereditaryNativeLambdaPrincipalLimitProgram
