import Alexander313.Wilken.SourceOneNativeLambdaPublicBranchesRaw
import Alexander313.Wilken.SourceOneNativeMuPublic
import Alexander313.Computability

/-!
# Actual public Programs for original source-one lambda and mu

Modes zero/one execute BOTH lambda branches on the original normal/raw
proper-root domains; modes two/three execute normal/raw original mu.
Every returned code is genuinely canonical public at the actual formula
value. Fixed-mode and complete numerical graph columns are constructed
from the real evaluators. The graph predicate compares every output,
including zero; no primitive-recursive lambda producer is assumed.
Uncompiled candidates. Context-change mu invariance is separate.
-/

namespace Alexander313.SourceOneAuxiliaryPublicProgram

open Wilken.RelativeTerm.Hereditary

/-- One actual mode evaluator; all other numerical modes reject. -/
def evaluation (query : Nat) : Part Nat := cond (query.unpair.1 == 0)
  (SourceOneIota.Lambda.PublicBranches.execute query.unpair.2)
  (cond (query.unpair.1 == 1) (SourceOneIota.Lambda.PublicBranches.Raw.execute query.unpair.2)
    (cond (query.unpair.1 == 2) (SourceOneIota.Mu.Public.execute query.unpair.2)
      (cond (query.unpair.1 == 3) (SourceOneIota.Mu.Public.rawExecute query.unpair.2) Part.none)))

theorem evaluation_partrec : Partrec evaluation := by
  have hm := Primrec.fst.comp Primrec.unpair
  have ha := (Primrec.snd.comp Primrec.unpair).to_comp
  exact Partrec.cond (Primrec.beq.comp hm (Primrec.const 0)).to_comp
    (SourceOneIota.Lambda.PublicBranches.execute_partrec.comp ha)
    (Partrec.cond (Primrec.beq.comp hm (Primrec.const 1)).to_comp
      (SourceOneIota.Lambda.PublicBranches.Raw.execute_partrec.comp ha)
      (Partrec.cond (Primrec.beq.comp hm (Primrec.const 2)).to_comp
        (SourceOneIota.Mu.Public.execute_partrec.comp ha)
        (Partrec.cond (Primrec.beq.comp hm (Primrec.const 3)).to_comp
          (SourceOneIota.Mu.Public.rawExecute_partrec.comp ha) Partrec.none)))

theorem evaluation_normal_lambda (a : Nat) : evaluation (Nat.pair 0 a) =
    SourceOneIota.Lambda.PublicBranches.execute a := by simp [evaluation]

theorem evaluation_raw_lambda (a : Nat) : evaluation (Nat.pair 1 a) =
    SourceOneIota.Lambda.PublicBranches.Raw.execute a := by simp [evaluation]

theorem evaluation_normal_mu (a : Nat) : evaluation (Nat.pair 2 a) =
    SourceOneIota.Mu.Public.execute a := by simp [evaluation]

theorem evaluation_raw_mu (a : Nat) : evaluation (Nat.pair 3 a) =
    SourceOneIota.Mu.Public.rawExecute a := by simp [evaluation]

theorem evaluation_domain (mode a : Nat) : (evaluation (Nat.pair mode a)).Dom ↔
    (mode = 0 ∧ SourceOneIota.Lambda.PublicBranches.inputCheck a = true) ∨
    (mode = 1 ∧ SourceOneIota.Lambda.PublicBranches.Raw.inputCheck a = true) ∨
    (mode = 2 ∧ SourceOneIota.Mu.inputCheck a = true) ∨
    (mode = 3 ∧ SourceOneIota.Mu.Raw.inputCheck a = true) := by
  by_cases h0 : mode = 0
  · subst mode; simp [evaluation, SourceOneIota.Lambda.PublicBranches.execute_domain]
  · by_cases h1 : mode = 1
    · subst mode; simp [evaluation, SourceOneIota.Lambda.PublicBranches.Raw.execute_domain]
    · by_cases h2 : mode = 2
      · subst mode; simp [evaluation, SourceOneIota.Mu.Public.execute_domain]
      · by_cases h3 : mode = 3
        · subst mode; simp [evaluation, SourceOneIota.Mu.Public.rawExecute_domain]
        · simp [evaluation, h0, h1, h2, h3]

theorem evaluation_graph (mode a out : Nat) : out ∈ evaluation (Nat.pair mode a) ↔
    (mode = 0 ∧ out ∈ SourceOneIota.Lambda.PublicBranches.execute a) ∨
    (mode = 1 ∧ out ∈ SourceOneIota.Lambda.PublicBranches.Raw.execute a) ∨
    (mode = 2 ∧ out ∈ SourceOneIota.Mu.Public.execute a) ∨
    (mode = 3 ∧ out ∈ SourceOneIota.Mu.Public.rawExecute a) := by
  by_cases h0 : mode = 0
  · subst mode; simp [evaluation]
  · by_cases h1 : mode = 1
    · subst mode; simp [evaluation]
    · by_cases h2 : mode = 2
      · subst mode; simp [evaluation]
      · by_cases h3 : mode = 3
        · subst mode; simp [evaluation]
        · simp [evaluation, h0, h1, h2, h3]

theorem program_exists : ∃ p : Program, ∀ query, p.eval query = evaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def program : Program := Classical.choose program_exists

theorem program_eval (query : Nat) : program.eval query = evaluation query :=
  Classical.choose_spec program_exists query

theorem program_domain (mode a : Nat) : program.domain (Nat.pair mode a) ↔
    (mode = 0 ∧ SourceOneIota.Lambda.PublicBranches.inputCheck a = true) ∨
    (mode = 1 ∧ SourceOneIota.Lambda.PublicBranches.Raw.inputCheck a = true) ∨
    (mode = 2 ∧ SourceOneIota.Mu.inputCheck a = true) ∨
    (mode = 3 ∧ SourceOneIota.Mu.Raw.inputCheck a = true) := by
  rw [Program.domain, program_eval, evaluation_domain]

theorem program_canonical (mode a out : Nat) (ho : out ∈ program.eval (Nat.pair mode a)) :
    Canonical.check out = true := by
  rw [program_eval, evaluation_graph] at ho
  rcases ho with ⟨_, hn⟩ | ⟨_, hn⟩ | ⟨_, hn⟩ | ⟨_, hn⟩
  · exact (SourceOneIota.Lambda.PublicBranches.execute_spec a out hn).2.1
  · exact (SourceOneIota.Lambda.PublicBranches.Raw.execute_spec a out hn).2.1
  · exact (SourceOneIota.Mu.Public.execute_spec a out hn).2.1
  · exact (SourceOneIota.Mu.Public.rawExecute_spec a out hn).2.1

theorem program_normal_lambda_spec (a out : Nat) (ho : out ∈ program.eval (Nat.pair 0 a)) :
    SourceOneIota.Lambda.PublicBranches.inputCheck a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = SourceOneIota.Lambda.PublicBranches.sourceValue a := by
  rw [program_eval, evaluation_normal_lambda] at ho
  exact SourceOneIota.Lambda.PublicBranches.execute_spec a out ho

theorem program_raw_lambda_spec (a out : Nat) (ho : out ∈ program.eval (Nat.pair 1 a)) :
    SourceOneIota.Lambda.PublicBranches.Raw.inputCheck a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = SourceOneIota.Lambda.PublicBranches.Raw.sourceValue a := by
  rw [program_eval, evaluation_raw_lambda] at ho
  exact SourceOneIota.Lambda.PublicBranches.Raw.execute_spec a out ho

theorem program_normal_mu_spec (a out : Nat) (ho : out ∈ program.eval (Nat.pair 2 a)) :
    SourceOneIota.Mu.inputCheck a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = SourceOneIota.Mu.sourceValue a := by
  rw [program_eval, evaluation_normal_mu] at ho
  exact SourceOneIota.Mu.Public.execute_spec a out ho

theorem program_raw_mu_spec (a out : Nat) (ho : out ∈ program.eval (Nat.pair 3 a)) :
    SourceOneIota.Mu.Raw.inputCheck a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = SourceOneIota.Mu.sourceValue (SourceOneIota.Mu.Raw.normalizedRoot a) := by
  rw [program_eval, evaluation_raw_mu] at ho
  exact SourceOneIota.Mu.Public.rawExecute_spec a out ho

noncomputable def sourceColumn (mode : Nat) : Program := program.column mode

theorem sourceColumn_primrec : Primrec sourceColumn :=
  Program.column_primrec.comp (Primrec.const program) Primrec.id

theorem sourceColumn_eval (mode a : Nat) : (sourceColumn mode).eval a = evaluation (Nat.pair mode a) := by
  rw [sourceColumn, Nat.Partrec.Code.eval_curry, program_eval]

/-- Test the proposed numerical output after the actual partial evaluator. -/
def compareResult (query out : Nat) : Part Nat :=
  cond (out == query.unpair.2) (Part.some 0) Part.none

theorem compareResult_partrec : Partrec₂ compareResult :=
  (Partrec.cond (Primrec.beq.comp Primrec.snd
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to_comp
    (Computable.const 0).partrec Partrec.none).to₂

theorem compareResult_domain (query out : Nat) : (compareResult query out).Dom ↔ out = query.unpair.2 := by
  cases h : out == query.unpair.2 <;> simp [compareResult, h, beq_iff_eq] at *

def graphEvaluation (query : Nat) : Part Nat :=
  (evaluation query.unpair.1).bind (compareResult query)

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.bind (evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp) compareResult_partrec

theorem graphEvaluation_domain (query : Nat) : (graphEvaluation query).Dom ↔
    query.unpair.2 ∈ evaluation query.unpair.1 := by
  rw [graphEvaluation, Part.bind_dom]
  constructor
  · rintro ⟨h, hc⟩
    have he := (compareResult_domain query _).mp hc
    rw [← he]
    exact Part.get_mem h
  · intro ho
    refine ⟨ho.1, (compareResult_domain query _).mpr ?_⟩
    exact ho.2

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (mode a out : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair mode a) out) ↔ out ∈ program.eval (Nat.pair mode a) := by
  rw [Program.domain, Classical.choose_spec graphProgram_exists, graphEvaluation_domain, program_eval]
  simp only [Nat.unpair_pair]

noncomputable def graphColumn (mode a : Nat) : Program := graphProgram.column (Nat.pair mode a)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem graphColumn_domain (mode a out : Nat) : (graphColumn mode a).domain out ↔
    out ∈ (sourceColumn mode).eval a := by
  rw [graphColumn, Program.column_domain, graphProgram_domain, sourceColumn, Nat.Partrec.Code.eval_curry]

end Alexander313.SourceOneAuxiliaryPublicProgram
