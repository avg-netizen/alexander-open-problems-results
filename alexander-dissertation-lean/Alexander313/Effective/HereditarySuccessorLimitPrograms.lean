import Alexander313.Wilken.HereditarySuccessorLimit
import Alexander313.Effective.HereditaryFinitePowerPrograms

/-!
# Actual successor/limit decisions and canonical predecessor Programs

Total 0/1 decisions and positive Programs execute the genuine guarded
decomposition decisions. Tags 0,1,2,3 select zero, nonzero limit, successor,
and zero-or-limit respectively. Unknown tags reject. The predecessor Program
executes the constructed canonical predecessor on exactly original successors.
Its positive output graph executes that routine and checks literal equality.
PR compiler maps specialize actual fixed Program kernels. Execution is not
claimed PR; every proof remains an uncompiled source candidate.
-/

namespace Alexander313.HereditarySuccessorLimitProgram

open Wilken.RelativeTerm.Hereditary

def positiveCheck (tag q : Nat) : Bool :=
  cond (tag == 3) (SuccessorLimit.prelimitCheck q) (SuccessorLimit.check tag q)

theorem positiveCheck_computable : Computable₂ positiveCheck :=
  ((Primrec.beq.comp Primrec.fst (Primrec.const 3)).to_comp.cond
    (SuccessorLimit.prelimitCheck_computable.comp Computable.snd)
    SuccessorLimit.check_computable).to₂

def decisionOutput (input : Nat) : Nat :=
  cond (positiveCheck input.unpair.1 input.unpair.2) 1 0

theorem decisionOutput_computable : Computable decisionOutput :=
  (positiveCheck_computable.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp).cond (Computable.const 1) (Computable.const 0)

theorem decisionOutput_one (tag q : Nat) : decisionOutput (Nat.pair tag q) = 1 ↔ positiveCheck tag q = true := by
  cases h : positiveCheck tag q <;> simp [decisionOutput, Nat.unpair_pair, h]

theorem decisionOutput_zero (tag q : Nat) : decisionOutput (Nat.pair tag q) = 0 ↔ positiveCheck tag q = false := by
  cases h : positiveCheck tag q <;> simp [decisionOutput, Nat.unpair_pair, h]

theorem decisionProgram_exists : ∃ p : Program, ∀ input, p.eval input = Part.some (decisionOutput input) :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionOutput_computable.partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (input : Nat) : decisionProgram.eval input = Part.some (decisionOutput input) :=
  Classical.choose_spec decisionProgram_exists input

theorem decisionProgram_total (input : Nat) : decisionProgram.domain input := by
  simp only [Program.domain, decisionProgram_eval]
  exact Part.some_dom _

theorem decisionProgram_one (tag q : Nat) : 1 ∈ decisionProgram.eval (Nat.pair tag q) ↔ positiveCheck tag q = true := by
  simpa only [decisionProgram_eval, Part.mem_some_iff, eq_comm] using decisionOutput_one tag q

theorem decisionProgram_zero (tag q : Nat) : 0 ∈ decisionProgram.eval (Nat.pair tag q) ↔ positiveCheck tag q = false := by
  simpa only [decisionProgram_eval, Part.mem_some_iff, eq_comm] using decisionOutput_zero tag q

noncomputable def decisionColumn (tag : Nat) : Program := decisionProgram.column tag

theorem decisionColumn_primrec : Primrec decisionColumn :=
  Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.id

theorem decisionColumn_total (tag q : Nat) : (decisionColumn tag).domain q := by
  rw [decisionColumn, Program.column_domain]
  exact decisionProgram_total _

private def positiveConstant (query : Nat) (_ : Nat) : Bool := positiveCheck query.unpair.1 query.unpair.2

private theorem positiveConstant_computable : Computable₂ positiveConstant :=
  ((positiveCheck_computable.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp).comp Computable.fst).to₂

def positiveEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (positiveConstant query witness))

theorem positiveEvaluation_partrec : Partrec positiveEvaluation :=
  Partrec.rfind positiveConstant_computable.partrec₂

theorem positiveEvaluation_domain (query : Nat) : (positiveEvaluation query).Dom ↔
    positiveCheck query.unpair.1 query.unpair.2 = true := by
  simp [positiveEvaluation, positiveConstant, Nat.rfind_dom, eq_comm]

theorem positiveProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ positiveCheck query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp positiveEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using positiveEvaluation_domain query

noncomputable def positiveProgram : Program := Classical.choose positiveProgram_exists
noncomputable def positiveColumn (tag : Nat) : Program := positiveProgram.column tag

theorem positiveColumn_primrec : Primrec positiveColumn :=
  Program.column_primrec.comp (Primrec.const positiveProgram) Primrec.id

theorem positiveColumn_domain (tag q : Nat) : (positiveColumn tag).domain q ↔ positiveCheck tag q = true := by
  rw [positiveColumn, Program.column_domain, Classical.choose_spec positiveProgram_exists]
  simp only [Nat.unpair_pair]

noncomputable def zeroProgram : Program := positiveColumn 0
noncomputable def limitProgram : Program := positiveColumn 1
noncomputable def successorProgram : Program := positiveColumn 2
noncomputable def prelimitProgram : Program := positiveColumn 3

theorem zeroProgram_domain (q : Nat) : zeroProgram.domain q ↔ unionCheck q = true ∧ unionInterpretation q = 0 := by
  simpa [zeroProgram, positiveCheck, SuccessorLimit.check_exact, SuccessorLimit.Meaning]
    using positiveColumn_domain 0 q

theorem limitProgram_domain (q : Nat) : limitProgram.domain q ↔ unionCheck q = true ∧ Order.IsSuccLimit (unionInterpretation q) := by
  simpa [limitProgram, positiveCheck, SuccessorLimit.check_exact, SuccessorLimit.Meaning]
    using positiveColumn_domain 1 q

theorem successorProgram_domain (q : Nat) : successorProgram.domain q ↔
    unionCheck q = true ∧ ¬ Order.IsSuccPrelimit (unionInterpretation q) := by
  simpa [successorProgram, positiveCheck, SuccessorLimit.check_exact, SuccessorLimit.Meaning]
    using positiveColumn_domain 2 q

theorem prelimitProgram_domain (q : Nat) : prelimitProgram.domain q ↔
    unionCheck q = true ∧ Order.IsSuccPrelimit (unionInterpretation q) := by
  simpa [prelimitProgram, positiveCheck, SuccessorLimit.prelimitCheck_exact] using positiveColumn_domain 3 q

theorem positiveColumn_unknown (tag q : Nat) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ¬ (positiveColumn tag).domain q := by
  rw [positiveColumn_domain]
  simp [positiveCheck, h3, SuccessorLimit.check_exact, SuccessorLimit.Meaning, h0, h1, h2]

theorem predecessorProgram_exists : ∃ p : Program, ∀ q, p.eval q = SuccessorLimit.predecessor q :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp SuccessorLimit.predecessor_partrec)

noncomputable def predecessorProgram : Program := Classical.choose predecessorProgram_exists

theorem predecessorProgram_eval (q : Nat) : predecessorProgram.eval q = SuccessorLimit.predecessor q :=
  Classical.choose_spec predecessorProgram_exists q

theorem predecessorProgram_domain (q : Nat) : predecessorProgram.domain q ↔
    unionCheck q = true ∧ ¬ Order.IsSuccPrelimit (unionInterpretation q) := by
  simp only [Program.domain, predecessorProgram_eval, SuccessorLimit.predecessor_domain]

theorem predecessorProgram_graph_iff (q c : Nat) : c ∈ predecessorProgram.eval q ↔
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c + 1 = unionInterpretation q := by
  rw [predecessorProgram_eval]
  exact SuccessorLimit.predecessor_graph_iff q c

theorem predecessorProgram_value (q c : Nat) (hc : c ∈ predecessorProgram.eval q) :
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c + 1 = unionInterpretation q ∧
      unionInterpretation c = Ordinal.pred (unionInterpretation q) := by
  rw [predecessorProgram_eval] at hc
  exact SuccessorLimit.predecessor_value q c hc

theorem predecessorProgram_returns (q : Nat) (hq : SuccessorLimit.successorCheck q = true) :
    ∃ c, c ∈ predecessorProgram.eval q ∧ Canonical.check c = true ∧
      unionInterpretation c + 1 = unionInterpretation q ∧ unionInterpretation c = Ordinal.pred (unionInterpretation q) := by
  rw [predecessorProgram_eval]
  exact SuccessorLimit.predecessor_returns q hq

theorem predecessorProgram_unique (q : Nat) (hq : SuccessorLimit.successorCheck q = true) :
    ∃! c, c ∈ predecessorProgram.eval q := by
  obtain ⟨c, hc, _⟩ := predecessorProgram_returns q hq
  exact ⟨c, hc, fun d hd => Part.mem_unique hd hc⟩

theorem predecessorProgram_invariant (q v c d : Nat) (hc : c ∈ predecessorProgram.eval q)
    (hd : d ∈ predecessorProgram.eval v) (he : unionInterpretation q = unionInterpretation v) : c = d := by
  rw [predecessorProgram_eval] at hc hd
  exact SuccessorLimit.predecessor_invariant q v c d hc hd he

def graphEvaluation (query : Nat) : Part Nat :=
  (SuccessorLimit.predecessor query.unpair.1).bind (HereditaryFinitePowerProgram.outputTest query)

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  (SuccessorLimit.predecessor_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp).bind
    HereditaryFinitePowerProgram.outputTest_partrec

theorem graphEvaluation_domain (q c : Nat) : (graphEvaluation (Nat.pair q c)).Dom ↔ c ∈ SuccessorLimit.predecessor q := by
  constructor
  · intro hd
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨d, hd, ht⟩ := Part.mem_bind_iff.mp ha
    have hp : d ∈ SuccessorLimit.predecessor q := by simpa only [Nat.unpair_pair] using hd
    cases he : d == c with
    | false =>
      have hf : False := by simpa [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair, he] using ht
      exact hf.elim
    | true => rw [← beq_iff_eq.mp he]; exact hp
  · intro hc
    apply Part.dom_iff_mem.mpr
    refine ⟨0, Part.mem_bind ?_ ?_⟩
    · simpa only [Nat.unpair_pair] using hc
    · simp [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair]

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (q : Nat) : Program := graphProgram.column q

theorem graphColumn_primrec : Primrec graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram) Primrec.id

theorem graphColumn_domain (q c : Nat) : (graphColumn q).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c + 1 = unionInterpretation q := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval,
    graphEvaluation_domain, SuccessorLimit.predecessor_graph_iff]

theorem graphColumn_unique (q : Nat) (hq : SuccessorLimit.successorCheck q = true) :
    ∃! c, (graphColumn q).domain c := by
  obtain ⟨c, hc, _⟩ := SuccessorLimit.predecessor_returns q hq
  refine ⟨c, (graphColumn_domain q c).mpr ((SuccessorLimit.predecessor_graph_iff q c).mp hc), ?_⟩
  intro d hd
  exact SuccessorLimit.predecessor_unique q d c
    ((SuccessorLimit.predecessor_graph_iff q d).mpr ((graphColumn_domain q d).mp hd)) hc

end Alexander313.HereditarySuccessorLimitProgram
