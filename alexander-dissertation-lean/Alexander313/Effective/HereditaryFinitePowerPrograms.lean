import Alexander313.Wilken.HereditaryFinitePowers

/-!
# Executing arbitrary-base finite powers and positive output graphs

Actual partial-recursive power recursion and finite-code exponent extraction
compile to genuine Programs. The positive output graph executes the constructed
power computation, then checks literal equality with its canonical result.
Its domain is exactly original base admission and the real finite power equation;
its compiler is PR. No total/PR power or semantic graph oracle is assumed.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryFinitePowerProgram

open Wilken.RelativeTerm.Hereditary

def evaluation (input : Nat) : Part Nat := FinitePowers.power input.unpair.1 input.unpair.2

theorem evaluation_partrec : Partrec evaluation :=
  FinitePowers.power_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

theorem powerProgram_exists : ∃ p : Program, ∀ input, p.eval input = evaluation input :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)

noncomputable def powerProgram : Program := Classical.choose powerProgram_exists

theorem powerProgram_eval (q n : Nat) : powerProgram.eval (Nat.pair q n) = FinitePowers.power q n := by
  simpa only [evaluation, Nat.unpair_pair] using Classical.choose_spec powerProgram_exists (Nat.pair q n)

theorem powerProgram_domain (q n : Nat) : powerProgram.domain (Nat.pair q n) ↔ unionCheck q = true := by
  simp only [Program.domain, powerProgram_eval, FinitePowers.power_domain]

theorem powerProgram_value (q n c : Nat) (hc : c ∈ powerProgram.eval (Nat.pair q n)) :
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  rw [powerProgram_eval] at hc
  exact FinitePowers.power_value q n c hc

theorem powerProgram_returns (q n : Nat) (hq : unionCheck q = true) :
    ∃ c : Nat, c ∈ powerProgram.eval (Nat.pair q n) ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  rw [powerProgram_eval]
  exact FinitePowers.power_returns q n hq

theorem powerProgram_graph_iff (q n c : Nat) : c ∈ powerProgram.eval (Nat.pair q n) ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  rw [powerProgram_eval]
  exact FinitePowers.power_graph_iff q n c

noncomputable def exponentColumn (q : Nat) : Program := powerProgram.column q

theorem exponentColumn_primrec : Primrec exponentColumn :=
  Program.column_primrec.comp (Primrec.const powerProgram) Primrec.id

theorem exponentColumn_domain (q n : Nat) : (exponentColumn q).domain n ↔ unionCheck q = true := by
  rw [exponentColumn, Program.column_domain]
  exact powerProgram_domain q n

def codedEvaluation (input : Nat) : Part Nat := FinitePowers.codedPower input.unpair.1 input.unpair.2

theorem codedEvaluation_partrec : Partrec codedEvaluation :=
  FinitePowers.codedPower_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

theorem codedProgram_exists : ∃ p : Program, ∀ input, p.eval input = codedEvaluation input :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp codedEvaluation_partrec)

noncomputable def codedProgram : Program := Classical.choose codedProgram_exists

theorem codedProgram_eval (q v : Nat) : codedProgram.eval (Nat.pair q v) = FinitePowers.codedPower q v := by
  simpa only [codedEvaluation, Nat.unpair_pair] using Classical.choose_spec codedProgram_exists (Nat.pair q v)

theorem codedProgram_domain (q v : Nat) : codedProgram.domain (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 := by
  simp only [Program.domain, codedProgram_eval, FinitePowers.codedPower_domain]

theorem codedProgram_graph_iff (q v c : Nat) : c ∈ codedProgram.eval (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 ∧
      Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  rw [codedProgram_eval]
  exact FinitePowers.codedPower_graph_iff q v c

def outputTest (query c : Nat) : Part Nat :=
  cond (c == query.unpair.2) (Part.some 0) Part.none

theorem outputTest_partrec : Partrec₂ outputTest :=
  (Partrec.cond
    (Primrec.beq.comp Primrec.snd (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to_comp
    (Computable.const 0).partrec Partrec.none).to₂

def graphEvaluation (query : Nat) : Part Nat :=
  (evaluation query.unpair.1).bind (outputTest query)

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  (evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp).bind outputTest_partrec

theorem graphEvaluation_domain (q n c : Nat) :
    (graphEvaluation (Nat.pair (Nat.pair q n) c)).Dom ↔ c ∈ FinitePowers.power q n := by
  constructor
  · intro hd
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨d, hd, ht⟩ := Part.mem_bind_iff.mp ha
    have hp : d ∈ FinitePowers.power q n := by simpa only [evaluation, Nat.unpair_pair] using hd
    cases he : d == c with
    | false =>
      have hf : False := by simp only [outputTest, Nat.unpair_pair, he, Bool.cond_false] at ht; simpa using ht
      exact hf.elim
    | true =>
      have hdc := beq_iff_eq.mp he
      rw [← hdc]
      exact hp
  · intro hc
    apply Part.dom_iff_mem.mpr
    refine ⟨0, Part.mem_bind ?_ ?_⟩
    · simpa only [evaluation, Nat.unpair_pair] using hc
    · simp only [outputTest, Nat.unpair_pair, beq_self_eq_true, Bool.cond_true, Part.mem_some_iff]

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (q n : Nat) : Program := graphProgram.column (Nat.pair q n)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (q n c : Nat) : (graphColumn q n).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ (n : Ordinal.{0}) := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval,
    graphEvaluation_domain, FinitePowers.power_graph_iff]

theorem graphColumn_unique (q n : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, (graphColumn q n).domain c := by
  obtain ⟨c, _, hc, he⟩ := FinitePowers.power_returns q n hq
  refine ⟨c, (graphColumn_domain q n c).mpr ⟨hq, hc, he⟩, ?_⟩
  intro d hd
  have hs := (graphColumn_domain q n d).mp hd
  exact Canonical.check_value_injective d c hs.2.1 hc (hs.2.2.trans he.symm)

end Alexander313.HereditaryFinitePowerProgram
