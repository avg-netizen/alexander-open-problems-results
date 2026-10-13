import Alexander313.Wilken.HereditaryPowers
import Alexander313.Effective.HereditaryFinitePowerPrograms

/-!
# Executing full ordinary coded-base exponentiation and its positive graph

Actual original-domain exponent decomposition, leading logarithms, finite
powers and genuine arithmetic produce the canonical alpha^beta Program.
Zero/one branches retain both original input guards. A positive graph executes
the actual power and checks literal canonical output equality. Exact source
equations and canonical injection derive its unique graph semantics, and PR
compiler maps specialize the fixed kernels. No PR execution claim is made.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryPowerProgram

open Wilken.RelativeTerm.Hereditary

theorem powerProgram_exists : ∃ p : Program, ∀ input, p.eval input = Powers.evaluation input :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp Powers.evaluation_partrec)

noncomputable def powerProgram : Program := Classical.choose powerProgram_exists

theorem powerProgram_eval (q v : Nat) : powerProgram.eval (Nat.pair q v) = Powers.power q v :=
  Classical.choose_spec powerProgram_exists _

theorem powerProgram_domain (q v : Nat) : powerProgram.domain (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true := by
  simp only [Program.domain, powerProgram_eval, Powers.power_domain]

theorem powerProgram_graph_iff (q v c : Nat) : c ∈ powerProgram.eval (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  rw [powerProgram_eval]
  exact Powers.power_graph_iff q v c

theorem powerProgram_returns (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃ c : Nat, c ∈ powerProgram.eval (Nat.pair q v) ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  obtain ⟨c, hc, hcc⟩ := Powers.power_returns q v hq hv
  exact ⟨c, by rw [powerProgram_eval]; exact hc, hcc, (Powers.power_value q v c hc).2.2.2⟩

theorem powerProgram_original (q v c : Nat) (hc : c ∈ powerProgram.eval (Nat.pair q v)) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := ((powerProgram_graph_iff q v c).mp hc).2.2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem powerProgram_invariant (q v q' v' c d : Nat)
    (hc : c ∈ powerProgram.eval (Nat.pair q v)) (hd : d ∈ powerProgram.eval (Nat.pair q' v'))
    (hq : unionInterpretation q = unionInterpretation q') (hv : unionInterpretation v = unionInterpretation v') : c = d := by
  rw [powerProgram_eval] at hc hd
  exact Powers.power_invariant q v q' v' c d hc hd hq hv

noncomputable def exponentColumn (q : Nat) : Program := powerProgram.column q

theorem exponentColumn_primrec : Primrec exponentColumn :=
  Program.column_primrec.comp (Primrec.const powerProgram) Primrec.id

theorem exponentColumn_domain (q v : Nat) : (exponentColumn q).domain v ↔
    unionCheck q = true ∧ unionCheck v = true := by
  rw [exponentColumn, Program.column_domain]
  exact powerProgram_domain q v

def graphEvaluation (query : Nat) : Part Nat :=
  (Powers.evaluation query.unpair.1).bind (HereditaryFinitePowerProgram.outputTest query)

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  (Powers.evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp).bind
    HereditaryFinitePowerProgram.outputTest_partrec

theorem graphEvaluation_domain (q v c : Nat) : (graphEvaluation (Nat.pair (Nat.pair q v) c)).Dom ↔
    c ∈ Powers.power q v := by
  constructor
  · intro hd
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨d, hd, ht⟩ := Part.mem_bind_iff.mp ha
    have hp : d ∈ Powers.power q v := by simpa only [Powers.power, Nat.unpair_pair] using hd
    cases he : d == c with
    | false =>
      have hf : False := by simpa [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair, he] using ht
      exact hf.elim
    | true => rw [← beq_iff_eq.mp he]; exact hp
  · intro hc
    apply Part.dom_iff_mem.mpr
    refine ⟨0, Part.mem_bind ?_ ?_⟩
    · simpa only [Powers.power, Nat.unpair_pair] using hc
    · simp [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair]

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (q v : Nat) : Program := graphProgram.column (Nat.pair q v)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (q v c : Nat) : (graphColumn q v).domain c ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q ^ unionInterpretation v := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval,
    graphEvaluation_domain, Powers.power_graph_iff]

theorem graphColumn_unique (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃! c : Nat, (graphColumn q v).domain c := by
  obtain ⟨c, hc, hcc⟩ := Powers.power_returns q v hq hv
  have he := (Powers.power_value q v c hc).2.2.2
  refine ⟨c, (graphColumn_domain q v c).mpr ⟨hq, hv, hcc, he⟩, ?_⟩
  intro d hd
  have hs := (graphColumn_domain q v d).mp hd
  exact Canonical.check_value_injective d c hs.2.2.1 hcc (hs.2.2.2.trans he.symm)

theorem graphColumn_returned (q v c : Nat) (hc : c ∈ powerProgram.eval (Nat.pair q v)) :
    (graphColumn q v).domain c := (graphColumn_domain q v c).mpr ((powerProgram_graph_iff q v c).mp hc)

end Alexander313.HereditaryPowerProgram
