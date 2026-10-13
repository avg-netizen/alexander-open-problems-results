import Alexander313.Wilken.HereditaryScaledQuotient
import Alexander313.Effective.HereditaryFinitePowerPrograms

/-!
# Actual scaled-quotient execution and literal graph Programs

These Programs execute the constructed positive-left quotient followed by
the genuine multiplier. All three original inputs, quotient existence and
positive divisor remain in the exact halting domain. Positive graphs execute
the routine and compare its actual canonical output. PR columns specialize
fixed kernels; arithmetic execution is not claimed PR. Real cap bounds do
not supply the missing source tracking reach theorem. All terms uncompiled.
-/

namespace Alexander313.HereditaryScaledQuotientProgram

open Wilken.RelativeTerm.Hereditary

theorem scaledProgram_exists : ∃ p : Program, ∀ input,
    p.eval input = ScaledQuotient.evaluation input :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp ScaledQuotient.evaluation_partrec)

noncomputable def scaledProgram : Program := Classical.choose scaledProgram_exists

theorem scaledProgram_eval (a b z : Nat) :
    scaledProgram.eval (Nat.pair (Nat.pair a b) z) = ScaledQuotient.scale a b z :=
  Classical.choose_spec scaledProgram_exists _

theorem scaledProgram_domain (a b z : Nat) :
    scaledProgram.domain (Nat.pair (Nat.pair a b) z) ↔ ScaledQuotient.SourceDomain a b z := by
  simp only [Program.domain, scaledProgram_eval, ScaledQuotient.scale_domain]

theorem scaledProgram_graph_iff (a b z c : Nat) :
    c ∈ scaledProgram.eval (Nat.pair (Nat.pair a b) z) ↔ ScaledQuotient.OutputSpec a b z c := by
  rw [scaledProgram_eval]
  exact ScaledQuotient.scale_graph_iff a b z c

theorem scaledProgram_returns (a b z : Nat) (h : ScaledQuotient.SourceDomain a b z) :
    ∃ c, c ∈ scaledProgram.eval (Nat.pair (Nat.pair a b) z) ∧ ScaledQuotient.OutputSpec a b z c := by
  rw [scaledProgram_eval]
  exact ScaledQuotient.scale_returns a b z h

theorem scaledProgram_below_cap (a b z c : Nat)
    (hc : c ∈ scaledProgram.eval (Nat.pair (Nat.pair a b) z)) (cap : Ordinal.{0})
    (hm : Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal cap)
    (hb : unionInterpretation b < cap)
    (hz : unionInterpretation z < unionInterpretation a * cap) : unionInterpretation c < cap := by
  rw [scaledProgram_eval] at hc
  exact ScaledQuotient.scale_below_cap a b z c hc cap hm hb hz

noncomputable def productColumn (a b : Nat) : Program := scaledProgram.column (Nat.pair a b)

theorem productColumn_primrec : Primrec₂ productColumn :=
  (Program.column_primrec.comp (Primrec.const scaledProgram) Primrec₂.natPair).to₂

theorem productColumn_domain (a b z : Nat) : (productColumn a b).domain z ↔
    ScaledQuotient.SourceDomain a b z := by
  rw [productColumn, Program.column_domain]
  exact scaledProgram_domain a b z

def graphEvaluation (query : Nat) : Part Nat :=
  (ScaledQuotient.evaluation query.unpair.1).bind (HereditaryFinitePowerProgram.outputTest query)

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  (ScaledQuotient.evaluation_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp).bind
    HereditaryFinitePowerProgram.outputTest_partrec

theorem graphEvaluation_domain (a b z c : Nat) :
    (graphEvaluation (Nat.pair (Nat.pair (Nat.pair a b) z) c)).Dom ↔ c ∈ ScaledQuotient.scale a b z := by
  constructor
  · intro hd
    obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨d, hd, ht⟩ := Part.mem_bind_iff.mp hr
    have hs : d ∈ ScaledQuotient.scale a b z := by
      simpa only [ScaledQuotient.scale, Nat.unpair_pair] using hd
    cases he : d == c with
    | false =>
      have hf : False := by simpa [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair, he] using ht
      exact hf.elim
    | true => rw [← beq_iff_eq.mp he]; exact hs
  · intro hc
    apply Part.dom_iff_mem.mpr
    refine ⟨0, Part.mem_bind ?_ ?_⟩
    · simpa only [ScaledQuotient.scale, Nat.unpair_pair] using hc
    · simp [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair]

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (a b z : Nat) : Program :=
  graphProgram.column (Nat.pair (Nat.pair a b) z)

theorem graphColumn_primrec : Primrec (fun p : (Nat × Nat) × Nat => graphColumn p.1.1 p.1.2 p.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem graphColumn_domain (a b z c : Nat) : (graphColumn a b z).domain c ↔
    ScaledQuotient.OutputSpec a b z c := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval,
    graphEvaluation_domain, ScaledQuotient.scale_graph_iff]

theorem graphColumn_unique (a b z : Nat) (h : ScaledQuotient.SourceDomain a b z) :
    ∃! c, (graphColumn a b z).domain c := by
  obtain ⟨c, hc, hs⟩ := ScaledQuotient.scale_returns a b z h
  exact ⟨c, (graphColumn_domain a b z c).mpr hs,
    fun d hd => ScaledQuotient.spec_unique a b z d c ((graphColumn_domain a b z d).mp hd) hs⟩

theorem graphColumn_returned (a b z c : Nat)
    (hc : c ∈ scaledProgram.eval (Nat.pair (Nat.pair a b) z)) : (graphColumn a b z).domain c :=
  (graphColumn_domain a b z c).mpr ((scaledProgram_graph_iff a b z c).mp hc)

end Alexander313.HereditaryScaledQuotientProgram
