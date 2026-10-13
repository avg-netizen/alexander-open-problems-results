import Alexander313.Wilken.HereditaryExponentDecomposition
import Alexander313.Effective.HereditaryFinitePowerPrograms

/-!
# Genuine omega-prefix/finite-tail decomposition Programs

Actual finite-certificate search returns the complete canonical quotient,
natural remainder and canonical omega-prefix triple. A positive graph executes
that computation and checks its literal output. Actual ordinal division and
canonical value injection supply exact graph meaning and unique output.
PR column compilers specialize actual fixed Program kernels. Uncompiled.
-/

namespace Alexander313.HereditaryExponentDecompositionProgram

open Wilken.RelativeTerm.Hereditary

theorem decompositionProgram_exists : ∃ p : Program, ∀ v,
    p.eval v = ExponentDecomposition.decompose v :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp ExponentDecomposition.decompose_partrec)

noncomputable def decompositionProgram : Program := Classical.choose decompositionProgram_exists

theorem decompositionProgram_eval (v : Nat) : decompositionProgram.eval v = ExponentDecomposition.decompose v :=
  Classical.choose_spec decompositionProgram_exists v

theorem decompositionProgram_domain (v : Nat) : decompositionProgram.domain v ↔ unionCheck v = true := by
  simp only [Program.domain, decompositionProgram_eval, ExponentDecomposition.decompose_domain]

theorem decompositionProgram_graph_iff (v data : Nat) :
    data ∈ decompositionProgram.eval v ↔ ExponentDecomposition.DataSpec v data := by
  rw [decompositionProgram_eval]
  exact ExponentDecomposition.decompose_graph_iff v data

theorem decompositionProgram_returns (v : Nat) (hv : unionCheck v = true) :
    ∃ data, data ∈ decompositionProgram.eval v ∧ ExponentDecomposition.DataSpec v data := by
  rw [decompositionProgram_eval]
  exact ExponentDecomposition.decompose_returns v hv

theorem decompositionProgram_unique (v : Nat) (hv : unionCheck v = true) :
    ∃! data, data ∈ decompositionProgram.eval v := by
  obtain ⟨data, hd, hs⟩ := decompositionProgram_returns v hv
  exact ⟨data, hd, fun t ht => ExponentDecomposition.data_unique v t data
    ((decompositionProgram_graph_iff v t).mp ht) hs⟩

def graphEvaluation (query : Nat) : Part Nat :=
  (ExponentDecomposition.decompose query.unpair.1).bind (HereditaryFinitePowerProgram.outputTest query)

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  (ExponentDecomposition.decompose_partrec.comp (Primrec.fst.comp Primrec.unpair).to_comp).bind
    HereditaryFinitePowerProgram.outputTest_partrec

theorem graphEvaluation_domain (v data : Nat) : (graphEvaluation (Nat.pair v data)).Dom ↔
    ExponentDecomposition.DataSpec v data := by
  have he : (graphEvaluation (Nat.pair v data)).Dom ↔ data ∈ ExponentDecomposition.decompose v := by
    constructor
    · intro hd
      obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hd
      obtain ⟨d, hd, ht⟩ := Part.mem_bind_iff.mp ha
      have hp : d ∈ ExponentDecomposition.decompose v := by simpa only [Nat.unpair_pair] using hd
      cases he : d == data with
      | false =>
        have hf : False := by simpa [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair, he] using ht
        exact hf.elim
      | true => rw [← beq_iff_eq.mp he]; exact hp
    · intro hd
      apply Part.dom_iff_mem.mpr
      refine ⟨0, Part.mem_bind ?_ ?_⟩
      · simpa only [Nat.unpair_pair] using hd
      · simp [HereditaryFinitePowerProgram.outputTest, Nat.unpair_pair]
  exact he.trans (ExponentDecomposition.decompose_graph_iff v data)

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (v : Nat) : Program := graphProgram.column v

theorem graphColumn_primrec : Primrec graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram) Primrec.id

theorem graphColumn_domain (v data : Nat) : (graphColumn v).domain data ↔ ExponentDecomposition.DataSpec v data := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval, graphEvaluation_domain]

theorem graphColumn_unique (v : Nat) (hv : unionCheck v = true) : ∃! data, (graphColumn v).domain data := by
  obtain ⟨data, _, hs⟩ := ExponentDecomposition.decompose_returns v hv
  exact ⟨data, (graphColumn_domain v data).mpr hs, fun t ht =>
    ExponentDecomposition.data_unique v t data ((graphColumn_domain v t).mp ht) hs⟩

end Alexander313.HereditaryExponentDecompositionProgram
