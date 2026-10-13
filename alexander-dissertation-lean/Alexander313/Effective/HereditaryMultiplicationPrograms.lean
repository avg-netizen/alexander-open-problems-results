import Alexander313.Wilken.HereditaryMultiplication

/-!
# Executing general hereditary multiplication and its positive graph

The partial Program executes the actual finite principal-log certificate
search and arithmetic fold. Its domain is exactly pairs of originally
admitted union inputs; the returned output is the unique canonical actual
ordinal product. A separate positive Program checks the same real numerical
certificate and literal result. PR column compilers specialize these actual
fixed kernels. No total multiplication function, graph, termination or
effectivity oracle is supplied. All proof terms remain uncompiled.
-/

namespace Alexander313.HereditaryMultiplicationProgram

open Wilken.RelativeTerm.Hereditary

theorem multiplyProgram_exists : ∃ p : Program, ∀ input,
    p.eval input = Multiplication.evaluation input :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp Multiplication.evaluation_partrec)

noncomputable def multiplyProgram : Program := Classical.choose multiplyProgram_exists

theorem multiplyProgram_eval (input : Nat) :
    multiplyProgram.eval input = Multiplication.evaluation input :=
  Classical.choose_spec multiplyProgram_exists input

theorem product_eval (q v : Nat) :
    multiplyProgram.eval (Nat.pair q v) = Multiplication.multiply q v :=
  multiplyProgram_eval (Nat.pair q v)

theorem multiplyProgram_domain (q v : Nat) : multiplyProgram.domain (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true := by
  simp only [Program.domain, product_eval, Multiplication.multiply_domain]

theorem multiplyProgram_value (q v c : Nat) (hc : c ∈ multiplyProgram.eval (Nat.pair q v)) :
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  rw [product_eval] at hc
  exact Multiplication.multiply_value q v c hc

theorem multiplyProgram_original (q v c : Nat) (hc : c ∈ multiplyProgram.eval (Nat.pair q v)) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  rw [product_eval] at hc
  exact Multiplication.multiply_original q v c hc

theorem multiplyProgram_returns (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃ c, c ∈ multiplyProgram.eval (Nat.pair q v) ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  rw [product_eval]
  exact Multiplication.multiply_returns q v hq hv

theorem multiplyProgram_graph_iff (q v c : Nat) : c ∈ multiplyProgram.eval (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  rw [product_eval]
  exact Multiplication.multiply_graph_iff q v c

theorem multiplyProgram_terminates (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    multiplyProgram.domain (Nat.pair q v) := (multiplyProgram_domain q v).mpr ⟨hq, hv⟩

theorem multiplyProgram_unique (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃! c, c ∈ multiplyProgram.eval (Nat.pair q v) := by
  rw [product_eval]
  exact Multiplication.multiply_unique q v hq hv

theorem multiplyProgram_invariant (q v q' v' c d : Nat)
    (hc : c ∈ multiplyProgram.eval (Nat.pair q v)) (hd : d ∈ multiplyProgram.eval (Nat.pair q' v'))
    (hq : unionInterpretation q = unionInterpretation q') (hv : unionInterpretation v = unionInterpretation v') : c = d := by
  rw [product_eval] at hc hd
  exact Multiplication.multiply_invariant q v q' v' c d hc hd hq hv

noncomputable def rightColumn (q : Nat) : Program := multiplyProgram.column q

theorem rightColumn_primrec : Primrec rightColumn :=
  Program.column_primrec.comp (Primrec.const multiplyProgram) Primrec.id

theorem rightColumn_eval (q v : Nat) : (rightColumn q).eval v = Multiplication.multiply q v := by
  rw [rightColumn, Nat.Partrec.Code.eval_curry]
  exact product_eval q v

theorem rightColumn_domain (q v : Nat) : (rightColumn q).domain v ↔
    unionCheck q = true ∧ unionCheck v = true := by
  simp only [Program.domain, rightColumn_eval, Multiplication.multiply_domain]

def graphEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (Multiplication.graphCertificateCheck query witness))

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.rfind Multiplication.graphCertificateCheck_primrec.to_comp.partrec.to₂

theorem graphEvaluation_domain (q v c : Nat) :
    (graphEvaluation (Nat.pair (Nat.pair q v) c)).Dom ↔
      unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
        unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  simpa [graphEvaluation, Nat.rfind_dom, eq_comm] using
    Multiplication.graphCertificateCheck_exists_iff q v c

theorem graphProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

theorem graphProgram_domain (q v c : Nat) : graphProgram.domain (Nat.pair (Nat.pair q v) c) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  simpa only [Program.domain, graphProgram_eval] using graphEvaluation_domain q v c

noncomputable def graphColumn (q v : Nat) : Program := graphProgram.column (Nat.pair q v)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (q v c : Nat) : (graphColumn q v).domain c ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q v c

theorem graphColumn_returned (q v c : Nat) (hc : c ∈ multiplyProgram.eval (Nat.pair q v)) :
    (graphColumn q v).domain c :=
  (graphColumn_domain q v c).mpr (multiplyProgram_value q v c hc)

theorem graphColumn_execution (q v c : Nat) : (graphColumn q v).domain c ↔
    c ∈ multiplyProgram.eval (Nat.pair q v) :=
  (graphColumn_domain q v c).trans (multiplyProgram_graph_iff q v c).symm

theorem graphColumn_unique (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃! c, (graphColumn q v).domain c := by
  obtain ⟨c, hc, hu⟩ := multiplyProgram_unique q v hq hv
  exact ⟨c, (graphColumn_execution q v c).mpr hc,
    fun d hd => hu d ((graphColumn_execution q v d).mp hd)⟩

end Alexander313.HereditaryMultiplicationProgram
