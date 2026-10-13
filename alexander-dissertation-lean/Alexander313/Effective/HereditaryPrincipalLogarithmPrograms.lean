import Alexander313.Wilken.HereditaryPrincipalLogarithm

/-!
# Genuine partial logarithm and positive canonical graph Programs

The actual rfind logarithm compiles to a partial Program. Its halting domain is
exactly the originally admitted positive additive principals, and each returned
code is the genuine unique canonical omega exponent. Separate positive graph
columns are specialized by a proved PR compiler and retain every original
input/canonical-output guard and the literal omega-power equation. No logarithm
Program, termination or semantic graph oracle is supplied. Uncompiled.
-/

namespace Alexander313.HereditaryPrincipalLogarithmProgram

open Wilken.RelativeTerm.Hereditary

theorem logarithmProgram_exists : ∃ p : Program, ∀ q,
    p.eval q = PrincipalLogarithm.logarithm q :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp PrincipalLogarithm.logarithm_partrec)

noncomputable def logarithmProgram : Program := Classical.choose logarithmProgram_exists

theorem logarithmProgram_eval (q : Nat) : logarithmProgram.eval q = PrincipalLogarithm.logarithm q :=
  Classical.choose_spec logarithmProgram_exists q

theorem logarithmProgram_domain (q : Nat) : logarithmProgram.domain q ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) := by
  simp only [Program.domain, logarithmProgram_eval, PrincipalLogarithm.logarithm_domain,
    Principal.unionPrincipalCheck_exact]

theorem logarithmProgram_original (q c : Nat) (hc : c ∈ logarithmProgram.eval q) :
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  rw [logarithmProgram_eval] at hc
  exact PrincipalLogarithm.logarithm_value q c hc

theorem logarithmProgram_output_original (q c : Nat) (hc : c ∈ logarithmProgram.eval q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  rw [logarithmProgram_eval] at hc
  exact PrincipalLogarithm.logarithm_original q c hc

theorem logarithmProgram_terminates (q : Nat) (hq : unionCheck q = true)
    (hp : 0 < unionInterpretation q)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation q)) : logarithmProgram.domain q :=
  (logarithmProgram_domain q).mpr ⟨hq, hp, hprincipal⟩

theorem logarithmProgram_returns (q : Nat) (hq : unionCheck q = true)
    (hp : 0 < unionInterpretation q)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation q)) :
    ∃ c : Nat, c ∈ logarithmProgram.eval q ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  rw [logarithmProgram_eval]
  exact PrincipalLogarithm.logarithm_returns q
    ((Principal.unionPrincipalCheck_exact q).mpr ⟨hq, hp, hprincipal⟩)

theorem logarithmProgram_output_unique (q c d : Nat)
    (hc : c ∈ logarithmProgram.eval q) (hd : d ∈ logarithmProgram.eval q) : c = d := by
  rw [logarithmProgram_eval] at hc hd
  exact PrincipalLogarithm.logarithm_output_unique q c d hc hd

theorem logarithmProgram_output_invariant (q v c d : Nat)
    (hc : c ∈ logarithmProgram.eval q) (hd : d ∈ logarithmProgram.eval v)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  have hcs := logarithmProgram_original q c hc
  have hds := logarithmProgram_original v d hd
  apply Canonical.check_value_injective c d hcs.2.2.2.1 hds.2.2.2.1
  exact Wilken.omegaPower_strictMono.injective
    (hcs.2.2.2.2.trans (he.trans hds.2.2.2.2.symm))

private def graphConstant (query : Nat) (_ : Nat) : Bool :=
  PrincipalLogarithm.graph query.unpair.1 query.unpair.2

private theorem graphConstant_primrec : Primrec₂ graphConstant :=
  ((PrincipalLogarithm.graph_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).comp Primrec.fst).to₂

def graphEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (graphConstant query witness))

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.rfind graphConstant_primrec.to_comp.partrec.to₂

theorem graphEvaluation_domain (query : Nat) : (graphEvaluation query).Dom ↔
    PrincipalLogarithm.graph query.unpair.1 query.unpair.2 = true := by
  simp [graphEvaluation, graphConstant, Nat.rfind_dom, eq_comm]

theorem graphProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ PrincipalLogarithm.graph query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using graphEvaluation_domain query

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (query : Nat) : graphProgram.domain query ↔
    PrincipalLogarithm.graph query.unpair.1 query.unpair.2 = true :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (q : Nat) : Program := graphProgram.column q

theorem graphColumn_primrec : Primrec graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram) Primrec.id

theorem graphColumn_domain (q c : Nat) : (graphColumn q).domain c ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation q := by
  simp only [graphColumn, Program.column_domain, graphProgram_domain, Nat.unpair_pair,
    PrincipalLogarithm.graph_exact]

theorem graphColumn_unique (q : Nat) (hq : unionCheck q = true)
    (hp : 0 < unionInterpretation q)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation q)) :
    ∃! c : Nat, (graphColumn q).domain c := by
  obtain ⟨c, hc, hunique⟩ := PrincipalLogarithm.graph_unique q
    ((Principal.unionPrincipalCheck_exact q).mpr ⟨hq, hp, hprincipal⟩)
  refine ⟨c, (graphColumn_domain q c).mpr ((PrincipalLogarithm.graph_exact q c).mp hc), ?_⟩
  intro d hd
  exact hunique d ((PrincipalLogarithm.graph_exact q d).mpr ((graphColumn_domain q d).mp hd))

theorem graphColumn_returned (q c : Nat) (hc : c ∈ logarithmProgram.eval q) : (graphColumn q).domain c :=
  (graphColumn_domain q c).mpr (logarithmProgram_original q c hc)

end Alexander313.HereditaryPrincipalLogarithmProgram
