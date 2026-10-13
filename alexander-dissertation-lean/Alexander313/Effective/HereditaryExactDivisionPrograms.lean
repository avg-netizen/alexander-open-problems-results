import Alexander313.Wilken.HereditaryExactDivision

/-!
# Actual exact-division execution and positive equation graph Programs

The constructed partial quotient routine compiles to an actual Program.
A separate graph Program searches genuine finite multiplication certificates
for a fixed canonical quotient. Its halting domain is the literal positive
left-division equation with all original and canonical admission guards.
Specialization is genuinely PR; neither the quotient nor its positive graph
recognition is claimed to be a total or primitive recursive decision routine.
No quotient, graph, arithmetic or compilation oracle is supplied. Uncompiled.
-/

namespace Alexander313.HereditaryExactDivisionProgram

open Wilken.RelativeTerm.Hereditary

theorem divisionProgram_exists : ∃ p : Program, ∀ input,
    p.eval input = ExactDivision.evaluation input :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp ExactDivision.evaluation_partrec)

noncomputable def divisionProgram : Program := Classical.choose divisionProgram_exists

theorem divisionProgram_eval (q v : Nat) :
    divisionProgram.eval (Nat.pair q v) = ExactDivision.divide q v :=
  Classical.choose_spec divisionProgram_exists _

theorem divisionProgram_domain (q v : Nat) :
    divisionProgram.domain (Nat.pair q v) ↔ ExactDivision.SourceDomain q v := by
  simp only [Program.domain, divisionProgram_eval, ExactDivision.divide_domain]

theorem divisionProgram_value (q v c : Nat)
    (hc : c ∈ divisionProgram.eval (Nat.pair q v)) :
    unionCheck q = true ∧ unionCheck v = true ∧ 0 < unionInterpretation q ∧
      Canonical.check c = true ∧ unionInterpretation q * unionInterpretation c = unionInterpretation v := by
  rw [divisionProgram_eval] at hc
  exact ExactDivision.divide_value q v c hc

theorem divisionProgram_original (q v c : Nat)
    (hc : c ∈ divisionProgram.eval (Nat.pair q v)) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  rw [divisionProgram_eval] at hc
  exact ExactDivision.divide_original q v c hc

theorem divisionProgram_bound (q v c : Nat)
    (hc : c ∈ divisionProgram.eval (Nat.pair q v)) :
    unionInterpretation c ≤ unionInterpretation v := by
  rw [divisionProgram_eval] at hc
  exact ExactDivision.divide_bound q v c hc

theorem divisionProgram_returns (q v : Nat) (h : ExactDivision.SourceDomain q v) :
    ∃ c : Nat, c ∈ divisionProgram.eval (Nat.pair q v) ∧ Canonical.check c = true ∧
      unionInterpretation q * unionInterpretation c = unionInterpretation v := by
  rw [divisionProgram_eval]
  exact ExactDivision.divide_returns q v h

theorem divisionProgram_output_unique (q v c d : Nat)
    (hc : c ∈ divisionProgram.eval (Nat.pair q v))
    (hd : d ∈ divisionProgram.eval (Nat.pair q v)) : c = d := by
  rw [divisionProgram_eval] at hc hd
  exact ExactDivision.divide_output_unique q v c d hc hd

theorem divisionProgram_eq_every_solution (q v c : Nat)
    (hc : c ∈ divisionProgram.eval (Nat.pair q v))
    (δ : Ordinal.{0}) (hδ : unionInterpretation q * δ = unionInterpretation v) :
    unionInterpretation c = δ := by
  rw [divisionProgram_eval] at hc
  exact ExactDivision.divide_eq_every_solution q v c hc δ hδ

/-- Query.first encodes (left factor, product); query.second is the quotient. -/
def graphCertificate (query witness : Nat) : Bool :=
  ExactDivision.certificateCheck query.unpair.1 (Nat.pair query.unpair.2 witness)

theorem graphCertificate_primrec : Primrec₂ graphCertificate :=
  (ExactDivision.certificateCheck_primrec.comp
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
      Primrec.snd)).to₂

def graphEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (graphCertificate query witness))

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.rfind graphCertificate_primrec.to_comp.partrec.to₂

theorem graphEvaluation_domain (q v c : Nat) :
    (graphEvaluation (Nat.pair (Nat.pair q v) c)).Dom ↔
      unionCheck q = true ∧ unionCheck v = true ∧ 0 < unionInterpretation q ∧
        Canonical.check c = true ∧ unionInterpretation q * unionInterpretation c = unionInterpretation v := by
  have he : (graphEvaluation (Nat.pair (Nat.pair q v) c)).Dom ↔
      ∃ w, ExactDivision.certificateCheck (Nat.pair q v) (Nat.pair c w) = true := by
    simp [graphEvaluation, graphCertificate, Nat.unpair_pair, Nat.rfind_dom, eq_comm]
  rw [he]
  constructor
  · rintro ⟨w, hw⟩
    simpa only [Nat.unpair_pair] using ExactDivision.certificateCheck_spec _ _ hw
  · rintro ⟨hq, hv, hp, hc, hproduct⟩
    exact ExactDivision.certificate_witness q v c hq hv hp hc hproduct

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.eval query = graphEvaluation query :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_eval (query : Nat) : graphProgram.eval query = graphEvaluation query :=
  Classical.choose_spec graphProgram_exists query

noncomputable def graphColumn (q v : Nat) : Program := graphProgram.column (Nat.pair q v)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (q v c : Nat) : (graphColumn q v).domain c ↔
    unionCheck q = true ∧ unionCheck v = true ∧ 0 < unionInterpretation q ∧
      Canonical.check c = true ∧ unionInterpretation q * unionInterpretation c = unionInterpretation v := by
  simp only [graphColumn, Program.column_domain, Program.domain, graphProgram_eval,
    graphEvaluation_domain]

theorem graphColumn_unique (q v : Nat) (h : ExactDivision.SourceDomain q v) :
    ∃! c : Nat, (graphColumn q v).domain c := by
  obtain ⟨c, hc, hcanonical, hproduct⟩ := ExactDivision.divide_returns q v h
  refine ⟨c, (graphColumn_domain q v c).mpr
    ⟨h.1, h.2.1, h.2.2.1, hcanonical, hproduct⟩, ?_⟩
  intro d hd
  have hs := (graphColumn_domain q v d).mp hd
  apply Canonical.check_value_injective d c hs.2.2.2.1 hcanonical
  exact Wilken.MultiplicativePrincipalArithmetic.positive_mul_injective h.2.2.1
    (hs.2.2.2.2.trans hproduct.symm)

theorem graphColumn_returned (q v c : Nat)
    (hc : c ∈ divisionProgram.eval (Nat.pair q v)) : (graphColumn q v).domain c :=
  (graphColumn_domain q v c).mpr (divisionProgram_value q v c hc)

end Alexander313.HereditaryExactDivisionProgram
