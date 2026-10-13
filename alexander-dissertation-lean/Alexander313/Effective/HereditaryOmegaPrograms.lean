import Alexander313.Wilken.HereditaryOmegaPowers

/-!
# Actual Programs for full hereditary ordinary omega powers

A total Program executes the constructed guarded primitive-recursive source
algorithm. An actual positive kernel recognizes the original input domain
and the genuine canonical output graph. Its graph columns are compiled
primitive recursively and have exactly one output on each originally admitted
input. The source values, admission and normality are unchanged. No power,
logarithm, semantic graph or effectivity oracle is supplied. Uncompiled.
-/

namespace Alexander313.HereditaryOmegaProgram

open Wilken.RelativeTerm.Hereditary
open OmegaPowers

theorem decisionProgram_exists : ∃ p : Program, ∀ q,
    p.eval q = Part.some (powerCode q) := by
  have h : Partrec (fun q => Part.some (powerCode q)) := powerCode_primrec.to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun q => congrFun hp q⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (q : Nat) : decisionProgram.eval q = Part.some (powerCode q) :=
  Classical.choose_spec decisionProgram_exists q

theorem decisionProgram_total (q : Nat) : decisionProgram.domain q := by
  change (decisionProgram.eval q).Dom
  rw [decisionProgram_eval]
  trivial

theorem power_original (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (powerCode q) = true ∧ unionCheck (powerCode q) = true ∧
      Theta.Normal (powerCode q).unpair.1 (ThetaCourse.rawTree (powerCode q).unpair.2) ∧
      unionInterpretation (powerCode q) = Ordinal.omega0 ^ unionInterpretation q :=
  ⟨powerCode_checked q hq, powerCode_original q hq, powerCode_normal q hq, powerCode_value q hq⟩

def powerGraph (q c : Nat) : Bool :=
  unionCheck q && (Canonical.check c && (c == powerCode q))

theorem powerGraph_primrec : Primrec₂ powerGraph :=
  (Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
      (Primrec.beq.comp Primrec.snd (powerCode_primrec.comp Primrec.fst)))).to₂

theorem powerGraph_exact (q c : Nat) : powerGraph q c = true ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = Ordinal.omega0 ^ unionInterpretation q := by
  simp only [powerGraph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hq, hc, he⟩
    exact ⟨hq, hc, by rw [he]; exact powerCode_value q hq⟩
  · rintro ⟨hq, hc, hv⟩
    exact ⟨hq, hc, powerCode_unique q c hq hc hv⟩

def positiveCheck (tag payload : Nat) : Bool :=
  cond (tag == 0) (unionCheck payload)
    (cond (tag == 1) (powerGraph payload.unpair.1 payload.unpair.2) false)

theorem positiveCheck_primrec : Primrec₂ positiveCheck := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have h0 : Primrec (fun p : Nat × Nat => p.1 == 0) := Primrec.beq.comp Primrec.fst (Primrec.const 0)
  have h1 : Primrec (fun p : Nat × Nat => p.1 == 1) := Primrec.beq.comp Primrec.fst (Primrec.const 1)
  exact (h0.cond (Uniform.unionCheck_primrec.comp Primrec.snd)
    (h1.cond (powerGraph_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
      (Primrec.const false))).to₂

private def powerPositiveConstant (query : Nat) (_ : Nat) : Bool :=
  positiveCheck query.unpair.1 query.unpair.2

private theorem powerPositiveConstant_primrec : Primrec₂ powerPositiveConstant :=
  (positiveCheck_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def positiveEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (powerPositiveConstant query witness))

theorem positiveEvaluation_partrec : Partrec positiveEvaluation :=
  Partrec.rfind powerPositiveConstant_primrec.to_comp.partrec.to₂

theorem positiveEvaluation_domain (query : Nat) : (positiveEvaluation query).Dom ↔
    positiveCheck query.unpair.1 query.unpair.2 = true := by
  simp only [positiveEvaluation, powerPositiveConstant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem positiveProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ positiveCheck query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp positiveEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using positiveEvaluation_domain query

noncomputable def positiveProgram : Program := Classical.choose positiveProgram_exists

noncomputable def positiveColumn (tag : Nat) : Program := positiveProgram.column tag

theorem positiveColumn_primrec : Primrec positiveColumn :=
  Program.column_primrec.comp (Primrec.const positiveProgram) Primrec.id

theorem positiveColumn_domain (tag payload : Nat) : (positiveColumn tag).domain payload ↔
    positiveCheck tag payload = true := by
  rw [positiveColumn, Program.column_domain, positiveProgram, Classical.choose_spec positiveProgram_exists]
  simp only [Nat.unpair_pair]

noncomputable def domainProgram : Program := positiveColumn 0

theorem domainProgram_domain (q : Nat) : domainProgram.domain q ↔ unionCheck q = true := by
  simpa only [domainProgram, positiveCheck, beq_self_eq_true, Bool.cond_true] using positiveColumn_domain 0 q

noncomputable def graphProgram : Program := positiveColumn 1

theorem graphProgram_domain (q c : Nat) : graphProgram.domain (Nat.pair q c) ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = Ordinal.omega0 ^ unionInterpretation q := by
  simpa [graphProgram, positiveCheck, Nat.unpair_pair, powerGraph_exact] using positiveColumn_domain 1 (Nat.pair q c)

noncomputable def graphColumn (q : Nat) : Program := graphProgram.column q

theorem graphColumn_primrec : Primrec graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram) Primrec.id

theorem graphColumn_domain (q c : Nat) : (graphColumn q).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = Ordinal.omega0 ^ unionInterpretation q := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q c

theorem graphColumn_unique (q : Nat) (hq : unionCheck q = true) : ∃! c : Nat, (graphColumn q).domain c := by
  refine ⟨powerCode q, (graphColumn_domain q _).mpr ⟨hq, powerCode_checked q hq, powerCode_value q hq⟩, ?_⟩
  intro c hc
  have hs := (graphColumn_domain q c).mp hc
  exact powerCode_unique q c hq hs.2.1 hs.2.2

end Alexander313.HereditaryOmegaProgram
