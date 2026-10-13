import Alexander313.Wilken.HereditaryFiniteMultiplication

/-!
# Executing finite right-multiplication Programs

A total Program computes the literal guarded finite source recursion. Its
columns uniformly fix the original ordinal input and take the raw natural
coefficient. An actual positive Program recognizes exactly the original
input domain; no restriction is imposed on the Nat coefficient. A further
positive graph Program recognizes the unique genuine canonical product.
All admission, graph and execution facts are derived from the constructed PR
algorithm, without an effectivity or ordinal multiplication oracle. Uncompiled.
-/

namespace Alexander313.HereditaryFiniteMultiplicationProgram

open Wilken.RelativeTerm.Hereditary
open FiniteMultiplication

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (multiplyCode query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (multiplyCode query.unpair.1 query.unpair.2)) :=
    (multiplyCode_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (query : Nat) :
    decisionProgram.eval query = Part.some (multiplyCode query.unpair.1 query.unpair.2) :=
  Classical.choose_spec decisionProgram_exists query

theorem product_eval (q n : Nat) :
    decisionProgram.eval (Nat.pair q n) = Part.some (multiplyCode q n) := by
  simpa only [Nat.unpair_pair] using decisionProgram_eval (Nat.pair q n)

noncomputable def coefficientColumn (q : Nat) : Program := decisionProgram.column q

theorem coefficientColumn_primrec : Primrec coefficientColumn :=
  Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.id

theorem coefficientColumn_eval (q n : Nat) :
    (coefficientColumn q).eval n = Part.some (multiplyCode q n) := by
  rw [coefficientColumn, Program.column, Nat.Partrec.Code.eval_curry]
  exact product_eval q n

theorem coefficientColumn_total (q n : Nat) : (coefficientColumn q).domain n := by
  change ((coefficientColumn q).eval n).Dom
  rw [coefficientColumn_eval]
  trivial

theorem coefficientColumn_original (q n : Nat) (hq : unionCheck q = true) :
    Canonical.check (multiplyCode q n) = true ∧
      unionCheck (multiplyCode q n) = true ∧
        Theta.Normal (multiplyCode q n).unpair.1 (ThetaCourse.rawTree (multiplyCode q n).unpair.2) ∧
          unionInterpretation (multiplyCode q n) = unionInterpretation q * (n : Ordinal.{0}) :=
  ⟨multiplyCode_checked q n hq, multiplyCode_original q n hq,
    multiplyCode_normal q n hq, multiplyCode_value q n hq⟩

private def multiplicationDomainConstant (query : Nat) (_ : Nat) : Bool :=
  unionCheck query.unpair.1

private theorem multiplicationDomainConstant_primrec : Primrec₂ multiplicationDomainConstant :=
  (Uniform.unionCheck_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).to₂

def domainEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (multiplicationDomainConstant query witness))

theorem domainEvaluation_partrec : Partrec domainEvaluation :=
  Partrec.rfind multiplicationDomainConstant_primrec.to_comp.partrec.to₂

theorem domainEvaluation_domain (query : Nat) : (domainEvaluation query).Dom ↔
    unionCheck query.unpair.1 = true := by
  simp only [domainEvaluation, multiplicationDomainConstant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem domainProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ unionCheck query.unpair.1 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp domainEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using domainEvaluation_domain query

noncomputable def domainProgram : Program := Classical.choose domainProgram_exists

theorem domainProgram_domain (q n : Nat) : domainProgram.domain (Nat.pair q n) ↔
    unionCheck q = true := by
  simpa only [domainProgram, Nat.unpair_pair] using Classical.choose_spec domainProgram_exists (Nat.pair q n)

noncomputable def domainColumn (q : Nat) : Program := domainProgram.column q

theorem domainColumn_primrec : Primrec domainColumn :=
  Program.column_primrec.comp (Primrec.const domainProgram) Primrec.id

theorem domainColumn_domain (q n : Nat) : (domainColumn q).domain n ↔ unionCheck q = true := by
  rw [domainColumn, Program.column_domain]
  exact domainProgram_domain q n

def productGraph (q n c : Nat) : Bool :=
  unionCheck q && (Canonical.check c && (c == multiplyCode q n))

theorem productGraph_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => productGraph p.1.1 p.1.2 p.2) := by
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.and.comp (Uniform.unionCheck_primrec.comp hq)
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
      (Primrec.beq.comp Primrec.snd (multiplyCode_primrec.comp hq hn)))

theorem productGraph_exact (q n c : Nat) : productGraph q n c = true ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * (n : Ordinal.{0}) := by
  simp only [productGraph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hq, hc, he⟩
    refine ⟨hq, hc, ?_⟩
    rw [he]
    exact multiplyCode_value q n hq
  · rintro ⟨hq, hc, he⟩
    exact ⟨hq, hc, multiplyCode_unique q n hq c hc he⟩

private def multiplicationGraphRaw (query : Nat) : Bool :=
  productGraph query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

private theorem multiplicationGraphRaw_primrec : Primrec multiplicationGraphRaw := by
  have result := productGraph_primrec.comp ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))
  exact result.of_eq (fun _ => rfl)

private def multiplicationGraphConstant (query : Nat) (_ : Nat) : Bool := multiplicationGraphRaw query

private theorem multiplicationGraphConstant_primrec : Primrec₂ multiplicationGraphConstant :=
  (multiplicationGraphRaw_primrec.comp Primrec.fst).to₂

def graphEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (multiplicationGraphConstant query witness))

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.rfind multiplicationGraphConstant_primrec.to_comp.partrec.to₂

theorem graphEvaluation_domain (query : Nat) : (graphEvaluation query).Dom ↔
    multiplicationGraphRaw query = true := by
  simp only [graphEvaluation, multiplicationGraphConstant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem graphProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ multiplicationGraphRaw query = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using graphEvaluation_domain query

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (q n c : Nat) : graphProgram.domain (Nat.pair (Nat.pair q n) c) ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * (n : Ordinal.{0}) := by
  have h := Classical.choose_spec graphProgram_exists (Nat.pair (Nat.pair q n) c)
  simpa only [graphProgram, multiplicationGraphRaw, Nat.unpair_pair, productGraph_exact] using h

noncomputable def graphColumn (q n : Nat) : Program := graphProgram.column (Nat.pair q n)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (q n c : Nat) : (graphColumn q n).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * (n : Ordinal.{0}) := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q n c

theorem graphColumn_unique (q n : Nat) (hq : unionCheck q = true) :
    ∃! c : Nat, (graphColumn q n).domain c := by
  refine ⟨multiplyCode q n, (graphColumn_domain _ _ _).mpr
    ⟨hq, multiplyCode_checked q n hq, multiplyCode_value q n hq⟩, ?_⟩
  intro c hc
  have hs := (graphColumn_domain q n c).mp hc
  exact multiplyCode_unique q n hq c hs.2.1 hs.2.2

end Alexander313.HereditaryFiniteMultiplicationProgram
