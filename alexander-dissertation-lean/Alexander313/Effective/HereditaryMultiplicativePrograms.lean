import Alexander313.Wilken.HereditaryMultiplicativeClassification

/-!
# Total decision and exact positive Programs for multiplicative principals

The actual guarded logarithm decision is computable because its termination was
proved; no primitive-recursive classifier claim is made. Its chosen Program
returns 1 for the source class and 0 otherwise. Separate positive Programs
recognize original class admission, canonical class admission and the guarded
Boolean output graph. Program columns are compiled primitive recursively even
though execution of the class decision uses an unbounded search. Uncompiled.
-/

namespace Alexander313.HereditaryMultiplicativeProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.MultiplicativePrincipalArithmetic

def decisionOutput (q : Nat) : Nat := cond (Multiplicative.check q) 1 0

theorem decisionOutput_computable : Computable decisionOutput :=
  Multiplicative.check_computable.cond (Computable.const 1) (Computable.const 0)

theorem decisionOutput_one (q : Nat) : decisionOutput q = 1 ↔
    unionCheck q = true ∧ IsMultiplicativePrincipal (unionInterpretation q) := by
  rw [← Multiplicative.check_exact]
  cases hq : Multiplicative.check q <;> simp [decisionOutput, hq]

theorem decisionOutput_zero (q : Nat) : decisionOutput q = 0 ↔
    ¬ (unionCheck q = true ∧ IsMultiplicativePrincipal (unionInterpretation q)) := by
  rw [← Multiplicative.check_exact]
  cases hq : Multiplicative.check q <;> simp [decisionOutput, hq]

theorem decisionOutput_range (q : Nat) : decisionOutput q = 0 ∨ decisionOutput q = 1 := by
  cases hq : Multiplicative.check q <;> simp [decisionOutput, hq]

theorem decisionProgram_exists : ∃ p : Program, ∀ q,
    p.eval q = Part.some (decisionOutput q) :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp decisionOutput_computable.partrec)

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (q : Nat) : decisionProgram.eval q = Part.some (decisionOutput q) :=
  Classical.choose_spec decisionProgram_exists q

theorem decisionProgram_total (q : Nat) : decisionProgram.domain q := by
  change (decisionProgram.eval q).Dom
  rw [decisionProgram_eval]
  trivial

theorem decisionProgram_one (q : Nat) : 1 ∈ decisionProgram.eval q ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) ∧
      Ordinal.IsPrincipal (· * ·) (unionInterpretation q) := by
  simpa only [decisionProgram_eval, Part.mem_some_iff, eq_comm] using decisionOutput_one q

theorem decisionProgram_class (q : Nat) : 1 ∈ decisionProgram.eval q ↔
    unionCheck q = true ∧ (unionInterpretation q = 1 ∨
      ∃ ρ : Ordinal.{0}, unionInterpretation q = Ordinal.omega0 ^ (Ordinal.omega0 ^ ρ)) := by
  simp only [decisionProgram_eval, Part.mem_some_iff, eq_comm, decisionOutput_one,
    multiplicativePrincipal_iff]

theorem decisionProgram_zero (q : Nat) : 0 ∈ decisionProgram.eval q ↔
    ¬ (unionCheck q = true ∧ IsMultiplicativePrincipal (unionInterpretation q)) := by
  simp only [decisionProgram_eval, Part.mem_some_iff, eq_comm, decisionOutput_zero]

def graph (q b : Nat) : Bool := unionCheck q && (b == decisionOutput q)

theorem graph_computable : Computable₂ graph :=
  (Primrec.and.to_comp.comp (Uniform.unionCheck_primrec.to_comp.comp Computable.fst)
    (Primrec.beq.to_comp.comp Computable.snd
      (decisionOutput_computable.comp Computable.fst))).to₂

theorem graph_exact (q b : Nat) : graph q b = true ↔
    unionCheck q = true ∧ ((b = 1 ∧ IsMultiplicativePrincipal (unionInterpretation q)) ∨
      (b = 0 ∧ ¬ IsMultiplicativePrincipal (unionInterpretation q))) := by
  cases hq : unionCheck q with
  | false => simp [graph, hq]
  | true =>
    have hs : Multiplicative.check q = true ↔ IsMultiplicativePrincipal (unionInterpretation q) := by
      simpa only [Multiplicative.check_exact, hq, true_and]
    cases hc : Multiplicative.check q with
    | false =>
      have hp : ¬ IsMultiplicativePrincipal (unionInterpretation q) := by
        intro hp
        have ht := hs.mpr hp
        rw [hc] at ht
        cases ht
      simp [graph, decisionOutput, hq, hc, hp]
    | true =>
      have hp := hs.mp hc
      simp [graph, decisionOutput, hq, hc, hp]

def positiveCheck (tag payload : Nat) : Bool :=
  cond (tag == 0) (Multiplicative.check payload)
    (cond (tag == 1) (Multiplicative.canonicalCheck payload)
      (cond (tag == 2) (graph payload.unpair.1 payload.unpair.2) false))

theorem positiveCheck_computable : Computable₂ positiveCheck := by
  have hp := Primrec.unpair.to_comp.comp Computable.snd
  have h0 := Primrec.beq.to_comp.comp Computable.fst (Computable.const 0)
  have h1 := Primrec.beq.to_comp.comp Computable.fst (Computable.const 1)
  have h2 := Primrec.beq.to_comp.comp Computable.fst (Computable.const 2)
  exact (h0.cond (Multiplicative.check_computable.comp Computable.snd)
    (h1.cond (Multiplicative.canonicalCheck_computable.comp Computable.snd)
      (h2.cond (graph_computable.comp (Computable.fst.comp hp) (Computable.snd.comp hp))
        (Computable.const false)))).to₂

private def positiveConstant (query : Nat) (_ : Nat) : Bool :=
  positiveCheck query.unpair.1 query.unpair.2

private theorem positiveConstant_computable : Computable₂ positiveConstant :=
  ((positiveCheck_computable.comp (Computable.fst.comp Primrec.unpair.to_comp)
    (Computable.snd.comp Primrec.unpair.to_comp)).comp Computable.fst).to₂

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

theorem positiveColumn_domain (tag payload : Nat) : (positiveColumn tag).domain payload ↔
    positiveCheck tag payload = true := by
  rw [positiveColumn, Program.column_domain, Classical.choose_spec positiveProgram_exists]
  simp only [Nat.unpair_pair]

noncomputable def classProgram : Program := positiveColumn 0

theorem classProgram_domain (q : Nat) : classProgram.domain q ↔
    unionCheck q = true ∧ IsMultiplicativePrincipal (unionInterpretation q) := by
  simpa only [classProgram, positiveCheck, beq_self_eq_true, Bool.cond_true,
    Multiplicative.check_exact] using positiveColumn_domain 0 q

noncomputable def canonicalClassProgram : Program := positiveColumn 1

theorem canonicalClassProgram_domain (q : Nat) : canonicalClassProgram.domain q ↔
    Canonical.check q = true ∧ IsMultiplicativePrincipal (unionInterpretation q) := by
  simpa [canonicalClassProgram, positiveCheck, Multiplicative.canonicalCheck_exact]
    using positiveColumn_domain 1 q

noncomputable def graphProgram : Program := positiveColumn 2

theorem graphProgram_domain (q b : Nat) : graphProgram.domain (Nat.pair q b) ↔
    unionCheck q = true ∧ ((b = 1 ∧ IsMultiplicativePrincipal (unionInterpretation q)) ∨
      (b = 0 ∧ ¬ IsMultiplicativePrincipal (unionInterpretation q))) := by
  simpa [graphProgram, positiveCheck, Nat.unpair_pair, graph_exact]
    using positiveColumn_domain 2 (Nat.pair q b)

noncomputable def graphColumn (q : Nat) : Program := graphProgram.column q

theorem graphColumn_primrec : Primrec graphColumn :=
  Program.column_primrec.comp (Primrec.const graphProgram) Primrec.id

theorem graphColumn_domain (q b : Nat) : (graphColumn q).domain b ↔
    unionCheck q = true ∧ ((b = 1 ∧ IsMultiplicativePrincipal (unionInterpretation q)) ∨
      (b = 0 ∧ ¬ IsMultiplicativePrincipal (unionInterpretation q))) := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q b

theorem graphColumn_unique (q : Nat) (hq : unionCheck q = true) :
    ∃! b : Nat, (graphColumn q).domain b := by
  have hg : graph q (decisionOutput q) = true := by simp [graph, hq]
  refine ⟨decisionOutput q, (graphColumn_domain q _).mpr ((graph_exact q _).mp hg), ?_⟩
  intro b hb
  have h := (graph_exact q b).mpr ((graphColumn_domain q b).mp hb)
  exact beq_iff_eq.mp (Bool.and_eq_true.mp h).2

end Alexander313.HereditaryMultiplicativeProgram
