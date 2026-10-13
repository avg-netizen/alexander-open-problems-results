import Alexander313.Wilken.HereditaryCanonicalArithmetic

/-!
# Executing canonical addition, subtraction, successor and numeral Programs

Total columns compute the genuine constructed raw-code operations. An actual
positive Program recognizes the graph of canonical addition; its exact domain
contains both original admission checks and the unique canonical sum code.
Successor is the column using the literal admitted ordinal-one code. A total
column computes canonical subtraction for all originally admitted pairs. No
effectivity, output chooser or arithmetic graph oracle is supplied. Uncompiled.
-/

namespace Alexander313.HereditaryCanonicalArithmeticProgram

open Wilken.RelativeTerm.Hereditary
open CanonicalArithmetic

def output (tag payload : Nat) : Nat :=
  cond (tag == 0) (canonicalSum payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (successorCode payload)
      (cond (tag == 2) (numeralCode payload)
        (cond (tag == 3) (canonicalSubtraction payload.unpair.1 payload.unpair.2) 0)))

theorem output_primrec : Primrec₂ output := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (canonicalSum_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
    ((tag 1).cond (successorCode_primrec.comp Primrec.snd)
      ((tag 2).cond (numeralCode_primrec.comp Primrec.snd)
        ((tag 3).cond (canonicalSubtraction_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp))
          (Primrec.const 0))))).to₂

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (output query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (output query.unpair.1 query.unpair.2)) :=
    (output_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (query : Nat) :
    decisionProgram.eval query = Part.some (output query.unpair.1 query.unpair.2) :=
  Classical.choose_spec decisionProgram_exists query

noncomputable def decisionColumn (tag : Nat) : Program := decisionProgram.column tag

theorem decisionColumn_eval (tag payload : Nat) :
    (decisionColumn tag).eval payload = Part.some (output tag payload) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]
  simp only [Nat.unpair_pair]

theorem decisionColumn_total (tag payload : Nat) : (decisionColumn tag).domain payload := by
  change ((decisionColumn tag).eval payload).Dom
  rw [decisionColumn_eval]
  trivial

theorem sum_eval (q v : Nat) :
    (decisionColumn 0).eval (Nat.pair q v) = Part.some (canonicalSum q v) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 0 (Nat.pair q v)

theorem sum_original (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    Canonical.check (canonicalSum q v) = true ∧
      unionInterpretation (canonicalSum q v) = unionInterpretation q + unionInterpretation v :=
  ⟨canonicalSum_checked q v hq hv, canonicalSum_value q v hq hv⟩

theorem successor_eval (q : Nat) : (decisionColumn 1).eval q = Part.some (successorCode q) := by
  simpa [output] using decisionColumn_eval 1 q

theorem successor_original (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (successorCode q) = true ∧
      unionInterpretation (successorCode q) = unionInterpretation q + 1 :=
  ⟨successorCode_checked q hq, successorCode_value q hq⟩

theorem numeral_eval (n : Nat) : (decisionColumn 2).eval n = Part.some (numeralCode n) := by
  simpa [output] using decisionColumn_eval 2 n

theorem numeral_original (n : Nat) :
    Canonical.check (numeralCode n) = true ∧ unionInterpretation (numeralCode n) = (n : Ordinal.{0}) :=
  ⟨numeralCode_checked n, numeralCode_value n⟩

theorem subtraction_eval (q v : Nat) :
    (decisionColumn 3).eval (Nat.pair q v) = Part.some (canonicalSubtraction q v) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 3 (Nat.pair q v)

theorem subtraction_original (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    Canonical.check (canonicalSubtraction q v) = true ∧
      unionInterpretation (canonicalSubtraction q v) = unionInterpretation v - unionInterpretation q :=
  ⟨canonicalSubtraction_checked q v hq hv, canonicalSubtraction_value q v hq hv⟩

def sumGraph (q v c : Nat) : Bool :=
  (unionCheck q && unionCheck v) && (Canonical.check c && (c == canonicalSum q v))

theorem sumGraph_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => sumGraph p.1.1 p.1.2 p.2) := by
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hv : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.and.comp
    (Primrec.and.comp (Uniform.unionCheck_primrec.comp hq) (Uniform.unionCheck_primrec.comp hv))
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
      (Primrec.beq.comp Primrec.snd (canonicalSum_primrec.comp hq hv)))

theorem sumGraph_exact (q v c : Nat) : sumGraph q v c = true ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q + unionInterpretation v := by
  simp only [sumGraph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨hq, hv⟩, hc, he⟩
    refine ⟨hq, hv, hc, ?_⟩
    rw [he]
    exact canonicalSum_value q v hq hv
  · rintro ⟨hq, hv, hc, he⟩
    exact ⟨⟨hq, hv⟩, hc, canonicalSum_unique q v hq hv c hc he⟩

private def arithmeticGraphRaw (query : Nat) : Bool :=
  sumGraph query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

private theorem arithmeticGraphRaw_primrec : Primrec arithmeticGraphRaw := by
  have hp := Primrec.unpair
  have hleft := Primrec.unpair.comp (Primrec.fst.comp hp)
  have result := sumGraph_primrec.comp (hleft.pair (Primrec.snd.comp hp))
  exact result.of_eq (fun _ => rfl)

private def arithmeticGraphConstant (query : Nat) (_ : Nat) : Bool := arithmeticGraphRaw query

private theorem arithmeticGraphConstant_primrec : Primrec₂ arithmeticGraphConstant := by
  have result := arithmeticGraphRaw_primrec.comp
    (show Primrec (fun p : Nat × Nat => p.1) from Primrec.fst)
  exact result.to₂.of_eq (fun _ _ => rfl)

def graphEvaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (arithmeticGraphConstant query witness))

theorem graphEvaluation_partrec : Partrec graphEvaluation :=
  Partrec.rfind arithmeticGraphConstant_primrec.to_comp.partrec.to₂

theorem graphEvaluation_domain (query : Nat) : (graphEvaluation query).Dom ↔
    arithmeticGraphRaw query = true := by
  simp only [graphEvaluation, arithmeticGraphConstant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem graphProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ arithmeticGraphRaw query = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp graphEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using graphEvaluation_domain query

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (q v c : Nat) :
    graphProgram.domain (Nat.pair (Nat.pair q v) c) ↔
      unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
        unionInterpretation c = unionInterpretation q + unionInterpretation v := by
  have h := Classical.choose_spec graphProgram_exists (Nat.pair (Nat.pair q v) c)
  simpa only [graphProgram, arithmeticGraphRaw, Nat.unpair_pair, sumGraph_exact] using h

noncomputable def graphColumn (q v : Nat) : Program := graphProgram.column (Nat.pair q v)

theorem graphColumn_domain (q v c : Nat) : (graphColumn q v).domain c ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q + unionInterpretation v := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain q v c

theorem graphColumn_unique (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃! c : Nat, (graphColumn q v).domain c := by
  refine ⟨canonicalSum q v, (graphColumn_domain _ _ _).mpr
    ⟨hq, hv, canonicalSum_checked q v hq hv, canonicalSum_value q v hq hv⟩, ?_⟩
  intro c hc
  have hs := (graphColumn_domain q v c).mp hc
  exact canonicalSum_unique q v hq hv c hs.2.2.1 hs.2.2.2

theorem successor_graph_domain (q c : Nat) : (graphColumn q oneCode).domain c ↔
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c = unionInterpretation q + 1 := by
  simp only [graphColumn_domain, oneCode_checked, oneCode_value, true_and]

end Alexander313.HereditaryCanonicalArithmeticProgram
