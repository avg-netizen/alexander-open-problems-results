import Alexander313.Wilken.HereditaryNaturalCodes

/-!
# Actual Programs for finite ordinal values and extraction

Total columns execute genuine finite-value checking and natural extraction.
Separate positive columns recognize exactly admitted finite values and the
graph of their unique numerical value. An actual column also multiplies original
ordinal codes when the second value is finite, with its exact input recognizer.
No supplied finite ordinal decision or
extraction Program is used. Raw fallback values have no semantic claim outside
the displayed original guards. Uncompiled candidates.
-/

namespace Alexander313.HereditaryNaturalProgram

open Wilken.RelativeTerm.Hereditary

def output (tag payload : Nat) : Nat :=
  cond (tag == 0) (NaturalCodes.count payload)
    (cond (tag == 1) (NaturalCodes.extract payload)
      (cond (tag == 2) (cond (NaturalCodes.check payload) 1 0)
        (cond (tag == 3)
          (cond (NaturalCodes.graph payload.unpair.1 payload.unpair.2) 1 0)
          (cond (tag == 4) (NaturalCodes.multiplyFinite payload.unpair.1 payload.unpair.2) 0))))

theorem output_primrec : Primrec₂ output := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (NaturalCodes.count_primrec.comp Primrec.snd)
    ((tag 1).cond (NaturalCodes.extract_primrec.comp Primrec.snd)
      ((tag 2).cond ((NaturalCodes.check_primrec.comp Primrec.snd).cond
          (Primrec.const 1) (Primrec.const 0))
        ((tag 3).cond ((NaturalCodes.graph_primrec.comp
          (Primrec.fst.comp hp) (Primrec.snd.comp hp)).cond
            (Primrec.const 1) (Primrec.const 0))
          ((tag 4).cond (NaturalCodes.multiplyFinite_primrec.comp
            (Primrec.fst.comp hp) (Primrec.snd.comp hp)) (Primrec.const 0)))))).to₂

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

theorem extraction_eval (q : Nat) :
    (decisionColumn 1).eval q = Part.some (NaturalCodes.extract q) := by
  simpa [output] using decisionColumn_eval 1 q

theorem extraction_original (q : Nat) (hq : NaturalCodes.check q = true) :
    unionCheck q = true ∧ unionInterpretation q = (NaturalCodes.extract q : Ordinal.{0}) :=
  ⟨((NaturalCodes.check_value q).mp hq).1, NaturalCodes.extract_value q hq⟩

theorem natural_decision (q : Nat) : 1 ∈ (decisionColumn 2).eval q ↔
    unionCheck q = true ∧ unionInterpretation q < Ordinal.omega0 := by
  rw [decisionColumn_eval]
  have h := NaturalCodes.check_below_omega q
  cases hc : NaturalCodes.check q <;> simp [output, hc] at h ⊢ <;> exact h

def check (tag payload : Nat) : Bool :=
  cond (tag == 0) (NaturalCodes.check payload)
    (cond (tag == 1) (NaturalCodes.graph payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (NaturalCodes.finiteInputs payload.unpair.1 payload.unpair.2) false))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (NaturalCodes.check_primrec.comp Primrec.snd)
    ((tag 1).cond (NaturalCodes.graph_primrec.comp
      (Primrec.fst.comp hp) (Primrec.snd.comp hp))
      ((tag 2).cond (NaturalCodes.finiteInputs_primrec.comp
        (Primrec.fst.comp hp) (Primrec.snd.comp hp)) (Primrec.const false)))).to₂

private def constant (query : Nat) (_ : Nat) : Bool :=
  check query.unpair.1 query.unpair.2

private theorem constant_primrec : Primrec₂ constant :=
  ((check_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).comp Primrec.fst).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (constant query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind constant_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔
    check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, constant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem recognizer_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ check query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

noncomputable def recognizerColumn (tag : Nat) : Program := recognizer.column tag

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  rw [recognizerColumn, Program.column_domain]
  simpa only [recognizer, Nat.unpair_pair] using Classical.choose_spec recognizer_exists (Nat.pair tag payload)

theorem natural_domain (q : Nat) : (recognizerColumn 0).domain q ↔
    unionCheck q = true ∧ unionInterpretation q < Ordinal.omega0 := by
  simpa [check, NaturalCodes.check_below_omega] using recognizerColumn_domain 0 q

theorem extraction_graph_domain (q n : Nat) :
    (recognizerColumn 1).domain (Nat.pair q n) ↔
      unionCheck q = true ∧ unionInterpretation q = (n : Ordinal.{0}) := by
  simpa [check, Nat.unpair_pair, NaturalCodes.graph_exact] using
    recognizerColumn_domain 1 (Nat.pair q n)

theorem extraction_graph_unique (q : Nat) (hq : NaturalCodes.check q = true) :
    ∃! n : Nat, (recognizerColumn 1).domain (Nat.pair q n) := by
  have hs := (NaturalCodes.check_value q).mp hq
  refine ⟨NaturalCodes.count q, (extraction_graph_domain _ _).mpr hs, ?_⟩
  intro n hn
  have ht := (extraction_graph_domain q n).mp hn
  exact (NaturalCodes.count_of_nat q n ht.1 ht.2).symm

theorem finite_multiplication_eval (q v : Nat) :
    (decisionColumn 4).eval (Nat.pair q v) = Part.some (NaturalCodes.multiplyFinite q v) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 4 (Nat.pair q v)

theorem finite_multiplication_domain (q v : Nat) :
    (recognizerColumn 2).domain (Nat.pair q v) ↔
      unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 := by
  simpa [check, Nat.unpair_pair, NaturalCodes.finiteInputs_exact] using
    recognizerColumn_domain 2 (Nat.pair q v)

theorem finite_multiplication_original (q v : Nat)
    (hq : unionCheck q = true) (hv : NaturalCodes.check v = true) :
    Canonical.check (NaturalCodes.multiplyFinite q v) = true ∧
      unionInterpretation (NaturalCodes.multiplyFinite q v) = unionInterpretation q * unionInterpretation v :=
  ⟨NaturalCodes.multiplyFinite_checked q v hq hv, NaturalCodes.multiplyFinite_value q v hq hv⟩

end Alexander313.HereditaryNaturalProgram
