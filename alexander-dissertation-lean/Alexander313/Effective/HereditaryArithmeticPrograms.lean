import Alexander313.Wilken.HereditaryAddition
import Alexander313.Wilken.HereditaryPrincipalClassification

/-! # Actual addition and additive-principal Programs

A total machine computes full old-domain union addition, its input admission
test, positive additive-principal decisions and coded principal decompositions.
A genuine positive search machine recognizes exactly original admitted union
codes denoting positive additive principals. All ordinal equations use the
original interpretation; no arithmetic, normalization or halting oracle is
supplied. Epsilon/multiplicative classification and remaining source arithmetic
are not claimed. Uncompiled.
-/

namespace Alexander313.HereditaryArithmeticProgram

open Wilken.RelativeTerm.Hereditary

def additionInputs (payload : Nat) : Bool :=
  unionCheck payload.unpair.1 && unionCheck payload.unpair.2

theorem additionInputs_primrec : Primrec additionInputs :=
  Primrec.and.comp (Uniform.unionCheck_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Uniform.unionCheck_primrec.comp (Primrec.snd.comp Primrec.unpair))

def output (tag payload : Nat) : Nat :=
  cond (tag == 0) (Addition.unionAdd payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (cond (Principal.unionPrincipalCheck payload) 1 0)
      (cond (tag == 2) (Encodable.encode (Principal.atomCodes payload.unpair.1 payload.unpair.2))
        (cond (tag == 3) (cond (additionInputs payload) 1 0) 0)))

theorem output_primrec : Primrec₂ output := by
  have hpay : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hp := Primrec.unpair.comp hpay
  have hl := Primrec.fst.comp hp
  have hr := Primrec.snd.comp hp
  have hadd := Addition.unionAdd_primrec.comp hl hr
  have hprincipal := (Principal.unionPrincipalCheck_primrec.comp hpay).cond
    (Primrec.const 1) (Primrec.const 0)
  have hatoms := Primrec.encode.comp (Principal.atomCodes_primrec.comp hl hr)
  have hguard := (additionInputs_primrec.comp hpay).cond (Primrec.const 1) (Primrec.const 0)
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond hadd ((tag 1).cond hprincipal
    ((tag 2).cond hatoms ((tag 3).cond hguard (Primrec.const 0))))).to₂

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

theorem addition_eval (q v : Nat) : (decisionColumn 0).eval (Nat.pair q v) =
    Part.some (Addition.unionAdd q v) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 0 (Nat.pair q v)

theorem addition_original (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionCheck (Addition.unionAdd q v) = true ∧
      unionInterpretation (Addition.unionAdd q v) = unionInterpretation q + unionInterpretation v := by
  have h := Addition.unionAdd_checked q v hq hv
  exact ⟨h.1, h.2.2⟩

theorem addition_inputs_decision (q v : Nat) :
    1 ∈ (decisionColumn 3).eval (Nat.pair q v) ↔
      unionCheck q = true ∧ unionCheck v = true := by
  rw [decisionColumn_eval]
  cases hq : unionCheck q <;> cases hv : unionCheck v <;>
    simp [output, additionInputs, Nat.unpair_pair, hq, hv]

theorem principal_decision (q : Nat) : 1 ∈ (decisionColumn 1).eval q ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) := by
  rw [decisionColumn_eval]
  have h := Principal.unionPrincipalCheck_exact q
  cases hc : Principal.unionPrincipalCheck q <;> simp [output, hc] at h ⊢ <;> exact h

theorem decomposition_eval (r c : Nat) : (decisionColumn 2).eval (Nat.pair r c) =
    Part.some (Encodable.encode (Principal.atomCodes r c)) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 2 (Nat.pair r c)

theorem decomposition_original (r c : Nat) (hc : checkCode r c = true) :
    (Principal.atomCodes r c).map (interpretation r) =
      Wilken.canonicalANF (interpretation r c) := Principal.atomCodes_anf r c hc

private def principalConstant (q : Nat) (_ : Nat) : Bool := Principal.unionPrincipalCheck q

private theorem principalConstant_primrec : Primrec₂ principalConstant :=
  (Principal.unionPrincipalCheck_primrec.comp Primrec.fst).to₂

def principalEvaluation (q : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (principalConstant q witness))

theorem principalEvaluation_partrec : Partrec principalEvaluation :=
  Partrec.rfind principalConstant_primrec.to_comp.partrec.to₂

theorem principalEvaluation_domain (q : Nat) : (principalEvaluation q).Dom ↔
    Principal.unionPrincipalCheck q = true := by
  simp only [principalEvaluation, principalConstant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem principalRecognizer_exists : ∃ p : Program, ∀ q,
    p.domain q ↔ Principal.unionPrincipalCheck q = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp principalEvaluation_partrec)
  refine ⟨p, fun q => ?_⟩
  simpa only [Program.domain, hp] using principalEvaluation_domain q

noncomputable def principalRecognizer : Program := Classical.choose principalRecognizer_exists

theorem principalRecognizer_domain (q : Nat) : principalRecognizer.domain q ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) := by
  rw [principalRecognizer, Classical.choose_spec principalRecognizer_exists q]
  exact Principal.unionPrincipalCheck_exact q

end Alexander313.HereditaryArithmeticProgram
