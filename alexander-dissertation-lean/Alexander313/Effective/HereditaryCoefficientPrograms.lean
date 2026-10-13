import Alexander313.Computability
import Alexander313.Wilken.HereditaryCoefficientNormalForm

/-!
# Actual Programs for hereditary additive coefficient forms

A total Program executes actual head compression, expansion and literal
source reconstruction. Primitive recursive column compilers fix the operation
and source level. Runs of literal trees and runs of literal head codes use
their actual Encodable encodings; the natural coefficients are raw Nat data.
General list decoder failure gives the empty list. Semantic output contracts
retain the unchanged original source admission or low admission assumptions.
An actual positive Program recognizes those exact source domains.

No equality, normal-form, arithmetic, effectivity or compiler oracle is supplied.
This is an additive coefficient form, not a full printed theta/epsilon or
multiplicative normal form. All proof terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryCoefficientProgram

open Wilken.RelativeTerm.Hereditary

def decodeRuns (c : Nat) : Coefficients.Runs Nat :=
  (Encodable.decode (α := Coefficients.Runs Nat) c).getD []

theorem decodeRuns_primrec : Primrec decodeRuns :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodeRuns_encode (rs : Coefficients.Runs Nat) :
    decodeRuns (Encodable.encode rs) = rs := by
  simp only [decodeRuns, Encodable.encodek, Option.getD_some]

def decodeAtoms (c : Nat) : List (Wilken.RelativeTerm Nat) :=
  (Encodable.decode (α := List (Wilken.RelativeTerm Nat)) c).getD []

theorem decodeAtoms_primrec : Primrec decodeAtoms :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodeAtoms_encode (as : List (Wilken.RelativeTerm Nat)) :
    decodeAtoms (Encodable.encode as) = as := by
  simp only [decodeAtoms, Encodable.encodek, Option.getD_some]

/-- Tags 0--3 are source forms, coded forms, coded expansion and reconstruction.
Tags 4--5 execute arbitrary coded expansion and actual literal-head compression. -/
def output (tag payload : Nat) : Nat :=
  let r := payload.unpair.1
  let c := payload.unpair.2
  cond (tag == 0) (Encodable.encode (Coefficients.coefficientForm r c))
    (cond (tag == 1) (Encodable.encode (Coefficients.coefficientCodes r c))
      (cond (tag == 2) (Encodable.encode (Coefficients.expandedCodes r c))
        (cond (tag == 3) (Coefficients.reconstructCode r c)
          (cond (tag == 4) (Encodable.encode (Coefficients.expand (decodeRuns payload)))
            (cond (tag == 5)
              (Encodable.encode (Coefficients.compress (Theta.equal r) (decodeAtoms c))) 0)))))

theorem output_primrec : Primrec₂ output := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  have hform := Primrec.encode.comp (Coefficients.coefficientForm_primrec.comp hr hc)
  have hcodes := Primrec.encode.comp (Coefficients.coefficientCodes_primrec.comp hr hc)
  have hexpanded := Primrec.encode.comp (Coefficients.expandedCodes_primrec.comp hr hc)
  have htree := Coefficients.reconstructCode_primrec.comp hr hc
  have hexpand : Primrec (fun p : Nat × Nat =>
      Encodable.encode (Coefficients.expand (decodeRuns p.2))) := Primrec.encode.comp
    (Coefficients.expand_primrec.comp (decodeRuns_primrec.comp Primrec.snd))
  have hcompress := Primrec.encode.comp
    ((Coefficients.compress_primrec (.parameter 0) Theta.equal Theta.Effective.equal_primrec).comp
      (hr.pair (decodeAtoms_primrec.comp hc)))
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond hform ((tag 1).cond hcodes ((tag 2).cond hexpanded
    ((tag 3).cond htree ((tag 4).cond hexpand ((tag 5).cond hcompress (Primrec.const 0))))))).to₂

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

theorem decisionColumn_primrec : Primrec decisionColumn :=
  Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.id

theorem decisionColumn_eval (tag payload : Nat) :
    (decisionColumn tag).eval payload = Part.some (output tag payload) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]
  simp only [Nat.unpair_pair]

theorem decisionColumn_total (tag payload : Nat) : (decisionColumn tag).domain payload := by
  change ((decisionColumn tag).eval payload).Dom
  rw [decisionColumn_eval]
  trivial

/-- The actual compiler fixes a source level and accepts its literal source code. -/
noncomputable def sourceColumn (tag r : Nat) : Program := (decisionColumn tag).column r

theorem sourceColumn_primrec : Primrec₂ sourceColumn :=
  (Program.column_primrec.comp (decisionColumn_primrec.comp Primrec.fst) Primrec.snd).to₂

theorem sourceColumn_eval (tag r c : Nat) :
    (sourceColumn tag r).eval c = Part.some (output tag (Nat.pair r c)) := by
  rw [sourceColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionColumn_eval]

theorem sourceColumn_total (tag r c : Nat) : (sourceColumn tag r).domain c := by
  change ((sourceColumn tag r).eval c).Dom
  rw [sourceColumn_eval]
  trivial

theorem coefficientForm_eval (r c : Nat) :
    (sourceColumn 0 r).eval c = Part.some (Encodable.encode (Coefficients.coefficientForm r c)) := by
  simpa [output, Nat.unpair_pair] using sourceColumn_eval 0 r c

theorem coefficientCodes_eval (r c : Nat) :
    (sourceColumn 1 r).eval c = Part.some (Encodable.encode (Coefficients.coefficientCodes r c)) := by
  simpa [output, Nat.unpair_pair] using sourceColumn_eval 1 r c

theorem expandedCodes_eval (r c : Nat) :
    (sourceColumn 2 r).eval c = Part.some (Encodable.encode (Coefficients.expandedCodes r c)) := by
  simpa [output, Nat.unpair_pair] using sourceColumn_eval 2 r c

theorem reconstruction_eval (r c : Nat) :
    (sourceColumn 3 r).eval c = Part.some (Coefficients.reconstructCode r c) := by
  simpa [output, Nat.unpair_pair] using sourceColumn_eval 3 r c

theorem expansion_eval (rs : Coefficients.Runs Nat) :
    (decisionColumn 4).eval (Encodable.encode rs) = Part.some (Encodable.encode (Coefficients.expand rs)) := by
  simpa [output] using decisionColumn_eval 4 (Encodable.encode rs)

theorem compression_eval (r : Nat) (as : List (Wilken.RelativeTerm Nat)) :
    (sourceColumn 5 r).eval (Encodable.encode as) =
      Part.some (Encodable.encode (Coefficients.compress (Theta.equal r) as)) := by
  simpa [output, Nat.unpair_pair] using sourceColumn_eval 5 r (Encodable.encode as)

theorem coefficientCodes_original (r c : Nat) (hc : checkCode r c = true) :
    (∀ p ∈ Coefficients.coefficientCodes r c, 0 < p.2 ∧ checkCode r p.1 = true ∧
      Theta.Normal r (ThetaCourse.rawTree p.1) ∧ 0 < interpretation r p.1 ∧
      Ordinal.IsPrincipal (· + ·) (interpretation r p.1)) ∧
    (Coefficients.coefficientCodes r c).Pairwise (fun p q => interpretation r q.1 < interpretation r p.1) ∧
    Coefficients.weightedSum (interpretation r) (Coefficients.coefficientCodes r c) = interpretation r c :=
  ⟨fun p hp => ⟨Coefficients.coefficientCodes_positive r c p hp,
      Coefficients.coefficientCodes_head_admitted r c hc p hp⟩,
    Coefficients.coefficientCodes_descending r c hc,
    Coefficients.coefficientCodes_weighted_value r c hc⟩

theorem reconstruction_original (r c : Nat) (hc : checkCode r c = true) :
    checkCode r (Coefficients.reconstructCode r c) = true ∧
      Theta.Normal r (ThetaCourse.rawTree (Coefficients.reconstructCode r c)) ∧
      interpretation r (Coefficients.reconstructCode r c) = interpretation r c :=
  Coefficients.reconstructCode_checked r c hc

theorem reconstruction_low (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode r (Coefficients.reconstructCode r c) = true := Coefficients.reconstructCode_low r c hc

def inputCheck (tag payload : Nat) : Bool :=
  cond (tag == 0) (checkCode payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (lowCheckCode payload.unpair.1 payload.unpair.2)
      (cond (tag == 2) (unionCheck payload) false))

theorem inputCheck_primrec : Primrec₂ inputCheck := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (Uniform.hereditaryCheckCode_primrec.comp hr hc)
    ((tag 1).cond (Uniform.hereditaryLowCheckCode_primrec.comp hr hc)
      ((tag 2).cond (Uniform.unionCheck_primrec.comp Primrec.snd) (Primrec.const false)))).to₂

private def inputConstant (query : Nat) (_ : Nat) : Bool := inputCheck query.unpair.1 query.unpair.2

private theorem inputConstant_primrec : Primrec₂ inputConstant :=
  (inputCheck_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def inputEvaluation (query : Nat) : Part Nat := Nat.rfind (fun witness => Part.some (inputConstant query witness))

theorem inputEvaluation_partrec : Partrec inputEvaluation :=
  Partrec.rfind inputConstant_primrec.to_comp.partrec.to₂

theorem inputEvaluation_domain (query : Nat) : (inputEvaluation query).Dom ↔
    inputCheck query.unpair.1 query.unpair.2 = true := by
  simp only [inputEvaluation, inputConstant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem inputProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ inputCheck query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp inputEvaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using inputEvaluation_domain query

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

noncomputable def inputColumn (tag : Nat) : Program := inputProgram.column tag

theorem inputColumn_primrec : Primrec inputColumn :=
  Program.column_primrec.comp (Primrec.const inputProgram) Primrec.id

theorem inputColumn_domain (tag payload : Nat) : (inputColumn tag).domain payload ↔ inputCheck tag payload = true := by
  rw [inputColumn, Program.column_domain, inputProgram, Classical.choose_spec inputProgram_exists]
  simp only [Nat.unpair_pair]

theorem original_input_domain (r c : Nat) :
    (inputColumn 0).domain (Nat.pair r c) ↔ checkCode r c = true := by
  simpa [inputCheck, Nat.unpair_pair] using inputColumn_domain 0 (Nat.pair r c)

theorem low_input_domain (r c : Nat) :
    (inputColumn 1).domain (Nat.pair r c) ↔ lowCheckCode r c = true := by
  simpa [inputCheck, Nat.unpair_pair] using inputColumn_domain 1 (Nat.pair r c)

theorem union_input_domain (q : Nat) : (inputColumn 2).domain q ↔ unionCheck q = true := by
  simpa [inputCheck] using inputColumn_domain 2 q

end Alexander313.HereditaryCoefficientProgram
