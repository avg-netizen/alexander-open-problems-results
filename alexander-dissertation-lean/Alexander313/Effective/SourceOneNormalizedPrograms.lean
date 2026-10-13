import Alexander313.Wilken.SourceOneNormalizationPrimitive

/-! # Executing normalization and comparison of all admitted base-one codes

The total joint machine returns the actual normalized literal code, or a
zero/one comparison answer. The positive checked columns admit the original
source grammar before comparing normalized trees. Their actual ordinal order
and equality domains therefore require no input normality hypothesis.
Normalization is not claimed to give a unique canonical representative, and
these machines do not compare hereditary later-base codes. Uncompiled.
-/

namespace Alexander313.SourceOneNormalizedProgram

open Wilken.RelativeTerm.SourceOne
open Wilken.RelativeTerm.SourceOne.Normalization

def check (tag payload : Nat) : Bool :=
  let c := payload.unpair.1
  let d := payload.unpair.2
  let admitted := PublicCodes.checkCode c && PublicCodes.checkCode d
  cond (tag == 1) (lessRawCode c d)
    (cond (tag == 2) (equalRawCode c d)
      (cond (tag == 3) (acceptedLowCode payload)
        (cond (tag == 4) (admitted && lessRawCode c d)
          (cond (tag == 5) (admitted && equalRawCode c d) false))))

theorem check_primrec : Primrec₂ check := by
  have hc : Primrec (fun p : Nat × Nat => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × Nat => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hl := Effective.lessRawCode_primrec.comp hc hd
  have he := Effective.equalRawCode_primrec.comp hc hd
  have ha := Primrec.and.comp (PublicCodes.checkCode_primrec.comp hc)
    (PublicCodes.checkCode_primrec.comp hd)
  have tag (k : Nat) : Primrec (fun p : Nat × Nat => p.1 == k) :=
    Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact ((tag 1).cond hl ((tag 2).cond he
    ((tag 3).cond (Effective.acceptedLowCode_primrec.comp Primrec.snd)
      ((tag 4).cond (Primrec.and.comp ha hl)
        ((tag 5).cond (Primrec.and.comp ha he) (Primrec.const false)))))).to₂

def output (tag payload : Nat) : Nat :=
  cond (tag == 0) (normalizeCode payload) (cond (check tag payload) 1 0)

theorem output_primrec : Primrec₂ output :=
  ((Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond
    (Effective.normalizeCode_primrec.comp Primrec.snd)
    (check_primrec.cond (Primrec.const 1) (Primrec.const 0))).to₂

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

theorem normalize_eval (c : Nat) :
    (decisionColumn 0).eval c = Part.some (normalizeCode c) := by
  simpa [output] using decisionColumn_eval 0 c

theorem normalize_preserves (c : Nat) (hc : PublicCodes.checkCode c = true) :
    ∃ d : Nat, d ∈ (decisionColumn 0).eval c ∧ Comparison.acceptedCode d = true ∧
      PublicCodes.interpretation d = PublicCodes.interpretation c := by
  refine ⟨normalizeCode c, ?_, normalizeCode_checked c hc⟩
  rw [normalize_eval]
  simp

theorem less_decision (c d : Nat) :
    1 ∈ (decisionColumn 1).eval (Nat.pair c d) ↔ lessRawCode c d = true := by
  rw [decisionColumn_eval]
  cases h : lessRawCode c d <;> simp [output, check, Nat.unpair_pair, h]

theorem equal_decision (c d : Nat) :
    1 ∈ (decisionColumn 2).eval (Nat.pair c d) ↔ equalRawCode c d = true := by
  rw [decisionColumn_eval]
  cases h : equalRawCode c d <;> simp [output, check, Nat.unpair_pair, h]

theorem less_decision_correct (c d : Nat)
    (hc : PublicCodes.checkCode c = true) (hd : PublicCodes.checkCode d = true) :
    1 ∈ (decisionColumn 1).eval (Nat.pair c d) ↔
      PublicCodes.interpretation c < PublicCodes.interpretation d :=
  (less_decision c d).trans (lessRawCode_correct c d hc hd)

theorem equal_decision_correct (c d : Nat)
    (hc : PublicCodes.checkCode c = true) (hd : PublicCodes.checkCode d = true) :
    1 ∈ (decisionColumn 2).eval (Nat.pair c d) ↔
      PublicCodes.interpretation c = PublicCodes.interpretation d :=
  (equal_decision c d).trans (equalRawCode_correct c d hc hd)

private def constantCheck (query : Nat) (_ : Nat) : Bool :=
  check query.unpair.1 query.unpair.2

private theorem constantCheck_primrec : Primrec₂ constantCheck :=
  (check_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (constantCheck query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind constantCheck_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) :
    (evaluation query).Dom ↔ check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, constantCheck, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem recognizer_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ check query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

theorem recognizer_domain (query : Nat) :
    recognizer.domain query ↔ check query.unpair.1 query.unpair.2 = true :=
  Classical.choose_spec recognizer_exists query

noncomputable def recognizerColumn (tag : Nat) : Program := recognizer.column tag

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  simp only [recognizerColumn, Program.column_domain, recognizer_domain, Nat.unpair_pair]

theorem order_domain (c d : Nat) : (recognizerColumn 4).domain (Nat.pair c d) ↔
    PublicCodes.checkCode c = true ∧ PublicCodes.checkCode d = true ∧
      PublicCodes.interpretation c < PublicCodes.interpretation d := by
  have hraw : (recognizerColumn 4).domain (Nat.pair c d) ↔
      (PublicCodes.checkCode c = true ∧ PublicCodes.checkCode d = true) ∧ lessRawCode c d = true := by
    simpa [check, Nat.unpair_pair] using recognizerColumn_domain 4 (Nat.pair c d)
  rw [hraw]
  constructor
  · rintro ⟨⟨hc, hd⟩, hless⟩
    exact ⟨hc, hd, (lessRawCode_correct c d hc hd).mp hless⟩
  · rintro ⟨hc, hd, hless⟩
    exact ⟨⟨hc, hd⟩, (lessRawCode_correct c d hc hd).mpr hless⟩

theorem equality_domain (c d : Nat) : (recognizerColumn 5).domain (Nat.pair c d) ↔
    PublicCodes.checkCode c = true ∧ PublicCodes.checkCode d = true ∧
      PublicCodes.interpretation c = PublicCodes.interpretation d := by
  have hraw : (recognizerColumn 5).domain (Nat.pair c d) ↔
      (PublicCodes.checkCode c = true ∧ PublicCodes.checkCode d = true) ∧ equalRawCode c d = true := by
    simpa [check, Nat.unpair_pair] using recognizerColumn_domain 5 (Nat.pair c d)
  rw [hraw]
  constructor
  · rintro ⟨⟨hc, hd⟩, hequal⟩
    exact ⟨hc, hd, (equalRawCode_correct c d hc hd).mp hequal⟩
  · rintro ⟨hc, hd, hequal⟩
    exact ⟨⟨hc, hd⟩, (equalRawCode_correct c d hc hd).mpr hequal⟩

/-- The real normal-code admission column covers the whole actual low
    base-one interval, by the proved normalization coverage theorem. -/
theorem low_domain (c : Nat) :
    (recognizerColumn 3).domain c ↔ acceptedLowCode c = true := by
  simpa [check] using recognizerColumn_domain 3 c

theorem low_covers (ξ : Ordinal.{0}) : ξ < Wilken.globalBoundary 1 0 ↔
    ∃ c : Nat, (recognizerColumn 3).domain c ∧ PublicCodes.interpretation c = ξ := by
  rw [lt_boundary_iff_normalCode]
  simp only [low_domain]

end Alexander313.SourceOneNormalizedProgram
