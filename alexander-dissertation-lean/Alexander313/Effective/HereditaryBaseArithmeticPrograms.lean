import Alexander313.Wilken.HereditaryBaseArithmeticCodes

/-! # Actual cross-level arithmetic fragment Programs

The total machine executes the uniform fragment checker, cross-level ordinal
order/equality and literal principal-word normalization. The positive search
machine retains fragment admission on both inputs before comparison. Every
accepted fragment code passes the unchanged hereditary low checker, and all
semantic statements use the original interpretation and unionInterpretation.
This is a strict public-grammar subclass: arbitrary later-base theta arguments
and full hereditary normalization/comparison are not claimed. Uncompiled.
-/

namespace Alexander313.HereditaryBaseArithmeticProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.RelativeTerm.Hereditary.BaseArithmetic

def check (tag payload : Nat) : Bool :=
  let rc := payload.unpair.1.unpair
  let sd := payload.unpair.2.unpair
  cond (tag == 0) (BaseArithmetic.checkCode payload.unpair.1 payload.unpair.2)
    (cond (tag == 1) (BaseArithmetic.less rc.1 rc.2 sd.1 sd.2)
      (cond (tag == 2) (BaseArithmetic.equal rc.1 rc.2 sd.1 sd.2) false))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hl := Primrec.unpair.comp (Primrec.fst.comp hp)
  have hr := Primrec.unpair.comp (Primrec.snd.comp hp)
  have ha := BaseArithmetic.checkCode_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp)
  have hc := BaseArithmetic.less_primrec.comp (hl.pair hr)
  have he := BaseArithmetic.equal_primrec.comp (hl.pair hr)
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond ha ((tag 1).cond hc ((tag 2).cond he (Primrec.const false)))).to₂

def output (tag payload : Nat) : Nat :=
  cond (tag == 3)
    (Encodable.encode (BaseAtoms.normalize (BaseArithmetic.words payload.unpair.1 payload.unpair.2)))
    (cond (check tag payload) 1 0)

theorem output_primrec : Primrec₂ output := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hw := BaseArithmetic.words_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp)
  have hn := Primrec.encode.comp (BaseAtoms.normalize_primrec.comp hw)
  exact ((Primrec.beq.comp Primrec.fst (Primrec.const 3)).cond hn
    (check_primrec.cond (Primrec.const 1) (Primrec.const 0))).to₂

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (output query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (output query.unpair.1 query.unpair.2)) :=
    (output_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
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

theorem admission_decision (r c : Nat) :
    1 ∈ (decisionColumn 0).eval (Nat.pair r c) ↔ BaseArithmetic.checkCode r c = true := by
  rw [decisionColumn_eval]
  cases h : BaseArithmetic.checkCode r c <;> simp [output, check, Nat.unpair_pair, h]

theorem less_decision (r c s d : Nat) :
    1 ∈ (decisionColumn 1).eval (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      BaseArithmetic.less r c s d = true := by
  rw [decisionColumn_eval]
  cases h : BaseArithmetic.less r c s d <;> simp [output, check, Nat.unpair_pair, h]

theorem equal_decision (r c s d : Nat) :
    1 ∈ (decisionColumn 2).eval (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      BaseArithmetic.equal r c s d = true := by
  rw [decisionColumn_eval]
  cases h : BaseArithmetic.equal r c s d <;> simp [output, check, Nat.unpair_pair, h]

/-- The result is a literal coded principal word, not a canonical public tree. -/
theorem normalized_word_eval (r c : Nat) :
    (decisionColumn 3).eval (Nat.pair r c) =
      Part.some (Encodable.encode (BaseAtoms.normalize (BaseArithmetic.words r c))) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 3 (Nat.pair r c)

theorem normalized_word_value (r c : Nat) (hc : BaseArithmetic.checkCode r c = true) :
    Wilken.principalSum ((BaseAtoms.normalize (BaseArithmetic.words r c)).map BaseAtoms.value) =
      interpretation r c := by
  have hs := BaseArithmetic.words_spec r c hc
  exact (BaseAtoms.normalize_value _ hs.1).trans hs.2

private def constantCheck (query : Nat) (_ : Nat) : Bool := check query.unpair.1 query.unpair.2

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

theorem admission_domain (r c : Nat) : (recognizerColumn 0).domain (Nat.pair r c) ↔
    BaseArithmetic.checkCode r c = true := by
  simpa [check, Nat.unpair_pair] using recognizerColumn_domain 0 (Nat.pair r c)

theorem admission_original (r c : Nat) (hc : (recognizerColumn 0).domain (Nat.pair r c)) :
    lowCheckCode r c = true ∧ unionCheck (Nat.pair r c) = true := by
  have h := BaseArithmetic.checkCode_old r c ((admission_domain r c).mp hc)
  exact ⟨h, by simpa only [unionCheck_pair] using h⟩

theorem admission_only_trees (r c : Nat) (hc : (recognizerColumn 0).domain (Nat.pair r c)) :
    ∃ t : Wilken.RelativeTerm Nat, t.code = c ∧ BaseArithmetic.Grammar r t :=
  (BaseArithmetic.state_exact r c).mp ((admission_domain r c).mp hc)

theorem order_domain (r c s d : Nat) :
    (recognizerColumn 1).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      BaseArithmetic.checkCode r c = true ∧ BaseArithmetic.checkCode s d = true ∧
        interpretation r c < interpretation s d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using BaseArithmetic.less_exact r c s d

theorem equality_domain (r c s d : Nat) :
    (recognizerColumn 2).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      BaseArithmetic.checkCode r c = true ∧ BaseArithmetic.checkCode s d = true ∧
        interpretation r c = interpretation s d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using BaseArithmetic.equal_exact r c s d

theorem order_union_interpretation (r c s d : Nat) :
    (recognizerColumn 1).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      BaseArithmetic.checkCode r c = true ∧ BaseArithmetic.checkCode s d = true ∧
        unionInterpretation (Nat.pair r c) < unionInterpretation (Nat.pair s d) := by
  simpa only [unionInterpretation_pair] using order_domain r c s d

theorem equality_union_interpretation (r c s d : Nat) :
    (recognizerColumn 2).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      BaseArithmetic.checkCode r c = true ∧ BaseArithmetic.checkCode s d = true ∧
        unionInterpretation (Nat.pair r c) = unionInterpretation (Nat.pair s d) := by
  simpa only [unionInterpretation_pair] using equality_domain r c s d

end Alexander313.HereditaryBaseArithmeticProgram
