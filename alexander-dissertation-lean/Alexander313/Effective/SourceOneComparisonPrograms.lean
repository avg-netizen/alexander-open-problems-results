import Alexander313.Wilken.SourceOneNormalPrimitive

/-! # Actual executing base-one comparison Programs

One total machine computes the literal Boolean operations, with zero/one
outputs. A second machine recognizes their positive inputs by actual search.
The checked order/equality columns include both normal-code admissions;
their exact ordinal interpretation follows from the existing constructed
source comparison theorem. Raw comparison columns retain total correctness
even on malformed inputs. No semantic comparison oracle is supplied.
Uncompiled.
-/

namespace Alexander313.SourceOneComparisonProgram

open Wilken (RelativeTerm)
open Wilken.RelativeTerm
open Wilken.RelativeTerm.SourceOne
open Wilken.RelativeTerm.SourceOne.Comparison

def normalCode (c : Nat) : Bool :=
  (decode c).isSome && normalCheck ((decode c).getD (.parameter 0))

theorem normalCode_primrec : Primrec normalCode :=
  Primrec.and.comp (Primrec.option_isSome.comp decode_primrec)
    (Effective.normalCheck_primrec.comp
      (Primrec.option_getD.comp decode_primrec
        (Primrec.const (RelativeTerm.parameter 0 : RelativeTerm Nat))))

def fuelCode (payload : Nat) : Bool :=
  let fuel := payload.unpair.1
  let c := payload.unpair.2.unpair.1
  let d := payload.unpair.2.unpair.2
  ((decode c).isSome && (decode d).isSome) &&
    lessFuel fuel ((decode c).getD (.parameter 0)) ((decode d).getD (.parameter 0))

theorem fuelCode_primrec : Primrec fuelCode := by
  have hf := Primrec.fst.comp Primrec.unpair
  have hp := Primrec.snd.comp Primrec.unpair
  have hc := decode_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hp))
  have hd := decode_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp hp))
  have ht := Primrec.option_getD.comp hc (Primrec.const (.parameter 0))
  have hu := Primrec.option_getD.comp hd (Primrec.const (.parameter 0))
  exact Primrec.and.comp (Primrec.and.comp (Primrec.option_isSome.comp hc)
    (Primrec.option_isSome.comp hd)) (Effective.lessFuel_primrec.comp (hf.pair (ht.pair hu)))

@[simp] theorem fuelCode_trees (fuel : Nat) (t u : RelativeTerm Nat) :
    fuelCode (Nat.pair fuel (Nat.pair t.code u.code)) = lessFuel fuel t u := by
  simp only [fuelCode, Nat.unpair_pair, decode_code, Option.isSome_some, Option.getD_some,
    Bool.true_and]

def admittedPair (c d : Nat) : Bool := acceptedCode c && acceptedCode d

theorem admittedPair_primrec : Primrec₂ admittedPair :=
  (Primrec.and.comp (Effective.acceptedCode_primrec.comp Primrec.fst)
    (Effective.acceptedCode_primrec.comp Primrec.snd)).to₂

/-- Tags 0--6 select normal source admission, raw strict comparison, raw
    equality, admitted strict comparison, admitted equality, raw normality
    and raw comparison with an explicitly supplied fuel. -/
def check (tag payload : Nat) : Bool :=
  let c := payload.unpair.1
  let d := payload.unpair.2
  cond (tag == 0) (acceptedCode payload)
    (cond (tag == 1) (lessCode c d)
      (cond (tag == 2) (equalCode c d)
        (cond (tag == 3) (admittedPair c d && lessCode c d)
          (cond (tag == 4) (admittedPair c d && equalCode c d)
            (cond (tag == 5) (normalCode payload)
              (cond (tag == 6) (fuelCode payload) false))))))

theorem check_primrec : Primrec₂ check := by
  have hc : Primrec (fun p : Nat × Nat => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × Nat => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hl := Effective.lessCode_primrec.comp hc hd
  have he := Effective.equalCode_primrec.comp hc hd
  have ha := admittedPair_primrec.comp hc hd
  have tag (k : Nat) : Primrec (fun p : Nat × Nat => p.1 == k) :=
    Primrec.beq.comp Primrec.fst (Primrec.const k)
  exact ((tag 0).cond (Effective.acceptedCode_primrec.comp Primrec.snd)
    ((tag 1).cond hl ((tag 2).cond he
      ((tag 3).cond (Primrec.and.comp ha hl)
        ((tag 4).cond (Primrec.and.comp ha he)
          ((tag 5).cond (normalCode_primrec.comp Primrec.snd)
            ((tag 6).cond (fuelCode_primrec.comp Primrec.snd) (Primrec.const false)))))))).to₂

def decision (query : Nat) : Nat := cond (check query.unpair.1 query.unpair.2) 1 0

theorem decision_primrec : Primrec decision :=
  (check_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).cond (Primrec.const 1) (Primrec.const 0)

theorem decision_eq_one (query : Nat) :
    decision query = 1 ↔ check query.unpair.1 query.unpair.2 = true := by
  cases h : check query.unpair.1 query.unpair.2 <;> simp [decision, h]

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (decision query) := by
  have h : Partrec (fun query => Part.some (decision query)) := decision_primrec.to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (query : Nat) :
    decisionProgram.eval query = Part.some (decision query) :=
  Classical.choose_spec decisionProgram_exists query

noncomputable def decisionColumn (tag : Nat) : Program := decisionProgram.column tag

/-- Every column returns a defined zero/one answer on every raw natural input. -/
theorem decisionColumn_eval (tag payload : Nat) :
    (decisionColumn tag).eval payload = Part.some (cond (check tag payload) 1 0) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry, decisionProgram_eval]
  simp only [decision, Nat.unpair_pair]

theorem decisionColumn_total (tag payload : Nat) : (decisionColumn tag).domain payload := by
  change ((decisionColumn tag).eval payload).Dom
  rw [decisionColumn_eval]
  trivial

theorem decisionColumn_accepts (tag payload : Nat) :
    1 ∈ (decisionColumn tag).eval payload ↔ check tag payload = true := by
  rw [decisionColumn_eval]
  cases h : check tag payload <;> simp [h]

theorem admission_decision (c : Nat) :
    1 ∈ (decisionColumn 0).eval c ↔ acceptedCode c = true := by
  simpa [check] using decisionColumn_accepts 0 c

theorem less_decision (c d : Nat) :
    1 ∈ (decisionColumn 1).eval (Nat.pair c d) ↔ lessCode c d = true := by
  simpa [check, Nat.unpair_pair] using decisionColumn_accepts 1 (Nat.pair c d)

theorem equal_decision (c d : Nat) :
    1 ∈ (decisionColumn 2).eval (Nat.pair c d) ↔ equalCode c d = true := by
  simpa [check, Nat.unpair_pair] using decisionColumn_accepts 2 (Nat.pair c d)

theorem normal_decision (c : Nat) :
    1 ∈ (decisionColumn 5).eval c ↔ normalCode c = true := by
  simpa [check] using decisionColumn_accepts 5 c

theorem fuel_decision (fuel : Nat) (t u : RelativeTerm Nat) :
    1 ∈ (decisionColumn 6).eval (Nat.pair fuel (Nat.pair t.code u.code)) ↔
      lessFuel fuel t u = true := by
  simpa [check] using decisionColumn_accepts 6 (Nat.pair fuel (Nat.pair t.code u.code))

theorem less_tree_decision (t u : RelativeTerm Nat) :
    1 ∈ (decisionColumn 1).eval (Nat.pair t.code u.code) ↔ less t u = true := by
  simpa only [lessCode_code] using less_decision t.code u.code

theorem equal_tree_decision (t u : RelativeTerm Nat) :
    1 ∈ (decisionColumn 2).eval (Nat.pair t.code u.code) ↔ equal t u = true := by
  simpa only [equalCode_code] using equal_decision t.code u.code

theorem normal_tree_decision (t : RelativeTerm Nat) :
    1 ∈ (decisionColumn 5).eval t.code ↔ normalCheck t = true := by
  simpa [normalCode] using normal_decision t.code

private def constantCheck (query : Nat) (_ : Nat) : Bool :=
  check query.unpair.1 query.unpair.2

private theorem constantCheck_primrec : Primrec₂ constantCheck :=
  ((check_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))).to₂

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

theorem admission_domain (c : Nat) :
    (recognizerColumn 0).domain c ↔ acceptedCode c = true := by
  simpa [check] using recognizerColumn_domain 0 c

theorem order_domain (c d : Nat) : (recognizerColumn 3).domain (Nat.pair c d) ↔
    acceptedCode c = true ∧ acceptedCode d = true ∧
      PublicCodes.interpretation c < PublicCodes.interpretation d := by
  have hraw : (recognizerColumn 3).domain (Nat.pair c d) ↔
      (acceptedCode c = true ∧ acceptedCode d = true) ∧ lessCode c d = true := by
    simpa [check, admittedPair, Nat.unpair_pair] using recognizerColumn_domain 3 (Nat.pair c d)
  rw [hraw]
  constructor
  · rintro ⟨⟨hc, hd⟩, hless⟩
    exact ⟨hc, hd, (lessCode_correct c d hc hd).mp hless⟩
  · rintro ⟨hc, hd, hless⟩
    exact ⟨⟨hc, hd⟩, (lessCode_correct c d hc hd).mpr hless⟩

theorem equality_domain (c d : Nat) : (recognizerColumn 4).domain (Nat.pair c d) ↔
    acceptedCode c = true ∧ acceptedCode d = true ∧
      PublicCodes.interpretation c = PublicCodes.interpretation d := by
  have hraw : (recognizerColumn 4).domain (Nat.pair c d) ↔
      (acceptedCode c = true ∧ acceptedCode d = true) ∧ equalCode c d = true := by
    simpa [check, admittedPair, Nat.unpair_pair] using recognizerColumn_domain 4 (Nat.pair c d)
  rw [hraw]
  constructor
  · rintro ⟨⟨hc, hd⟩, hequal⟩
    exact ⟨hc, hd, (equalCode_correct c d hc hd).mp hequal⟩
  · rintro ⟨hc, hd, hequal⟩
    exact ⟨⟨hc, hd⟩, (equalCode_correct c d hc hd).mpr hequal⟩

end Alexander313.SourceOneComparisonProgram
