import Alexander313.Wilken.HereditaryThetaNormalizationPrimitive

/-! # Actual full hereditary normalization and comparison Programs

Original low codes at two arbitrary finite levels are literally embedded into
their common maximum level, normalized by the constructed algorithm, and
compared there. All admission guards are the unchanged original checkers.
The machine computes total decisions and normal codes, and a genuine positive
search machine recognizes the exact admitted order/equality domains under the
original interpretation. No normality assumption on admitted inputs, supplied
semantic comparator or effectivity contract is used. Canonical code uniqueness,
source υ identification and tracking/edge algorithms remain separate. Uncompiled.
-/

namespace Alexander313.HereditaryThetaProgram

open Wilken.RelativeTerm.Hereditary
open Wilken.RelativeTerm.Hereditary.Theta

private theorem low_checked (r c : Nat) (hc : lowCheckCode r c = true) :
    checkCode r c = true :=
  (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1

def alignCode (r s c : Nat) : Nat := BaseArithmetic.embedCode (max r s - r) c

theorem alignCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => alignCode p.1.1 p.1.2 p.2) :=
  BaseArithmetic.embedCode_primrec.comp
    (Primrec.nat_sub.comp (Primrec.nat_max.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.fst)) Primrec.snd

theorem alignCode_checked (r s c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode (max r s) (alignCode r s c) = true := by
  simpa only [alignCode, Nat.add_sub_of_le (le_max_left r s)] using
    embed_old_checked r (max r s - r) c hc

theorem alignCode_value (r s c : Nat) :
    interpretation (max r s) (alignCode r s c) = interpretation r c := by
  simpa only [alignCode, Nat.add_sub_of_le (le_max_left r s)] using
    embed_original_value r (max r s - r) c

def crossLess (r c s d : Nat) : Bool :=
  (lowCheckCode r c && lowCheckCode s d) &&
    Normalization.lessRawCode (max r s) (alignCode r s c) (alignCode s r d)

def crossEqual (r c s d : Nat) : Bool :=
  (lowCheckCode r c && lowCheckCode s d) &&
    Normalization.equalRawCode (max r s) (alignCode r s c) (alignCode s r d)

private theorem aligned_pair_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) =>
      (max p.1.1 p.2.1, (alignCode p.1.1 p.2.1 p.1.2, alignCode p.2.1 p.1.1 p.2.2))) := by
  have hr : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.nat_max.comp hr hs).pair
    ((alignCode_primrec.comp ((hr.pair hs).pair hc)).pair
      (alignCode_primrec.comp ((hs.pair hr).pair hd)))

private theorem crossGuard_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => lowCheckCode p.1.1 p.1.2 && lowCheckCode p.2.1 p.2.2) :=
  Primrec.and.comp (Uniform.hereditaryLowCheckCode_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Uniform.hereditaryLowCheckCode_primrec.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem crossLess_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => crossLess p.1.1 p.1.2 p.2.1 p.2.2) :=
  Primrec.and.comp crossGuard_primrec
    (Normalization.Effective.lessRawCode_primrec.comp aligned_pair_primrec)

theorem crossEqual_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × Nat) => crossEqual p.1.1 p.1.2 p.2.1 p.2.2) :=
  Primrec.and.comp crossGuard_primrec
    (Normalization.Effective.equalRawCode_primrec.comp aligned_pair_primrec)

theorem crossLess_exact (r c s d : Nat) : crossLess r c s d = true ↔
    lowCheckCode r c = true ∧ lowCheckCode s d = true ∧ interpretation r c < interpretation s d := by
  simp only [crossLess, Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨hc, hd, hcmp⟩
    have hc' := low_checked _ _ (alignCode_checked r s c hc)
    have hd' : checkCode (max r s) (alignCode s r d) = true := by
      simpa only [max_comm s r] using low_checked _ _ (alignCode_checked s r d hd)
    have h := (Normalization.lessRawCode_correct _ _ _ hc' hd').mp hcmp
    rw [alignCode_value r s c, show interpretation (max r s) (alignCode s r d) =
      interpretation s d from by simpa only [max_comm s r] using alignCode_value s r d] at h
    exact ⟨hc, hd, h⟩
  · rintro ⟨hc, hd, hcmp⟩
    have hc' := low_checked _ _ (alignCode_checked r s c hc)
    have hd' : checkCode (max r s) (alignCode s r d) = true := by
      simpa only [max_comm s r] using low_checked _ _ (alignCode_checked s r d hd)
    refine ⟨hc, hd, (Normalization.lessRawCode_correct _ _ _ hc' hd').mpr ?_⟩
    simpa only [alignCode_value r s c,
      show interpretation (max r s) (alignCode s r d) = interpretation s d from by
        simpa only [max_comm s r] using alignCode_value s r d] using hcmp

theorem crossEqual_exact (r c s d : Nat) : crossEqual r c s d = true ↔
    lowCheckCode r c = true ∧ lowCheckCode s d = true ∧ interpretation r c = interpretation s d := by
  simp only [crossEqual, Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨hc, hd, hcmp⟩
    have hc' := low_checked _ _ (alignCode_checked r s c hc)
    have hd' : checkCode (max r s) (alignCode s r d) = true := by
      simpa only [max_comm s r] using low_checked _ _ (alignCode_checked s r d hd)
    have h := (Normalization.equalRawCode_correct _ _ _ hc' hd').mp hcmp
    rw [alignCode_value r s c, show interpretation (max r s) (alignCode s r d) =
      interpretation s d from by simpa only [max_comm s r] using alignCode_value s r d] at h
    exact ⟨hc, hd, h⟩
  · rintro ⟨hc, hd, hcmp⟩
    have hc' := low_checked _ _ (alignCode_checked r s c hc)
    have hd' : checkCode (max r s) (alignCode s r d) = true := by
      simpa only [max_comm s r] using low_checked _ _ (alignCode_checked s r d hd)
    refine ⟨hc, hd, (Normalization.equalRawCode_correct _ _ _ hc' hd').mpr ?_⟩
    simpa only [alignCode_value r s c,
      show interpretation (max r s) (alignCode s r d) = interpretation s d from by
        simpa only [max_comm s r] using alignCode_value s r d] using hcmp

def sameLess (r c d : Nat) : Bool :=
  (checkCode r c && checkCode r d) && Normalization.lessRawCode r c d

def sameEqual (r c d : Nat) : Bool :=
  (checkCode r c && checkCode r d) && Normalization.equalRawCode r c d

theorem sameLess_exact (r c d : Nat) : sameLess r c d = true ↔
    checkCode r c = true ∧ checkCode r d = true ∧ interpretation r c < interpretation r d := by
  simp only [sameLess, Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨hc, hd, h⟩
    exact ⟨hc, hd, (Normalization.lessRawCode_correct r c d hc hd).mp h⟩
  · rintro ⟨hc, hd, h⟩
    exact ⟨hc, hd, (Normalization.lessRawCode_correct r c d hc hd).mpr h⟩

theorem sameEqual_exact (r c d : Nat) : sameEqual r c d = true ↔
    checkCode r c = true ∧ checkCode r d = true ∧ interpretation r c = interpretation r d := by
  simp only [sameEqual, Bool.and_eq_true, and_assoc]
  constructor
  · rintro ⟨hc, hd, h⟩
    exact ⟨hc, hd, (Normalization.equalRawCode_correct r c d hc hd).mp h⟩
  · rintro ⟨hc, hd, h⟩
    exact ⟨hc, hd, (Normalization.equalRawCode_correct r c d hc hd).mpr h⟩

private theorem sameGuard_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.1 && checkCode p.1 p.2.2) :=
  Primrec.and.comp (Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem sameLess_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => sameLess p.1 p.2.1 p.2.2) :=
  Primrec.and.comp sameGuard_primrec Normalization.Effective.lessRawCode_primrec

theorem sameEqual_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => sameEqual p.1 p.2.1 p.2.2) :=
  Primrec.and.comp sameGuard_primrec Normalization.Effective.equalRawCode_primrec

def check (tag payload : Nat) : Bool :=
  let r := payload.unpair.1
  let c := payload.unpair.2
  let rc := payload.unpair.1.unpair
  let sd := payload.unpair.2.unpair
  cond (tag == 0) (checkCode r c)
    (cond (tag == 1) (lowCheckCode r c)
      (cond (tag == 2) (acceptedCode r c)
        (cond (tag == 3) (acceptedLowCode r c)
          (cond (tag == 4) (sameLess r c.unpair.1 c.unpair.2)
            (cond (tag == 5) (sameEqual r c.unpair.1 c.unpair.2)
              (cond (tag == 6) (crossLess rc.1 rc.2 sd.1 sd.2)
                (cond (tag == 7) (crossEqual rc.1 rc.2 sd.1 sd.2) false)))))))

theorem check_primrec : Primrec₂ check := by
  have hp : Primrec (fun p : Nat × Nat => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hc := Primrec.snd.comp hp
  have hcd := Primrec.unpair.comp hc
  have hpair := (Primrec.unpair.comp hr).pair (Primrec.unpair.comp hc)
  have tag (i : Nat) : Primrec (fun p : Nat × Nat => p.1 == i) :=
    Primrec.beq.comp Primrec.fst (Primrec.const i)
  exact ((tag 0).cond (Uniform.hereditaryCheckCode_primrec.comp hr hc)
    ((tag 1).cond (Uniform.hereditaryLowCheckCode_primrec.comp hr hc)
      ((tag 2).cond (Effective.acceptedCode_primrec.comp hr hc)
        ((tag 3).cond (Effective.acceptedLowCode_primrec.comp hr hc)
          ((tag 4).cond (sameLess_primrec.comp (hr.pair hcd))
            ((tag 5).cond (sameEqual_primrec.comp (hr.pair hcd))
              ((tag 6).cond (crossLess_primrec.comp hpair)
                ((tag 7).cond (crossEqual_primrec.comp hpair) (Primrec.const false))))))))).to₂

def output (tag payload : Nat) : Nat :=
  cond (tag == 8) (Normalization.normalizeCode payload.unpair.1 payload.unpair.2)
    (cond (check tag payload) 1 0)

theorem output_primrec : Primrec₂ output :=
  ((Primrec.beq.comp Primrec.fst (Primrec.const 8)).cond
    (Normalization.Effective.normalizeCode_primrec.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
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

theorem normalize_eval (r c : Nat) : (decisionColumn 8).eval (Nat.pair r c) =
    Part.some (Normalization.normalizeCode r c) := by
  simpa [output, Nat.unpair_pair] using decisionColumn_eval 8 (Nat.pair r c)

theorem normalize_original (r c : Nat) (hc : checkCode r c = true) :
    acceptedCode r (Normalization.normalizeCode r c) = true ∧
      interpretation r (Normalization.normalizeCode r c) = interpretation r c := by
  have hs := Normalization.normalizeCode_checked r c hc
  exact ⟨(acceptedCode_iff _ _).mpr ⟨hs.1, hs.2.1⟩, hs.2.2⟩

theorem normalize_original_low (r c : Nat) (hc : lowCheckCode r c = true) :
    acceptedLowCode r (Normalization.normalizeCode r c) = true ∧
      interpretation r (Normalization.normalizeCode r c) = interpretation r c := by
  have hs := Normalization.normalizeCode_lowChecked r c hc
  exact ⟨(acceptedLowCode_iff _ _).mpr ⟨hs.1, hs.2.1⟩, hs.2.2⟩

private def constantCheck (query : Nat) (_ : Nat) : Bool := check query.unpair.1 query.unpair.2

private theorem constantCheck_primrec : Primrec₂ constantCheck :=
  (check_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (constantCheck query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind constantCheck_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) : (evaluation query).Dom ↔
    check query.unpair.1 query.unpair.2 = true := by
  simp only [evaluation, constantCheck, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem recognizer_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ check query.unpair.1 query.unpair.2 = true := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, fun query => ?_⟩
  simpa only [Program.domain, hp] using evaluation_domain query

noncomputable def recognizer : Program := Classical.choose recognizer_exists

theorem recognizer_domain (query : Nat) : recognizer.domain query ↔
    check query.unpair.1 query.unpair.2 = true := Classical.choose_spec recognizer_exists query

noncomputable def recognizerColumn (tag : Nat) : Program := recognizer.column tag

theorem recognizerColumn_domain (tag payload : Nat) :
    (recognizerColumn tag).domain payload ↔ check tag payload = true := by
  simp only [recognizerColumn, Program.column_domain, recognizer_domain, Nat.unpair_pair]

theorem admission_domain (r c : Nat) : (recognizerColumn 0).domain (Nat.pair r c) ↔
    checkCode r c = true := by
  simpa [check, Nat.unpair_pair] using recognizerColumn_domain 0 (Nat.pair r c)

theorem low_domain (r c : Nat) : (recognizerColumn 1).domain (Nat.pair r c) ↔
    lowCheckCode r c = true := by
  simpa [check, Nat.unpair_pair] using recognizerColumn_domain 1 (Nat.pair r c)

theorem normal_domain (r c : Nat) : (recognizerColumn 2).domain (Nat.pair r c) ↔
    checkCode r c = true ∧ Normal r (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  simpa [check, Nat.unpair_pair, acceptedCode_iff] using recognizerColumn_domain 2 (Nat.pair r c)

theorem normal_low_domain (r c : Nat) : (recognizerColumn 3).domain (Nat.pair r c) ↔
    lowCheckCode r c = true ∧ Normal r (Wilken.RelativeTerm.Hereditary.ThetaCourse.rawTree c) := by
  simpa [check, Nat.unpair_pair, acceptedLowCode_iff] using recognizerColumn_domain 3 (Nat.pair r c)

theorem same_order_domain (r c d : Nat) :
    (recognizerColumn 4).domain (Nat.pair r (Nat.pair c d)) ↔
      checkCode r c = true ∧ checkCode r d = true ∧ interpretation r c < interpretation r d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using sameLess_exact r c d

theorem same_equality_domain (r c d : Nat) :
    (recognizerColumn 5).domain (Nat.pair r (Nat.pair c d)) ↔
      checkCode r c = true ∧ checkCode r d = true ∧ interpretation r c = interpretation r d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using sameEqual_exact r c d

theorem cross_order_domain (r c s d : Nat) :
    (recognizerColumn 6).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      lowCheckCode r c = true ∧ lowCheckCode s d = true ∧ interpretation r c < interpretation s d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using crossLess_exact r c s d

theorem cross_equality_domain (r c s d : Nat) :
    (recognizerColumn 7).domain (Nat.pair (Nat.pair r c) (Nat.pair s d)) ↔
      lowCheckCode r c = true ∧ lowCheckCode s d = true ∧ interpretation r c = interpretation s d := by
  rw [recognizerColumn_domain]
  simpa [check, Nat.unpair_pair] using crossEqual_exact r c s d

theorem union_order_domain (q v : Nat) : (recognizerColumn 6).domain (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q < unionInterpretation v := by
  have hq : Nat.pair q.unpair.1 q.unpair.2 = q := Nat.pair_unpair q
  have hv : Nat.pair v.unpair.1 v.unpair.2 = v := Nat.pair_unpair v
  simpa only [hq, hv, unionCheck, unionInterpretation] using
    cross_order_domain q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2

theorem union_equality_domain (q v : Nat) : (recognizerColumn 7).domain (Nat.pair q v) ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q = unionInterpretation v := by
  have hq : Nat.pair q.unpair.1 q.unpair.2 = q := Nat.pair_unpair q
  have hv : Nat.pair v.unpair.1 v.unpair.2 = v := Nat.pair_unpair v
  simpa only [hq, hv, unionCheck, unionInterpretation] using
    cross_equality_domain q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2

end Alexander313.HereditaryThetaProgram
