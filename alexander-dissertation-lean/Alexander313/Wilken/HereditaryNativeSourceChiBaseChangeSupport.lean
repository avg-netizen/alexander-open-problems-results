import Alexander313.Wilken.HereditaryNativeSourceChi
import Alexander313.Wilken.HereditaryNativeBaseTransformation

/-!
# Actual branch transport for the native indicator

Every comparison below runs the original finite native algorithm. Its context
agreement is used only with original admission at both coded epsilon bases;
all higher-presentation and last-component comparison callers are derived
from the actual ANF and reconstructed high/low words. The original repaired
fixed-point classifier, including its epsilon-base boundary, is unchanged.
No fixed-point, support, indicator or base-change oracle is supplied.
These source proofs are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.BaseChange

theorem acceptedCode_context (q v c : Nat)
    (hq : checkCode q c = true) (hv : checkCode v c = true) :
    Comparison.acceptedCode q c = Comparison.acceptedCode v c := by
  simp only [Comparison.acceptedCode, hq, hv, Bool.true_and,
    BaseTransformation.normalCheck_context q v]

theorem lessCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Comparison.lessCode q c d = Comparison.lessCode v c d := by
  simp only [Comparison.lessCode, acceptedCode_context q v c hcq hcv,
    acceptedCode_context q v d hdq hdv, BaseTransformation.less_context q v]

theorem equalCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Comparison.equalCode q c d = Comparison.equalCode v c d := by
  simp only [Comparison.equalCode, acceptedCode_context q v c hcq hcv,
    acceptedCode_context q v d hdq hdv, BaseTransformation.equal_context q v]

private theorem checkedCode (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    checkCode q t.code = true := by simpa only [checkCode_code] using ht

private theorem accepted_original (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    checkCode q c = true := ((Decomposition.inputCheck_exact q c).mp hc).1

theorem decomposition_input_context (q v c : Nat)
    (hq : checkCode q c = true) (hv : checkCode v c = true) :
    Decomposition.inputCheck q c = Decomposition.inputCheck v c :=
  acceptedCode_context q v c hq hv

theorem fixed_input_context (q v m c : Nat)
    (hq : checkCode q c = true) (hv : checkCode v c = true) :
    FixedPoint.inputCheck q m c = FixedPoint.inputCheck v m c := by
  simp only [FixedPoint.inputCheck, decomposition_input_context q v c hq hv]

/-- The star predicate compares the same actual exposed nodes, using the
derived context-independent finite comparator. -/
theorem starCode_context (q v m d e : Nat) :
    FixedPoint.starCode q m d e = FixedPoint.starCode v m d e := by
  unfold FixedPoint.starCode FixedPoint.starLess
  apply List.all_congr rfl
  intro s
  exact BaseTransformation.less_context q v s _

theorem nodeCandidate_context (q v m d e : Nat)
    (hdq : Decomposition.inputCheck q d = true) (heq : Decomposition.inputCheck q e = true)
    (hdv : Decomposition.inputCheck v d = true) (hev : Decomposition.inputCheck v e = true)
    (s : RelativeTerm Nat) (hs : s ∈ Decomposition.word e) :
    FixedPoint.nodeCandidate q m d e s = FixedPoint.nodeCandidate v m d e s := by
  have hnq := (Decomposition.word_spec q e heq).1 s hs
  have hnv := (Decomposition.word_spec v e hev).1 s hs
  cases s with
  | parameter p => rfl
  | sum a b => rfl
  | theta k a =>
    have haq := (SourceChi.theta_argument_parts q k a hnq.1 hnq.2.1).1
    have hav := (SourceChi.theta_argument_parts v k a hnv.1 hnv.2.1).1
    have hhq := (Decomposition.parts_accepted q m a.code haq).1
    have hhv := (Decomposition.parts_accepted v m a.code hav).1
    have he := equalCode_context q v e (.theta k a : RelativeTerm Nat).code
      (accepted_original q e heq) (checkedCode q _ hnq.1)
      (accepted_original v e hev) (checkedCode v _ hnv.1)
    have hl := lessCode_context q v d (Decomposition.highCode m a.code)
      (accepted_original q d hdq) ((Comparison.acceptedCode_exact q _).mp hhq).1
      (accepted_original v d hdv) ((Comparison.acceptedCode_exact v _).mp hhv).1
    simp only [FixedPoint.nodeCandidate, he, hl]

private theorem any_eq_of_mem {alpha : Type*} (as : List alpha) (f g : alpha → Bool)
    (h : ∀ a ∈ as, f a = g a) : as.any f = as.any g := by
  revert h
  induction as with
  | nil => intro h; rfl
  | cons a as ih =>
    intro h
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem higherCheck_context (q v m d e : Nat)
    (hdq : Decomposition.inputCheck q d = true) (heq : Decomposition.inputCheck q e = true)
    (hdv : Decomposition.inputCheck v d = true) (hev : Decomposition.inputCheck v e = true) :
    FixedPoint.higherCheck q m d e = FixedPoint.higherCheck v m d e := by
  have ha := any_eq_of_mem (Decomposition.word e)
    (FixedPoint.nodeCandidate q m d e) (FixedPoint.nodeCandidate v m d e)
    (fun s hs => nodeCandidate_context q v m d e hdq heq hdv hev s hs)
  simp only [FixedPoint.higherCheck, starCode_context q v, ha]

theorem fixedCode_context (q v m c : Nat)
    (hq : Decomposition.inputCheck q c = true) (hv : Decomposition.inputCheck v c = true) :
    FixedPoint.fixedCode q m c = FixedPoint.fixedCode v m c := by
  have hpq := Decomposition.parts_accepted q m c hq
  have hpv := Decomposition.parts_accepted v m c hv
  have hi := fixed_input_context q v m c (accepted_original q c hq) (accepted_original v c hv)
  have hh := higherCheck_context q v m (Decomposition.highCode m c) (Decomposition.lowCode m c)
    hpq.1 hpq.2 hpv.1 hpv.2
  simp only [FixedPoint.fixedCode, hi, hh]

theorem strictCode_context (q v m c : Nat)
    (hq : Decomposition.inputCheck q c = true) (hv : Decomposition.inputCheck v c = true) :
    FixedPoint.strictCode q m c = FixedPoint.strictCode v m c := by
  simp only [FixedPoint.strictCode,
    fixed_input_context q v m c (accepted_original q c hq) (accepted_original v c hv),
    fixedCode_context q v m c hq hv]

theorem logendZero_context (q v c : Nat)
    (hq : Decomposition.inputCheck q c = true) (hv : Decomposition.inputCheck v c = true) :
    LogEndZero.zeroCheck q c = LogEndZero.zeroCheck v c := by
  have hbq := (Bool.and_eq_true.mp (Decomposition.input_tree q c hq).1).1
  have hbv := (Bool.and_eq_true.mp (Decomposition.input_tree v c hv).1).1
  have heq := LogEndZero.endCode_accepted q c hq
  have hev := LogEndZero.endCode_accepted v c hv
  have huq := LogEndZero.unitCode_accepted q hbq
  have huv := LogEndZero.unitCode_accepted v hbv
  have he := equalCode_context q v (LogEndZero.endCode c) LogEndZero.unitCode
    (accepted_original q _ heq) (accepted_original q _ huq)
    (accepted_original v _ hev) (accepted_original v _ huv)
  simp only [LogEndZero.zeroCheck, hq, hv, he]

theorem chooseHigh_context (q v m c : Nat)
    (hq : Decomposition.inputCheck q c = true) (hv : Decomposition.inputCheck v c = true) :
    SourceChi.chooseHigh q m c = SourceChi.chooseHigh v m c := by
  have hpq := (Decomposition.parts_accepted q m c hq).2
  have hpv := (Decomposition.parts_accepted v m c hv).2
  simp only [SourceChi.chooseHigh, fixedCode_context q v m c hq hv,
    logendZero_context q v (Decomposition.lowCode m c) hpq hpv]

/-- Every label, including the final high label used for the rebuilt Delta,
is transported by genuine finite syntax induction. -/
theorem state_context (q v : Nat) (t : RelativeTerm Nat)
    (hq : check q t = true) (hv : check v t = true) (hn : Comparison.Normal q t) :
    SourceChi.state q t = SourceChi.state v t := by
  revert hq hv hn
  induction t with
  | parameter p => intro hq hv hn; rfl
  | sum a b iha ihb =>
    intro hq hv hn
    have hs := SourceChi.sum_children q a b hq hn
    have ht := BaseTransformation.sum_checks v a b hv
    change SourceChi.sumState (SourceChi.state q a) (SourceChi.state q b) =
      SourceChi.sumState (SourceChi.state v a) (SourceChi.state v b)
    rw [iha hs.1 ht.1 hs.2.1, ihb hs.2.2.1 ht.2 hs.2.2.2.1]
  | theta m a ih =>
    intro hq hv hn
    have haq := SourceChi.theta_argument_parts q m a hq hn
    have hna : Comparison.Normal v (.theta m a) :=
      (BaseTransformation.normal_context q v _ hq hv).mp hn
    have hav := SourceChi.theta_argument_parts v m a hv hna
    have he := ih (FixedPoint.checked_theta_argument q m a hq)
      (FixedPoint.checked_theta_argument v m a hv) hn
    have hb : SourceChi.baseCase q m a.code = SourceChi.baseCase v m a.code := rfl
    have hc := chooseHigh_context q v m a.code haq.1 hav.1
    change SourceChi.thetaState q m (SourceChi.state q a) =
      SourceChi.thetaState v m (SourceChi.state v a)
    rw [he]
    unfold SourceChi.thetaState
    simp only [SourceChi.state_tree, hb, hc]

theorem indicator_context (q v : Nat) (t : RelativeTerm Nat)
    (hq : check q t = true) (hv : check v t = true) (hn : Comparison.Normal q t) :
    SourceChi.indicator q t = SourceChi.indicator v t :=
  congrArg (fun s : SourceChi.State => s.2.1) (state_context q v t hq hv hn)

theorem chiCode_context (q v c : Nat)
    (hq : Decomposition.inputCheck q c = true) (hv : Decomposition.inputCheck v c = true) :
    SourceChi.chiCode q c = SourceChi.chiCode v c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp (accepted_original q c hq)
  have htv : check v t = true := by simpa only [checkCode_code] using accepted_original v t.code hv
  have hn : Comparison.Normal q t := by
    simpa only [ThetaCourse.rawTree_code] using ((Decomposition.inputCheck_exact q t.code).mp hq).2
  have hnv := (BaseTransformation.normal_context q v t ht htv).mp hn
  rw [SourceChi.chiCode_correct q t ht hn, SourceChi.chiCode_correct v t htv hnv]
  exact indicator_context q v t ht htv hn

theorem dualCode_context (q v c : Nat)
    (hq : Decomposition.inputCheck q c = true) (hv : Decomposition.inputCheck v c = true) :
    SourceChi.dualCode q c = SourceChi.dualCode v c := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact q c).mp (accepted_original q c hq)
  have htv : check v t = true := by simpa only [checkCode_code] using accepted_original v t.code hv
  have hn : Comparison.Normal q t := by
    simpa only [ThetaCourse.rawTree_code] using ((Decomposition.inputCheck_exact q t.code).mp hq).2
  have hnv := (BaseTransformation.normal_context q v t ht htv).mp hn
  rw [SourceChi.dualCode_correct q t ht hn, SourceChi.dualCode_correct v t htv hnv,
    indicator_context q v t ht htv hn]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.BaseChange
