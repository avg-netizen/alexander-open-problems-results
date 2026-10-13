import Alexander313.Wilken.HereditaryNativeOmegaPowers
import Alexander313.Wilken.HereditaryNativeSourceChiBaseChangeSupport

/-!
# Literal branch agreement for actual LOW omega powers

All comparisons, normalization, epsilon-head recognition and native
addition/subtraction below are the existing finite operations. Agreement is
proved on genuine original admission at both coded epsilon contexts. In the
public theorem these second-context callers will be derived from the original
atomic-stop payload bound. No ordinal-value equality is used to infer a
syntactic parameter cutoff. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers.BaseChange

open ThetaCourse

theorem lessRawCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Normalization.lessRawCode q c d = Normalization.lessRawCode v c d := by
  have hnc := BaseTransformation.normalizeCode_context q v c hcq hcv
  have hnd := BaseTransformation.normalizeCode_context q v d hdq hdv
  have hccq := (Normalization.normalizeCode_checked q c hcq).1
  have hddq := (Normalization.normalizeCode_checked q d hdq).1
  have hccv : checkCode v (Normalization.normalizeCode q c) = true := by
    rw [hnc]; exact (Normalization.normalizeCode_checked v c hcv).1
  have hddv : checkCode v (Normalization.normalizeCode q d) = true := by
    rw [hnd]; exact (Normalization.normalizeCode_checked v d hdv).1
  have he := SourceChi.BaseChange.lessCode_context q v
    (Normalization.normalizeCode q c) (Normalization.normalizeCode q d) hccq hddq hccv hddv
  simp only [Normalization.lessRawCode, hcq, hdq, hcv, hdv, Bool.true_and]
  exact he.trans (congrArg₂ (Comparison.lessCode v) hnc hnd)

theorem normalizedWord_context (q v c : Nat)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Arithmetic.normalizedWord q c = Arithmetic.normalizedWord v c := by
  simp only [Arithmetic.normalizedWord, BaseTransformation.normalizeCode_context q v c hcq hcv]

theorem addCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Arithmetic.addCode q c d = Arithmetic.addCode v c d := by
  simp only [Arithmetic.addCode, Arithmetic.inputCheck, hcq, hdq, hcv, hdv,
    Bool.true_and, Bool.cond_true, Arithmetic.addTerm, BaseTransformation.normalize_context q v]

theorem subtractCode_context (q v c d : Nat)
    (hcq : checkCode q c = true) (hdq : checkCode q d = true)
    (hcv : checkCode v c = true) (hdv : checkCode v d = true) :
    Arithmetic.subtractCode q c d = Arithmetic.subtractCode v c d := by
  have he : Comparison.equal q = Comparison.equal v :=
    funext fun t => funext fun u => BaseTransformation.equal_context q v t u
  simp only [Arithmetic.subtractCode, Arithmetic.inputCheck, hcq, hdq, hcv, hdv,
    Bool.true_and, Bool.cond_true, Arithmetic.subtractTerm, Arithmetic.leCode,
    lessRawCode_context q v d c hdq hcq hdv hcv, Arithmetic.differenceWord,
    normalizedWord_context q v c hcq hcv, normalizedWord_context q v d hdq hdv, he]

theorem finiteTailCode_context (q v c n : Nat)
    (hq : baseCheck q = true) (hv : baseCheck v = true)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    OmegaPowerHeight.finiteTailCode q c n = OmegaPowerHeight.finiteTailCode v c n := by
  have huq := ((Comparison.acceptedCode_exact q _).mp
    (OmegaPowerHeight.numeralCode_spec q n hq).2.1).1
  have huv := ((Comparison.acceptedCode_exact v _).mp
    (OmegaPowerHeight.numeralCode_spec v n hv).2.1).1
  exact addCode_context q v c (OmegaPowerHeight.numeralCode n) hcq huq hcv huv

theorem word_context (q v c : Nat)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Offsets.word q c = Offsets.word v c := normalizedWord_context q v c hcq hcv

theorem headTree_context (q v c : Nat)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Offsets.headTree q c = Offsets.headTree v c := by
  simp only [Offsets.headTree, word_context q v c hcq hcv]

theorem headCode_context (q v c : Nat)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Offsets.headCode q c = Offsets.headCode v c :=
  congrArg RelativeTerm.code (headTree_context q v c hcq hcv)

theorem offset_context (q v c : Nat)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Offsets.offset q c = Offsets.offset v c := by
  simp only [Offsets.offset, word_context q v c hcq hcv]

theorem headCode_checked (q c : Nat) (hc : checkCode q c = true) :
    checkCode q (Offsets.headCode q c) = true := by
  have hq := (Bool.and_eq_true.mp (Arithmetic.raw_checked q c hc)).1
  cases hw : Offsets.word q c with
  | nil =>
    simpa only [Offsets.headCode, Offsets.headTree, hw, List.head?_nil,
      Option.getD_none, checkCode_code] using Normalization.zeroTree_checked q hq
  | cons t ts =>
    have ht : t ∈ Arithmetic.normalizedWord q c := by
      change t ∈ Offsets.word q c
      rw [hw]; exact List.mem_cons_self
    have htc := (Arithmetic.normalizedWord_spec q c hc).1 t ht
    simpa only [Offsets.headCode, Offsets.headTree, hw, List.head?_cons,
      Option.getD_some, checkCode_code] using htc.1

theorem epsilonAtomCheck_context (q v c : Nat)
    (hq : baseCheck q = true) (hv : baseCheck v = true)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Offsets.epsilonAtomCheck q c = Offsets.epsilonAtomCheck v c := by
  have hbq := ((Comparison.acceptedCode_exact q _).mp (Offsets.baseCode_spec q hq).1).1
  have hbv := ((Comparison.acceptedCode_exact v _).mp (Offsets.baseCode_spec v hv).1).1
  simp only [Offsets.epsilonAtomCheck,
    SourceChi.BaseChange.equalCode_context q v c Offsets.baseCode hcq hbq hcv hbv]

private theorem all_eq_of_mem {α : Type*} (as : List α) (f g : α → Bool)
    (h : ∀ t ∈ as, f t = g t) : as.all f = as.all g := by
  revert h
  induction as with
  | nil => intro h; rfl
  | cons t ts ih =>
    intro h
    simp only [List.all_cons, h t List.mem_cons_self,
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem tailCheck_context (q v c : Nat)
    (hq : baseCheck q = true) (hv : baseCheck v = true)
    (hcq : checkCode q c = true) (hcv : checkCode v c = true) :
    Offsets.tailCheck q c = Offsets.tailCheck v c := by
  have hw := word_context q v c hcq hcv
  have huq := ((Comparison.acceptedCode_exact q _).mp (LogEndZero.unitCode_accepted q hq)).1
  have huv := ((Comparison.acceptedCode_exact v _).mp (LogEndZero.unitCode_accepted v hv)).1
  unfold Offsets.tailCheck
  rw [hw]
  apply all_eq_of_mem
  intro t ht
  have hm : t ∈ Offsets.word v c := List.mem_of_mem_tail ht
  have hmq : t ∈ Arithmetic.normalizedWord q c := by
    change t ∈ Offsets.word q c
    rw [hw]; exact hm
  have hmv : t ∈ Arithmetic.normalizedWord v c := hm
  have htcq := (Arithmetic.normalizedWord_spec q c hcq).1 t hmq
  have htcv := (Arithmetic.normalizedWord_spec v c hcv).1 t hmv
  exact SourceChi.BaseChange.equalCode_context q v t.code LogEndZero.unitCode
    (by simpa only [checkCode_code] using htcq.1) huq
    (by simpa only [checkCode_code] using htcv.1) huv

theorem offsetsCheck_context (q v c : Nat)
    (hcq : lowCheckCode q c = true) (hcv : lowCheckCode v c = true) :
    Offsets.check q c = Offsets.check v c := by
  have hs := HeightBoundary.input_spec q c hcq
  have ht := HeightBoundary.input_spec v c hcv
  have hh := headCode_context q v c hs.1 ht.1
  have hhv : checkCode v (Offsets.headCode q c) = true := by
    rw [hh]; exact headCode_checked v c ht.1
  have he := epsilonAtomCheck_context q v (Offsets.headCode q c) hs.2.1 ht.2.1
    (headCode_checked q c hs.1) hhv
  have he' : Offsets.epsilonAtomCheck q (Offsets.headCode q c) =
      Offsets.epsilonAtomCheck v (Offsets.headCode v c) :=
    he.trans (congrArg (Offsets.epsilonAtomCheck v) hh)
  simp only [Offsets.check, hcq, hcv, word_context q v c hs.1 ht.1,
    he', tailCheck_context q v c hs.2.1 ht.2.1 hs.1 ht.1]

theorem headAbove_context (q v c : Nat)
    (hcq : lowCheckCode q c = true) (hcv : lowCheckCode v c = true) :
    headAbove q c = headAbove v c := by
  have hs := HeightBoundary.input_spec q c hcq
  have ht := HeightBoundary.input_spec v c hcv
  have hbq := ((Comparison.acceptedCode_exact q _).mp (Offsets.baseCode_spec q hs.2.1).1).1
  have hbv := ((Comparison.acceptedCode_exact v _).mp (Offsets.baseCode_spec v ht.2.1).1).1
  have hh := headCode_context q v c hs.1 ht.1
  have hhv : checkCode v (Offsets.headCode q c) = true := by
    rw [hh]; exact headCode_checked v c ht.1
  have he := lessRawCode_context q v Offsets.baseCode (Offsets.headCode q c)
    hbq (headCode_checked q c hs.1) hbv hhv
  simpa only [headAbove, hh] using he

theorem argumentCode_context (q v c : Nat)
    (hcq : lowCheckCode q c = true) (hcv : lowCheckCode v c = true) :
    argumentCode q c = argumentCode v c := by
  have hs := HeightBoundary.input_spec q c hcq
  have ht := HeightBoundary.input_spec v c hcv
  have hh := headCode_context q v c hs.1 ht.1
  have hn := offset_context q v c hs.1 ht.1
  have hhv : checkCode v (Offsets.headCode q c) = true := by
    rw [hh]; exact headCode_checked v c ht.1
  have hf := finiteTailCode_context q v (Offsets.headCode q c) (Offsets.offset q c - 1)
    hs.2.1 ht.2.1 (headCode_checked q c hs.1) hhv
  have hbq := ((Comparison.acceptedCode_exact q _).mp (Offsets.baseCode_spec q hs.2.1).1).1
  have hbv := ((Comparison.acceptedCode_exact v _).mp (Offsets.baseCode_spec v ht.2.1).1).1
  have hd := subtractCode_context q v Offsets.baseCode c hbq hs.1 hbv ht.1
  have ho := offsetsCheck_context q v c hcq hcv
  have ha := headAbove_context q v c hcq hcv
  cases hoff : Offsets.check q c with
  | false =>
    have hoffv : Offsets.check v c = false := ho.symm.trans hoff
    simpa only [argumentCode, hoff, hoffv, Bool.cond_false] using hd
  | true =>
    have hoffv : Offsets.check v c = true := ho.symm.trans hoff
    cases habove : headAbove q c with
    | false =>
      have habovev : headAbove v c = false := ha.symm.trans habove
      simpa only [argumentCode, hoff, hoffv, habove, habovev,
        Bool.cond_true, Bool.cond_false] using congrArg OmegaPowerHeight.numeralCode hn
    | true =>
      have habovev : headAbove v c = true := ha.symm.trans habove
      have hf' : OmegaPowerHeight.finiteTailCode q (Offsets.headCode q c) (Offsets.offset q c - 1) =
          OmegaPowerHeight.finiteTailCode v (Offsets.headCode v c) (Offsets.offset v c - 1) :=
        hf.trans (congrArg₂ (OmegaPowerHeight.finiteTailCode v) hh (congrArg (fun n => n - 1) hn))
      simpa only [argumentCode, hoff, hoffv, habove, habovev, Bool.cond_true] using hf'

/-- This is equality of the actual numerical executing producers, including
all corrected epsilon-finite and native subtraction branches. -/
theorem powerCode_context (q v c : Nat)
    (hcq : lowCheckCode q c = true) (hcv : lowCheckCode v c = true) :
    powerCode q c = powerCode v c := by
  have hs := HeightBoundary.input_spec q c hcq
  have ht := HeightBoundary.input_spec v c hcv
  have hbq := ((Comparison.acceptedCode_exact q _).mp (Offsets.baseCode_spec q hs.2.1).1).1
  have hbv := ((Comparison.acceptedCode_exact v _).mp (Offsets.baseCode_spec v ht.2.1).1).1
  have hl := lessRawCode_context q v c Offsets.baseCode hs.1 hbq ht.1 hbv
  simp only [powerCode, hcq, hcv, hl, offsetsCheck_context q v c hcq hcv,
    offset_context q v c hs.1 ht.1, BaseTransformation.normalizeCode_context q v c hs.1 ht.1,
    argumentCode_context q v c hcq hcv, belowPowerCode]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers.BaseChange
