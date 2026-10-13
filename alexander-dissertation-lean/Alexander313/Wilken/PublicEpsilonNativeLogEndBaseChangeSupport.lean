import Alexander313.Wilken.HereditaryNativeLogEnd
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChange

/-!
# Actual LOW logarithm branch agreement at two coded epsilon contexts

The original raw LOW checkers derive every normalized final-atom and LOW
argument caller. Real epsilon-finite parsing, addition and finite-tail
operations agree literally. The public parameter logarithm is the same
actual computation, and a high theta-zero epsilon atom returns itself.
No log, caller, Normality or branch oracle. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd.BaseChange

open ThetaCourse

theorem aboveOffset_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : Support.aboveOffset q c = Support.aboveOffset v c := by
  simp only [Support.aboveOffset, OmegaPowers.BaseChange.offsetsCheck_context q v c hcq hcv,
    OmegaPowers.BaseChange.headAbove_context q v c hcq hcv]

theorem correctedCode_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : Support.correctedCode q c = Support.correctedCode v c := by
  have hq := HeightBoundary.input_spec q c hcq
  have hv := HeightBoundary.input_spec v c hcv
  have hbq := ((Comparison.acceptedCode_exact q _).mp (OmegaPowers.Offsets.baseCode_spec q hq.2.1).1).1
  have hbv := ((Comparison.acceptedCode_exact v _).mp (OmegaPowers.Offsets.baseCode_spec v hv.2.1).1).1
  simp only [Support.correctedCode, aboveOffset_context q v c hcq hcv,
    OmegaPowers.BaseChange.finiteTailCode_context q v c 1 hq.2.1 hv.2.1 hq.1 hv.1,
    OmegaPowers.BaseChange.addCode_context q v OmegaPowers.Offsets.baseCode c hbq hq.1 hbv hv.1]

theorem atom_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true)
    (shape : (∃ p, rawTree c = .parameter p) ∨ ∃ k a, rawTree c = .theta k a) : atom q c = atom v c := by
  have hi := HeightBoundary.input_spec q c hcq
  have he : (rawTree c).code = c := by
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hi.1
    simp only [← ht, rawTree_code]
  rcases shape with ⟨p, hp⟩ | ⟨k, a, ha⟩
  · rw [← he, hp, atom_parameter, atom_parameter]
  · have hcode : (.theta k a : RelativeTerm Nat).code = c := by rw [← ha]; exact he
    have hk := Support.theta_low_index q k a (by simpa only [hcode] using hcq)
    subst k
    rw [← hcode, atom_theta_zero, atom_theta_zero]
    cases hh : Decomposition.above 0 a with
    | true => rfl
    | false =>
      have htq : check q (.theta 0 a) = true := by
        simpa only [checkCode_code] using (HeightBoundary.input_spec q _ (by simpa only [hcode] using hcq)).1
      have htv : check v (.theta 0 a) = true := by
        simpa only [checkCode_code] using (HeightBoundary.input_spec v _ (by simpa only [hcode] using hcv)).1
      simp only [hh, Bool.cond_false, correctedCode_context q v a.code
        (Support.theta_argument_low q a htq hh) (Support.theta_argument_low v a htv hh)]

/-- Every original RAW LOW input has literally the same actual partial
last-exponent computation whenever both original checkers admit it. -/
theorem execute_context (q v c : Nat) (hcq : lowCheckCode q c = true)
    (hcv : lowCheckCode v c = true) : execute q c = execute v c := by
  have hq := HeightBoundary.input_spec q c hcq
  have hv := HeightBoundary.input_spec v c hcv
  have he := BaseTransformation.normalizeCode_context q v c hq.1 hv.1
  have hnq := Normalization.normalizeCode_accepted q c hq.1
  have hnv : Decomposition.inputCheck v (Normalization.normalizeCode q c) = true := by
    rw [he]
    exact (Normalization.normalizeCode_accepted v c hv.1).1
  have hlowv : lowCheckCode v (Normalization.normalizeCode q c) = true := by
    rw [he]; exact normalized_low v c hcv
  cases hz : FixedPoint.zeroCheck (Normalization.normalizeCode q c) with
  | true => simp only [execute, hcq, hcv, ← he, hz, Bool.cond_true]
  | false =>
    have hneq : interpretation q (Normalization.normalizeCode q c) ≠ 0 := by
      intro h
      have ht := (FixedPoint.zeroCheck_exact q _ hnq.1).mpr h
      simp only [hz, Bool.false_eq_true] at ht
    have hnev : interpretation v (Normalization.normalizeCode q c) ≠ 0 := by
      intro h
      have ht := (FixedPoint.zeroCheck_exact v _ hnv).mpr h
      simp only [hz, Bool.false_eq_true] at ht
    have hsq := Support.endCode_spec q _ (normalized_low q c hcq) hnq.1 hneq
    have hsv := Support.endCode_spec v _ hlowv hnv hnev
    have ha := atom_context q v _ hsq.1 hsv.1 hsq.2.2.2.2.2
    simp only [execute, hcq, hcv, ← he, hz, Bool.cond_true, Bool.cond_false, ha]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd.BaseChange
