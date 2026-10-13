import Alexander313.Wilken.PublicEpsilonNativeUnboundedRhoMu
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChange
import Alexander313.Wilken.HereditaryNativeSourceChiBaseChangeSupport

/-!
# Genuine common-root iota and inverse-pi callers for mu comparison

The lower root's full original restriction implies the upper root's
restriction. Both actual iota trees then agree literally: the original
source code, whole LOW stops and retained positive syntax are the same.
Actual upward admission constructs the inverse of pi on the lower mu
spelling. No inverse-iota theorem is substituted for inverse base change.
The high-part comparison needed by printed 3.10 is derived separately
from the real fine-predecessor interval. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.Support

open ThetaCourse OrderSupport

theorem restricted_mono (q lower upper : Nat) (t : RelativeTerm Nat)
    (hl : interpretation q lower ≤ interpretation q upper)
    (hr : Restricted q lower t) : Restricted q upper t :=
  fun x hx => (hr x hx).trans_le hl

/-- Literal equality on the original common source domain, including
whole LOW sums and every hidden theta-zero argument. -/
theorem transform_root_eq (q lower upper : Nat)
    (hl : rootCheck q lower = true) (hu : rootCheck q upper = true)
    (t : RelativeTerm Nat) (ht : check q t = true)
    (hrl : Restricted q lower t) (hru : Restricted q upper t) :
    transform q lower t = transform q upper t := by
  revert ht hrl hru
  induction t with
  | parameter p =>
    intro ht hrl hru
    rw [transform_low q lower hl _ ht hrl (Nat.zero_le _),
      transform_low q upper hu _ ht hru (Nat.zero_le _)]
  | sum t u iht ihu =>
    intro ht hrl hru
    have hc := BaseTransformation.sum_checks q t u ht
    have hls := (restricted_sum q lower t u).mp hrl
    have hus := (restricted_sum q upper t u).mp hru
    have he : small q lower (.sum t u) = small q upper (.sum t u) := by
      apply Bool.eq_iff_iff.mpr
      exact (small_iff_outerSort q lower hl _ ht hrl).trans
        (small_iff_outerSort q upper hu _ ht hru).symm
    cases hs : small q upper (.sum t u) with
    | true => simp only [transform, he, hs, Bool.cond_true]
    | false =>
      simp only [transform, he, hs, Bool.cond_false,
        iht hc.1 hls.1 hus.1, ihu hc.2 hls.2 hus.2]
  | theta k t ih =>
    intro ht hrl hru
    cases k with
    | zero =>
      rw [transform_low q lower hl _ ht hrl le_rfl,
        transform_low q upper hu _ ht hru le_rfl]
    | succ k =>
      rw [transform_theta_succ q lower k hl t ht hrl,
        transform_theta_succ q upper k hu t ht hru,
        ih (FixedPoint.checked_theta_argument q (k + 1) t ht)
          ((restricted_theta_succ q lower k t).mp hrl)
          ((restricted_theta_succ q upper k t).mp hru)]

theorem input_root_mono (q lower upper c : Nat)
    (hu : rootCheck q upper = true)
    (hl : interpretation q lower ≤ interpretation q upper)
    (hi : inputCheck q lower c = true) : inputCheck q upper c = true := by
  obtain ⟨ha, t, he, ht, hn, hs⟩ := (inputCheck_exact q lower c).mp hi
  have hr := (restricted_iff_sourceStar q lower ha t ht hn).mpr hs
  exact (inputCheck_exact q upper c).mpr ⟨hu, t, he, ht, hn,
    (restricted_iff_sourceStar q upper hu t ht hn).mp (restricted_mono q lower upper t hl hr)⟩

theorem literal_root_eq (q lower upper c : Nat)
    (hu : rootCheck q upper = true)
    (hl : interpretation q lower ≤ interpretation q upper)
    (hi : inputCheck q lower c = true) :
    literalCode q lower c = literalCode q upper c := by
  obtain ⟨ha, t, he, ht, hn, hs⟩ := (inputCheck_exact q lower c).mp hi
  have hr := (restricted_iff_sourceStar q lower ha t ht hn).mpr hs
  have hru := restricted_mono q lower upper t hl hr
  rw [he, literalCode_code q lower ha t ht hn hr,
    literalCode_code q upper hu t ht hn hru]
  exact congrArg RelativeTerm.code (transform_root_eq q lower upper ha hu t ht hr hru)

theorem low_larger (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base q ≤ base v) : lowCheckCode v c = true := by
  obtain ⟨t, he, ht⟩ := (lowCheckCode_exact q c).mp hc
  have hs := Bool.and_eq_true.mp ht
  have ht' := BaseTransformation.check_change q v t hs.1 hv
    (BaseTransformation.payloads_larger q v t hs.1 hv hl)
  rw [← he, lowCheckCode_code]
  exact Bool.and_eq_true.mpr ⟨ht', hs.2⟩

theorem accepted_larger (q v c : Nat) (hc : Comparison.acceptedCode q c = true)
    (hv : baseCheck v = true) (hl : base q ≤ base v) : Comparison.acceptedCode v c = true := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hs.1
  have ht' := BaseTransformation.check_change q v t ht hv
    (BaseTransformation.payloads_larger q v t ht hv hl)
  have hn : Comparison.Normal q t := by simpa only [← he, rawTree_code] using hs.2
  exact (Comparison.acceptedCode_exact v c).mpr
    ⟨by simpa only [← he, checkCode_code] using ht',
      by simpa only [← he, rawTree_code] using (BaseTransformation.normal_context q v t ht ht').mp hn⟩

/-- Every actual lower mu spelling is genuinely in the domain of pi
from the upper epsilon to the lower one. This constructs inverse-pi
provenance on its original code; no inverse representative is supplied. -/
theorem inverse_pi_caller (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper) :
    BaseTransformation.inputCheck (betaCode q upper) (betaCode q lower)
      (Mu.muCode q lower) = true := by
  apply BaseTransformation.target_preimage
  · exact betaCode_baseCheck q upper hu
  · simpa only [beta_base q lower hl, beta_base q upper hu] using hlt
  · exact ((Comparison.acceptedCode_exact _ _).mp (Mu.muCode_spec q lower hl).2.1).1

theorem inverse_pi_literal (q lower upper : Nat)
    (hl : Mu.inputCheck q lower = true) (hu : Mu.inputCheck q upper = true)
    (hlt : interpretation q lower < interpretation q upper) :
    Comparison.acceptedCode (betaCode q upper) (Mu.muCode q lower) = true ∧
      BaseTransformation.ParBounded (betaCode q upper) (betaCode q lower)
        (rawTree (Mu.muCode q lower)) ∧
      BaseTransformation.piCode (betaCode q upper) (betaCode q lower)
        (Mu.muCode q lower) = Mu.muCode q lower := by
  have hc := inverse_pi_caller q lower upper hl hu hlt
  exact ⟨accepted_larger _ _ _ (Mu.muCode_spec q lower hl).2.1
      (betaCode_baseCheck q upper hu) (by rw [beta_base q lower hl, beta_base q upper hu]; exact hlt.le),
    ((BaseTransformation.inputCheck_exact _ _ _).mp hc).2.2.2,
    BaseTransformation.piCode_eq _ _ _ hc⟩

/-- Actual zero-or-limit coefficients order lexicographically with their
finite offsets. The limit hypotheses are those proved by the real quotient. -/
theorem coefficient_order (lambda other : Ordinal.{0}) (k n : Nat)
    (hl : lambda = 0 ∨ IsSuccLimit lambda)
    (ho : other = 0 ∨ IsSuccLimit other)
    (he : lambda + (k : Ordinal.{0}) ≤ other + (n : Ordinal.{0})) :
    lambda < other ∨ lambda = other ∧ k ≤ n := by
  have hle : lambda ≤ other := by
    by_contra h
    have hh : other < lambda := lt_of_not_ge h
    rcases hl with hz | hlim
    · exact (hz ▸ hh).not_ge (bot_le)
    · exact (hlim.add_natCast_lt hh n).not_ge (le_self_add.trans he)
  rcases lt_or_eq_of_le hle with hh | hh
  · exact Or.inl hh
  · right
    refine ⟨hh, ?_⟩
    rw [hh, add_le_add_iff_left] at he
    exact Nat.cast_le.mp he

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.Support
