import Alexander313.Wilken.SourceOneNativeRhoMu
import Alexander313.Wilken.PublicEpsilonNativeMuInverseBaseChangeSupport
import Alexander313.Wilken.HereditaryFineLocalizationOrderSupport

/-!
# Original source-one common iota and genuine inverse-pi spelling

All source syntax uses original check0 and Theta.Normal0. Actual source-one
LOW stops are independent of the epsilon root, so the two genuine iota
outputs coincide literally on their common original restricted domain.
Native admission is used only at the actual lower and upper epsilon target
bases. Actual upward admission constructs the inverse of pi on the lower
mu spelling; no inverse-iota, Native base-one or provenance oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MuInverseBaseChange.Support

open OrderSupport
open NativeContext.PublicEpsilonUnboundedIota.MuInverseBaseChange.Support
  (low_larger accepted_larger coefficient_order)

theorem restricted_mono (lower upper : Nat) (t : RelativeTerm Nat)
    (hl : interpretation 0 lower ≤ interpretation 0 upper)
    (hr : Restricted lower t) : Restricted upper t :=
  fun x hx => (hr x hx).trans_le hl

theorem transform_root_eq (lower upper : Nat)
    (hl : rootCheck lower = true) (hu : rootCheck upper = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true)
    (hrl : Restricted lower t) (hru : Restricted upper t) :
    transform lower t = transform upper t := by
  revert ht hrl hru
  induction t with
  | parameter p =>
    intro ht hrl hru
    rw [transform_low lower hl _ ht hrl (Nat.zero_le _),
      transform_low upper hu _ ht hru (Nat.zero_le _)]
  | sum t u iht ihu =>
    intro ht hrl hru
    have hc := sum_checks t u ht
    have hls := (restricted_sum lower t u).mp hrl
    have hus := (restricted_sum upper t u).mp hru
    have he : small lower (.sum t u) = small upper (.sum t u) := by
      apply Bool.eq_iff_iff.mpr
      exact (small_iff_outerSort lower hl _ ht hrl).trans
        (small_iff_outerSort upper hu _ ht hru).symm
    cases hs : small upper (.sum t u) with
    | true => simp only [transform, he, hs, Bool.cond_true]
    | false =>
      simp only [transform, he, hs, Bool.cond_false,
        iht hc.1 hls.1 hus.1, ihu hc.2 hls.2 hus.2]
  | theta k t ih =>
    intro ht hrl hru
    cases k with
    | zero =>
      rw [transform_low lower hl _ ht hrl le_rfl,
        transform_low upper hu _ ht hru le_rfl]
    | succ k =>
      rw [transform_theta_succ lower k hl t ht hrl,
        transform_theta_succ upper k hu t ht hru,
        ih (argument_checked (k + 1) t ht)
          ((restricted_theta_succ lower k t).mp hrl)
          ((restricted_theta_succ upper k t).mp hru)]

theorem input_root_mono (lower upper c : Nat) (hu : rootCheck upper = true)
    (hl : interpretation 0 lower ≤ interpretation 0 upper)
    (hi : inputCheck lower c = true) : inputCheck upper c = true := by
  obtain ⟨ha, t, he, ht, hn, hs⟩ := (inputCheck_exact lower c).mp hi
  have hr := (restricted_iff_sourceStar lower ha t ht hn).mpr hs
  exact (inputCheck_exact upper c).mpr ⟨hu, t, he, ht, hn,
    (restricted_iff_sourceStar upper hu t ht hn).mp (restricted_mono lower upper t hl hr)⟩

theorem literal_root_eq (lower upper c : Nat) (hu : rootCheck upper = true)
    (hl : interpretation 0 lower ≤ interpretation 0 upper)
    (hi : inputCheck lower c = true) : literalCode lower c = literalCode upper c := by
  obtain ⟨ha, t, he, ht, hn, hs⟩ := (inputCheck_exact lower c).mp hi
  have hr := (restricted_iff_sourceStar lower ha t ht hn).mpr hs
  have hru := restricted_mono lower upper t hl hr
  rw [he, literalCode_code lower ha t ht hn hr, literalCode_code upper hu t ht hn hru]
  exact congrArg RelativeTerm.code (transform_root_eq lower upper ha hu t ht hr hru)

/-- Equality of original source values reflects through actual source-one
literal iota on its genuine original domain. -/
theorem literal_value_eq (root c d : Nat) (hc : inputCheck root c = true)
    (hd : inputCheck root d = true) (hv : interpretation 0 c = interpretation 0 d) :
    NativeContext.interpretation (alphaCode root) (literalCode root c) =
      NativeContext.interpretation (alphaCode root) (literalCode root d) := by
  apply le_antisymm
  · apply le_of_not_gt
    intro h
    exact hv.not_gt ((literalCode_lt_iff root d c hd hc).mp h)
  · apply le_of_not_gt
    intro h
    exact hv.not_lt ((literalCode_lt_iff root c d hc hd).mp h)

theorem inverse_pi_caller (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper) :
    NativeContext.BaseTransformation.inputCheck (alphaCode upper) (alphaCode lower)
      (Mu.muCode lower) = true := by
  apply NativeContext.BaseTransformation.target_preimage
  · exact alphaCode_baseCheck upper hu
  · simpa only [alpha_base lower hl, alpha_base upper hu] using hlt
  · exact ((NativeContext.Comparison.acceptedCode_exact _ _).mp (Mu.muCode_spec lower hl).2.1).1

theorem inverse_pi_literal (lower upper : Nat)
    (hl : Mu.inputCheck lower = true) (hu : Mu.inputCheck upper = true)
    (hlt : interpretation 0 lower < interpretation 0 upper) :
    NativeContext.Comparison.acceptedCode (alphaCode upper) (Mu.muCode lower) = true ∧
      NativeContext.BaseTransformation.ParBounded (alphaCode upper) (alphaCode lower)
        (ThetaCourse.rawTree (Mu.muCode lower)) ∧
      NativeContext.BaseTransformation.piCode (alphaCode upper) (alphaCode lower)
        (Mu.muCode lower) = Mu.muCode lower := by
  have hc := inverse_pi_caller lower upper hl hu hlt
  exact ⟨accepted_larger _ _ _ (Mu.muCode_spec lower hl).2.1
      (alphaCode_baseCheck upper hu) (by rw [alpha_base lower hl, alpha_base upper hu]; exact hlt.le),
    ((NativeContext.BaseTransformation.inputCheck_exact _ _ _).mp hc).2.2.2,
    NativeContext.BaseTransformation.piCode_eq _ _ _ hc⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.MuInverseBaseChange.Support
