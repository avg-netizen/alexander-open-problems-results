import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambda
import Alexander313.Wilken.PublicEpsilonNativeRootPositiveCollapse
import Alexander313.Wilken.HereditaryNativeIotaEnclosureSupport

/-!
# Genuine same-value carrier and scalar bounds for full-domain iota

Every originally checked restricted tree has a checked Normal SAME-value
presentation at the actual beta context. LOW subtrees become genuine
uniform public parameters; retained positive indices keep their indices
and use the proved cardinal-suffix collapse equality. No selected endpoint,
translated presentation, Normality or collapse equality oracle occurs.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Enclosure

open ThetaCourse
open OrderSupport
open Iota.OrderInduction

/-- A same-value alpha presentation. This auxiliary map keeps every retained
theta index; its values are identified by the actual positive-level hulls. -/
def unshifted (q root : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode q (.parameter p))
  | .sum t u => cond (small q root (.sum t u))
      (.parameter (parameterCode q (.sum t u))) (.sum (unshifted q root t) (unshifted q root u))
  | .theta k t => cond (small q root (.theta k t))
      (.parameter (parameterCode q (.theta k t))) (.theta k (unshifted q root t))

theorem unshifted_below (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hb : denote (q) t < interpretation q root) :
    unshifted q root t = .parameter (parameterCode q t) := by
  have hs := (small_exact q root ha t ht).mpr hb
  cases t <;> simp only [unshifted, hs, Bool.cond_true]

theorem unshifted_theta_succ (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) (.theta (k + 1) t) = true)
    (hr : Restricted q root (.theta (k + 1) t)) :
    unshifted q root (.theta (k + 1) t) = .theta (k + 1) (unshifted q root t) := by
  have hf : small q root (.theta (k + 1) t) = false := by
    cases h : small q root (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hl := (small_iff_outerSort q root ha _ ht hr).mp h
      simp only [outerSort] at hl
      omega
  simp only [unshifted, hf, Bool.cond_false]

theorem unshifted_outerSort (q root : Nat) (t : RelativeTerm Nat) :
    (unshifted q root t).outerSort ≤ t.outerSort := by
  induction t with
  | parameter p => exact le_rfl
  | sum t u iht ihu =>
    cases h : small q root (.sum t u) <;>
      simp only [unshifted, h, Bool.cond_true, Bool.cond_false, outerSort] <;> omega
  | theta k t ih =>
    cases h : small q root (.theta k t) <;>
      simp only [unshifted, h, Bool.cond_true, Bool.cond_false, outerSort] <;> omega

/-- Original source checks and restriction alone derive the new admission. -/
theorem unshifted_checked (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true) (hr : Restricted q root t) :
    check (betaCode q root) (unshifted q root t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hb := restricted_low_below q root ha (.parameter p) ht hr (by exact Nat.zero_le _)
    have hp := (parameterCode_spec q root ha (.parameter p) ht hb).1
    simpa only [unshifted, check, betaCode_baseCheck q root ha,
      finiteCheck_parameter, hp, Bool.true_and]
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q root t u).mp hr
    cases h : small q root (.sum t u) with
    | true =>
      have hp := (parameterCode_spec q root ha (.sum t u) ht ((small_exact q root ha _ ht).mp h)).1
      simp only [unshifted, h, Bool.cond_true, check, betaCode_baseCheck q root ha,
        finiteCheck_parameter, hp, Bool.true_and]
    | false =>
      simp only [unshifted, h, Bool.cond_false]
      exact Iota.Inverse.checked_sum _ _ _ (iht hc.1 hs.1) (ihu hc.2 hs.2)
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero q root t).mp hr).1
      rw [unshifted_below q root ha _ ht hb]
      have hp := (parameterCode_spec q root ha (.theta 0 t) ht hb).1
      simp only [check, betaCode_baseCheck q root ha, finiteCheck_parameter, hp, Bool.true_and]
    | succ k =>
      rw [unshifted_theta_succ q root k ha t ht hr]
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ q root k t).mp hr
      have hf : finiteCheck (q) (SourceOne.PublicCodes.fragment (.theta (k + 1) t)) t = true ∧
          k + 1 < SourceOne.PublicCodes.fragment (.theta (k + 1) t) ∧ t.outerSort ≤ k + 1 + 2 := by
        simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
          (Bool.and_eq_true.mp ht).2
      exact RootPositiveCollapse.theta_checked _ (k + 1) _ (ih hc hs)
        ((unshifted_outerSort q root t).trans hf.2.2)

/-- Genuine same-value transport, with no collapse equality hypothesis. -/
theorem unshifted_value (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true) (hr : Restricted q root t) :
    denote (betaCode q root) (unshifted q root t) = denote (q) t := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    exact (parameterCode_spec q root ha (.parameter p) ht
      (restricted_low_below q root ha _ ht hr (by exact Nat.zero_le _))).2
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q root t u).mp hr
    cases h : small q root (.sum t u) with
    | true =>
      simpa only [unshifted, h, Bool.cond_true] using
        (parameterCode_spec q root ha (.sum t u) ht ((small_exact q root ha _ ht).mp h)).2
    | false =>
      simp only [unshifted, h, Bool.cond_false]
      change denote (betaCode q root) (unshifted q root t) + denote (betaCode q root) (unshifted q root u) =
        denote (q) t + denote (q) u
      rw [iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero q root t).mp hr).1
      rw [unshifted_below q root ha _ ht hb]
      exact (parameterCode_spec q root ha (.theta 0 t) ht hb).2
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ q root k t).mp hr
      have hu := unshifted_checked q root ha (.theta (k + 1) t) ht hr
      rw [unshifted_theta_succ q root k ha t ht hr] at hu ⊢
      change globalCollapse (base (betaCode q root)) (k + 1)
        (denote (betaCode q root) (unshifted q root t)) =
          globalCollapse (base q) (k + 1) (denote q t)
      rw [ih hc hs, beta_base q root ha]
      exact (RootPositiveCollapse.positive_collapse_eq q root (k + 1) ha
        (by omega) t hc ((denote_lt_iff_outerSort_le q t hc (k + 1 + 2)
          (by omega)).mp (FixedPoint.checked_theta_sort q (k + 1) t ht))).symm

theorem unshifted_normal (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) t = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t) :
    Comparison.Normal (betaCode q root) (unshifted q root t) := by
  revert ht hn hr
  induction t with
  | parameter p => intro ht hn hr; trivial
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum q root t u).mp hr
    cases h : small q root (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, Comparison.Normal]
    | false =>
      simp only [unshifted, h, Bool.cond_false, Comparison.Normal]
      refine ⟨iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2, ?_⟩
      change SourceNormalSum
        (denote (betaCode q root) (unshifted q root t) + denote (betaCode q root) (unshifted q root u))
        (denote (betaCode q root) (unshifted q root t)) (denote (betaCode q root) (unshifted q root u))
      rw [unshifted_value q root ha t hc.1 hs.1, unshifted_value q root ha u hc.2 hs.2]
      exact hn.2.2
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      rw [unshifted_below q root ha _ ht ((restricted_theta_zero q root t).mp hr).1]
      trivial
    | succ k =>
      rw [unshifted_theta_succ q root k ha t ht hr]
      exact ih (BaseTransformation.theta_argument_check _ (k + 1) t ht) hn
        ((restricted_theta_succ q root k t).mp hr)


theorem unshifted_theta_checked (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q (.theta k t) = true)
    (hr : Restricted q root t) :
    check (betaCode q root) (.theta k (unshifted q root t)) = true := by
  have hc := BaseTransformation.theta_argument_check q k t ht
  have hs := (denote_lt_iff_outerSort_le q t hc (k + 2) (by omega)).mp
    (FixedPoint.checked_theta_sort q k t ht)
  exact RootPositiveCollapse.theta_checked _ k _ (unshifted_checked q root ha t hc hr)
    ((unshifted_outerSort q root t).trans hs)

theorem unshifted_positive_theta_value (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q (.theta k t) = true)
    (hr : Restricted q root t) (hk : 0 < k) :
    denote (betaCode q root) (.theta k (unshifted q root t)) = denote q (.theta k t) := by
  have hc := BaseTransformation.theta_argument_check q k t ht
  change globalCollapse (base (betaCode q root)) k
    (denote (betaCode q root) (unshifted q root t)) = globalCollapse (base q) k (denote q t)
  rw [unshifted_value q root ha t hc hr, beta_base q root ha]
  exact (RootPositiveCollapse.positive_collapse_eq q root k ha hk t hc
    ((denote_lt_iff_outerSort_le q t hc (k + 2) (by omega)).mp
      (FixedPoint.checked_theta_sort q k t ht))).symm

/-- The same-value carrier has no exposed zero-family collapse. All source
zero nodes are stopped below beta, including every hidden argument. -/
theorem unshifted_exposed_zero (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hr : Restricted q root t) :
    exposedThetaList 0 (unshifted q root t) = [] := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hs := (restricted_sum q root t u).mp hr
    cases h : small q root (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, exposedThetaList]
    | false =>
      simp only [unshifted, h, Bool.cond_false, exposedThetaList,
        iht hc.1 hs.1, ihu hc.2 hs.2, List.nil_append]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [unshifted_below q root ha _ ht ((restricted_theta_zero q root t).mp hr).1]
      rfl
    | succ k =>
      rw [unshifted_theta_succ q root k ha t ht hr]
      simpa only [exposedThetaList, Nat.succ_ne_zero, if_false,
        Nat.zero_lt_succ, if_true] using
        ih (BaseTransformation.theta_argument_check q (k + 1) t ht)
          ((restricted_theta_succ q root k t).mp hr)

theorem low_transform_lt_theta (q root k : Nat) (ha : rootCheck q root = true)
    (x t : RelativeTerm Nat) (hx : check (q) x = true)
    (hrx : Restricted q root x) (hl : x.outerSort ≤ 1)
    (ht : check (betaCode q root) (.theta k t) = true) :
    denote (betaCode q root) (transform q root x) < denote (betaCode q root) (.theta k t) := by
  have hv : denote (betaCode q root) (transform q root x) < base (betaCode q root) := by
    rw [transform_low_value q root ha x hx hrx hl, beta_base q root ha]
    exact restricted_low_below q root ha x hx hrx hl
  exact hv.trans_le (((omegaSequence_strictMono (base (betaCode q root))).monotone
    (Nat.zero_le k)).trans (FixedPoint.checked_theta_range _ k t ht).1)

theorem shifted_theta_lt_positive_theta (q root j k : Nat) (ha : rootCheck q root = true)
    (u t : RelativeTerm Nat) (hu : check (q) (.theta (j + 1) u) = true)
    (hru : Restricted q root (.theta (j + 1) u)) (hjk : j + 1 ≤ k)
    (ht : check (betaCode q root) (.theta k t) = true) :
    denote (betaCode q root) (transform q root (.theta (j + 1) u)) <
      denote (betaCode q root) (.theta k t) := by
  have hc := transform_checked q root ha (.theta (j + 1) u) hu hru
  rw [transform_theta_succ q root j ha u hu hru] at hc ⊢
  exact (FixedPoint.checked_theta_range _ j _ hc).2.trans_le
    (((omegaSequence_strictMono (base (betaCode q root))).monotone hjk).trans
      (FixedPoint.checked_theta_range _ k t ht).1)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Enclosure
