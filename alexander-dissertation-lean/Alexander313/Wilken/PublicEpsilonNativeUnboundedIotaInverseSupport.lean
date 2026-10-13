import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaOrderInduction
import Alexander313.Wilken.HereditaryNativeIotaInverseSupport
import Alexander313.Wilken.HereditaryNativeNormalization

/-!
# Genuine original-domain inverse witnesses at every literal epsilon

The actual source LOW coverage below its genuine global boundary supplies
all target parameter values below the original beta root. Real source
normalization makes those representatives weak Normal; their full hidden
support is bounded by the real LOW principal-support theorem. A raised-index
lift therefore has original source admission and full beta restriction,
with a genuine semantic right inverse on every checked target tree.
No source representative, inverse or admission oracle is supplied. The
semantic witnesses are noncomputable choices; the companion module proves
termination of an actual computable least-code inverse search instead of
asserting primitive recursion for this choice-based lift. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Inverse

open OrderSupport
open Iota.Inverse (checked_sum checked_theta fullList_value_le_low)

/-- Every actual target payload has a genuine originally admitted Normal
LOW source representative at its SAME value, derived from actual coverage. -/
theorem atom_exists (q root p : Nat) (ha : rootCheck q root = true)
    (hp : parameterCheck (betaCode q root) p = true) :
    ∃ t : RelativeTerm Nat, check q t = true ∧ Comparison.Normal q t ∧
      t.outerSort ≤ 1 ∧ denote q t = parameters p := by
  have hq := source_checked q root ha
  have hpb : parameters p < interpretation q root := by
    simpa only [beta_base q root ha] using parameter_sound (betaCode q root) p hp
  have hboundary := checked_low_bound q root (root_low q root ha)
  obtain ⟨u, hu, hv⟩ := (lt_boundary_iff_checked q hq (parameters p)).mp
    (hpb.trans hboundary)
  have hc := (Bool.and_eq_true.mp hu).1
  have hn := Normalization.normalize_checked q u hc
  have hvalue : denote q (Normalization.normalize q u) = parameters p := hn.2.2.trans hv
  have hsort : (Normalization.normalize q u).outerSort ≤ 1 := by
    apply (denote_lt_iff_outerSort_le q _ hn.1 1 (by omega)).mp
    rw [hvalue]
    exact hpb.trans (root_below_first_cardinal q root ha)
  exact ⟨Normalization.normalize q u, hn.1, hn.2.1, hsort, hvalue⟩

noncomputable def atomTerm (q root p : Nat) : RelativeTerm Nat :=
  if h : rootCheck q root = true ∧ parameterCheck (betaCode q root) p = true then
    Classical.choose (atom_exists q root p h.1 h.2)
  else Normalization.zeroTree

theorem atom_spec (q root p : Nat) (ha : rootCheck q root = true)
    (hp : parameterCheck (betaCode q root) p = true) :
    check q (atomTerm q root p) = true ∧ Comparison.Normal q (atomTerm q root p) ∧
      (atomTerm q root p).outerSort ≤ 1 ∧ denote q (atomTerm q root p) = parameters p := by
  simp only [atomTerm, dif_pos (And.intro ha hp)]
  exact Classical.choose_spec (atom_exists q root p ha hp)

theorem atom_restricted (q root p : Nat) (ha : rootCheck q root = true)
    (hp : parameterCheck (betaCode q root) p = true) : Restricted q root (atomTerm q root p) := by
  have hs := atom_spec q root p ha hp
  intro u hu
  have hle := fullList_value_le_low q _ u hs.1 hs.2.1 hs.2.2.1 hu
  rw [hs.2.2.2] at hle
  exact hle.trans_lt (by simpa only [beta_base q root ha] using parameter_sound _ p hp)

noncomputable def lift (q root : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => atomTerm q root p
  | .sum t u => .sum (lift q root t) (lift q root u)
  | .theta k t => .theta (k + 1) (lift q root t)

theorem lift_outerSort (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) :
    (lift q root t).outerSort ≤ t.outerSort + 1 := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact (atom_spec q root p ha (NativeContext.checked_admissible _ _ ht).1).2.2.1
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    have hlt := iht hc.1
    have hlu := ihu hc.2
    simp only [lift, outerSort]
    omega
  | theta k t ih => intro ht; simp only [lift, outerSort]; omega

theorem lift_checked (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) :
    check q (lift q root t) = true := by
  revert ht
  induction t with
  | parameter p => intro ht; exact (atom_spec q root p ha (NativeContext.checked_admissible _ _ ht).1).1
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    exact checked_sum _ _ _ (iht hc.1) (ihu hc.2)
  | theta k t ih =>
    intro ht
    have hc := BaseTransformation.theta_argument_check _ k t ht
    have hf := (Bool.and_eq_true.mp ht).2
    have hs : finiteCheck (betaCode q root) (SourceOne.PublicCodes.fragment (.theta k t)) t = true ∧
        k < SourceOne.PublicCodes.fragment (.theta k t) ∧ t.outerSort ≤ k + 2 := by
      simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hf
    apply checked_theta _ (k + 1) _ (ih hc)
    have hl := lift_outerSort q root ha t hc
    have hsort := hs.2.2
    omega

theorem lift_restricted (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) : Restricted q root (lift q root t) := by
  revert ht
  induction t with
  | parameter p => intro ht; exact atom_restricted q root p ha (NativeContext.checked_admissible _ _ ht).1
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    exact (restricted_sum q root _ _).mpr ⟨iht hc.1, ihu hc.2⟩
  | theta k t ih =>
    intro ht
    exact (restricted_theta_succ q root k _).mpr
      (ih (BaseTransformation.theta_argument_check _ k t ht))

/-- Actual target value recovery already holds on every originally admitted
target expression; no target Normality is required. -/
theorem lift_right_inverse (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q root) t = true) :
    denote (betaCode q root) (transform q root (lift q root t)) = denote (betaCode q root) t := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    have hp := (NativeContext.checked_admissible _ _ ht).1
    have hs := atom_spec q root p ha hp
    have hb : denote q (atomTerm q root p) < interpretation q root := by
      rw [hs.2.2.2]
      simpa only [beta_base q root ha] using parameter_sound _ p hp
    exact ((transform_parameter_value q root ha _ hs.1 hb).2).trans hs.2.2.2
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    rw [lift, transform_add q root ha _ _ (lift_checked q root ha t hc.1)
      (lift_checked q root ha u hc.2), iht hc.1, ihu hc.2]
    rfl
  | theta k t ih =>
    intro ht
    have hc := BaseTransformation.theta_argument_check _ k t ht
    have hs := lift_checked q root ha (.theta k t) ht
    have hr := lift_restricted q root ha (.theta k t) ht
    rw [lift, transform_theta_succ q root k ha _ hs hr]
    change globalCollapse (base (betaCode q root)) k
      (denote (betaCode q root) (transform q root (lift q root t))) =
      globalCollapse (base (betaCode q root)) k (denote (betaCode q root) t)
    rw [ih hc]


end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Inverse
