import Alexander313.Wilken.HereditaryNativeIota

/-!
# Semantic cutoff and exposed-support shift for the actual iota transform

The source is the original positive public contextCode s, and alpha is the
actual admitted high theta-zero root. On the ORIGINAL restricted domain,
being below alpha is equivalent to having outer value sort at most one.
This is proved from the actual restriction and epsilon additive closure;
it is not an extra syntactic guard. The exposed theta support shifts exactly
one index, including hidden high arguments of low theta-zero nodes.

These source-only proof candidates have not been compiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota

open NativePublicBridge (contextCode contextCode_checked)

theorem alpha_base (s a : Nat) (ha : rootCheck s a = true) :
    base (alphaCode s a) = interpretation (contextCode s) a :=
  (alphaCode_spec s a ha).2

theorem root_additive (s a : Nat) (ha : rootCheck s a = true) :
    Ordinal.IsPrincipal (· + ·) (interpretation (contextCode s) a) := by
  rw [← alpha_base s a ha]
  exact BaseTransformation.base_additive _ (alphaCode_baseCheck s a ha)

theorem root_below_first_cardinal (s a : Nat) (ha : rootCheck s a = true) :
    interpretation (contextCode s) a < omegaSequence (base (contextCode s)) 1 := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact s a).mp ha
  rw [interpretation_code]
  exact (denote_lt_iff_outerSort_le _ (.theta 0 t) ht 1 (by omega)).mpr le_rfl

/-- Every low outer expression in the original restricted domain is below
alpha. Theta-zero arguments may have arbitrary admitted hidden height. -/
theorem restricted_low_below (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) (hl : t.outerSort ≤ 1) :
    denote (contextCode s) t < interpretation (contextCode s) a := by
  revert ht hr hl
  induction t with
  | parameter p =>
    intro ht hr hl
    have hp := checked_parameters _ (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact hp.2.trans_le (root_base_le s a ha)
  | sum t u iht ihu =>
    intro ht hr hl
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    have hlt : t.outerSort ≤ 1 := (le_max_left _ _).trans hl
    have hlu : u.outerSort ≤ 1 := (le_max_right _ _).trans hl
    exact root_additive s a ha (iht hc.1 hs.1 hlt) (ihu hc.2 hs.2 hlu)
  | theta k t ih =>
    intro ht hr hl
    have hk : k = 0 := by simp only [outerSort] at hl; omega
    subst k
    exact ((restricted_theta_zero s a t).mp hr).1

theorem restricted_below_iff_outerSort (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) :
    denote (contextCode s) t < interpretation (contextCode s) a ↔ t.outerSort ≤ 1 := by
  constructor
  · intro hs
    exact (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mp
      (hs.trans (root_below_first_cardinal s a ha))
  · exact restricted_low_below s a ha t ht hr

theorem small_iff_outerSort (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) : small s a t = true ↔ t.outerSort ≤ 1 :=
  (small_exact s a ha t ht).trans (restricted_below_iff_outerSort s a ha t ht hr)

theorem transform_low (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) (hl : t.outerSort ≤ 1) :
    transform s a t = .parameter (parameterCode s t) :=
  transform_below s a ha t ht (restricted_low_below s a ha t ht hr hl)

theorem transform_low_value (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) (hl : t.outerSort ≤ 1) :
    denote (alphaCode s a) (transform s a t) = denote (contextCode s) t :=
  (transform_parameter_value s a ha t ht (restricted_low_below s a ha t ht hr hl)).2

theorem transform_low_normal (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) (hl : t.outerSort ≤ 1) :
    Comparison.Normal (alphaCode s a) (transform s a t) := by
  rw [transform_low s a ha t ht hr hl]
  trivial

theorem transform_theta_succ (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hr : Restricted s a (.theta (k + 1) t)) :
    transform s a (.theta (k + 1) t) = .theta k (transform s a t) := by
  have hf : small s a (.theta (k + 1) t) = false := by
    cases h : small s a (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hs := (small_iff_outerSort s a ha _ ht hr).mp h
      simp only [outerSort] at hs
      omega
  simp only [transform, hf, Bool.cond_false, Nat.add_sub_cancel]

/-- A low outer expression exposes no theta at a positive index. Hidden
arguments of theta-zero nodes are correctly stopped by exposedThetaList. -/
theorem exposedThetaList_low (m : Nat) (hm : 0 < m) (t : RelativeTerm Nat)
    (ht : t.outerSort ≤ 1) : exposedThetaList m t = [] := by
  revert ht
  induction t with
  | parameter p => intro ht; rfl
  | sum t u iht ihu =>
    intro ht
    have hlt : t.outerSort ≤ 1 := (le_max_left _ _).trans ht
    have hlu : u.outerSort ≤ 1 := (le_max_right _ _).trans ht
    simp only [exposedThetaList, iht hlt, ihu hlu, List.nil_append]
  | theta k t ih =>
    intro ht
    have hk : k = 0 := by simp only [outerSort] at ht; omega
    subst k
    have he : (0 : Nat) ≠ m := by omega
    have hn : ¬m < 0 := by omega
    simp only [exposedThetaList, if_neg he, if_neg hn]

/-- Exact list transport of the support used by the actual collapse
comparison theorem. No order transport or collapse naturality is assumed. -/
theorem transform_exposedThetaList (s a m : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) :
    exposedThetaList m (transform s a t) =
      (exposedThetaList (m + 1) t).map (transform s a) := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
    | true =>
      have hl := (small_iff_outerSort s a ha _ ht hr).mp h
      rw [exposedThetaList_low (m + 1) (by omega) (.sum t u) hl]
      simp only [transform, h, Bool.cond_true, exposedThetaList, List.map_nil]
    | false =>
      simp only [transform, h, Bool.cond_false, exposedThetaList, List.map_append,
        iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [transform_low s a ha (.theta 0 t) ht hr le_rfl,
        exposedThetaList_low (m + 1) (by omega) (.theta 0 t) le_rfl]
      rfl
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ s a k t).mp hr
      rw [transform_theta_succ s a k ha t ht hr]
      by_cases he : k = m
      · subst k
        simp only [exposedThetaList, if_pos rfl, List.map_cons, List.map_nil,
          transform_theta_succ s a m ha t ht hr]
      · have he' : k + 1 ≠ m + 1 := by omega
        by_cases hm : m < k
        · have hm' : m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_pos hm, if_pos hm', ih hc hs]
        · have hm' : ¬m + 1 < k + 1 := by omega
          simp only [exposedThetaList, if_neg he, if_neg he', if_neg hm, if_neg hm', List.map_nil]

theorem transform_ge_base (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t)
    (hs : interpretation (contextCode s) a ≤ denote (contextCode s) t) :
    base (alphaCode s a) ≤ denote (alphaCode s a) (transform s a t) := by
  revert ht hr hs
  induction t with
  | parameter p =>
    intro ht hr hs
    have hlow := restricted_low_below s a ha (.parameter p) ht hr (by exact Nat.zero_le _)
    exact False.elim (hlow.not_ge hs)
  | sum t u iht ihu =>
    intro ht hr hs
    have hc := BaseTransformation.sum_checks _ t u ht
    have hr' := (restricted_sum s a t u).mp hr
    have hf : small s a (.sum t u) = false := by
      cases h : small s a (.sum t u) with
      | false => rfl
      | true => exact False.elim (((small_exact s a ha _ ht).mp h).not_ge hs)
    simp only [transform, hf, Bool.cond_false]
    change base (alphaCode s a) ≤
      denote (alphaCode s a) (transform s a t) + denote (alphaCode s a) (transform s a u)
    by_cases ht' : interpretation (contextCode s) a ≤ denote (contextCode s) t
    · exact (iht hc.1 hr'.1 ht').trans le_self_add
    · have hu' : interpretation (contextCode s) a ≤ denote (contextCode s) u := by
        by_contra hu'
        exact (root_additive s a ha (lt_of_not_ge ht') (lt_of_not_ge hu')).not_ge hs
      exact (ihu hc.2 hr'.2 hu').trans le_add_self
  | theta k t ih =>
    intro ht hr hs
    cases k with
    | zero => exact False.elim (((restricted_theta_zero s a t).mp hr).1.not_ge hs)
    | succ k =>
      have hct := transform_checked s a ha (.theta (k + 1) t) ht hr
      rw [transform_theta_succ s a k ha t ht hr] at hct ⊢
      exact BaseTransformation.theta_base_le _ k _ hct

theorem transform_below_base_iff (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) :
    denote (alphaCode s a) (transform s a t) < base (alphaCode s a) ↔
      denote (contextCode s) t < interpretation (contextCode s) a := by
  constructor
  · intro h
    by_contra hs
    exact h.not_ge (transform_ge_base s a ha t ht hr (le_of_not_gt hs))
  · intro h
    rw [(transform_parameter_value s a ha t ht h).2, alpha_base s a ha]
    exact h

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota
