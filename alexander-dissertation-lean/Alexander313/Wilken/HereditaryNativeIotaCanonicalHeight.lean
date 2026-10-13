import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeightSupport

/-!
# The printed same-alpha descent and actual inverse height bound

Every original restricted source expression has a genuinely admitted weak
normal SAME-VALUE presentation at alpha: atomize its low subtrees and retain
its positive theta indices. Positive-index collapse equality follows from
the actual hull/minimum recursion in the support module. Comparing the
literal iota output with this presentation proves the strict height descent
at alpha in Lemma 2.46(b), rather than a bound using source height.

The constructed inverse's LOW parameter heights are bounded by the source
height of alpha. Structural lifting and the real target normalizer then
prove the exact maximum in Lemma 2.46(c) for every original admitted target,
without a target Normal guard or a supplied inverse-height premise.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota

open NativePublicBridge (contextCode contextCode_checked)
open HeightSupport

/-- A same-value alpha presentation. This auxiliary map keeps every retained
theta index; its values are identified by the actual positive-level hulls. -/
def unshifted (s a : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode s (.parameter p))
  | .sum t u => cond (small s a (.sum t u))
      (.parameter (parameterCode s (.sum t u))) (.sum (unshifted s a t) (unshifted s a u))
  | .theta k t => cond (small s a (.theta k t))
      (.parameter (parameterCode s (.theta k t))) (.theta k (unshifted s a t))

theorem unshifted_below (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hb : denote (contextCode s) t < interpretation (contextCode s) a) :
    unshifted s a t = .parameter (parameterCode s t) := by
  have hs := (small_exact s a ha t ht).mpr hb
  cases t <;> simp only [unshifted, hs, Bool.cond_true]

theorem unshifted_theta_succ (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta (k + 1) t) = true)
    (hr : Restricted s a (.theta (k + 1) t)) :
    unshifted s a (.theta (k + 1) t) = .theta (k + 1) (unshifted s a t) := by
  have hf : small s a (.theta (k + 1) t) = false := by
    cases h : small s a (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hl := (small_iff_outerSort s a ha _ ht hr).mp h
      simp only [outerSort] at hl
      omega
  simp only [unshifted, hf, Bool.cond_false]

theorem unshifted_outerSort (s a : Nat) (t : RelativeTerm Nat) :
    (unshifted s a t).outerSort ≤ t.outerSort := by
  induction t with
  | parameter p => exact le_rfl
  | sum t u iht ihu =>
    cases h : small s a (.sum t u) <;>
      simp only [unshifted, h, Bool.cond_true, Bool.cond_false, outerSort] <;> omega
  | theta k t ih =>
    cases h : small s a (.theta k t) <;>
      simp only [unshifted, h, Bool.cond_true, Bool.cond_false, outerSort] <;> omega

/-- Original source checks and restriction alone derive the new admission. -/
theorem unshifted_checked (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    check (alphaCode s a) (unshifted s a t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hb := restricted_low_below s a ha (.parameter p) ht hr (by exact Nat.zero_le _)
    have hp := (parameterCode_spec s a ha (.parameter p) ht hb).1
    simpa only [unshifted, check, alphaCode_baseCheck s a ha,
      finiteCheck_parameter, hp, Bool.true_and]
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
    | true =>
      have hp := (parameterCode_spec s a ha (.sum t u) ht ((small_exact s a ha _ ht).mp h)).1
      simp only [unshifted, h, Bool.cond_true, check, alphaCode_baseCheck s a ha,
        finiteCheck_parameter, hp, Bool.true_and]
    | false =>
      simp only [unshifted, h, Bool.cond_false]
      exact Inverse.checked_sum _ _ _ (iht hc.1 hs.1) (ihu hc.2 hs.2)
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero s a t).mp hr).1
      rw [unshifted_below s a ha _ ht hb]
      have hp := (parameterCode_spec s a ha (.theta 0 t) ht hb).1
      simp only [check, alphaCode_baseCheck s a ha, finiteCheck_parameter, hp, Bool.true_and]
    | succ k =>
      rw [unshifted_theta_succ s a k ha t ht hr]
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ s a k t).mp hr
      have hf : finiteCheck (contextCode s) (SourceOne.PublicCodes.fragment (.theta (k + 1) t)) t = true ∧
          k + 1 < SourceOne.PublicCodes.fragment (.theta (k + 1) t) ∧ t.outerSort ≤ k + 1 + 2 := by
        simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
          (Bool.and_eq_true.mp ht).2
      exact Inverse.checked_theta _ (k + 1) _ (ih hc hs)
        ((unshifted_outerSort s a t).trans hf.2.2)

/-- Genuine same-value transport, with no collapse equality hypothesis. -/
theorem unshifted_value (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    denote (alphaCode s a) (unshifted s a t) = denote (contextCode s) t := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    exact (parameterCode_spec s a ha (.parameter p) ht
      (restricted_low_below s a ha _ ht hr (by exact Nat.zero_le _))).2
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
    | true =>
      simpa only [unshifted, h, Bool.cond_true] using
        (parameterCode_spec s a ha (.sum t u) ht ((small_exact s a ha _ ht).mp h)).2
    | false =>
      simp only [unshifted, h, Bool.cond_false]
      change denote (alphaCode s a) (unshifted s a t) + denote (alphaCode s a) (unshifted s a u) =
        denote (contextCode s) t + denote (contextCode s) u
      rw [iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero s a t).mp hr).1
      rw [unshifted_below s a ha _ ht hb]
      exact (parameterCode_spec s a ha (.theta 0 t) ht hb).2
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ s a k t).mp hr
      have hu := unshifted_checked s a ha (.theta (k + 1) t) ht hr
      rw [unshifted_theta_succ s a k ha t ht hr] at hu ⊢
      exact root_positive_theta_value s a (k + 1) ha t (unshifted s a t)
        (by omega) ht hu (ih hc hs)

theorem unshifted_normal (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    Comparison.Normal (alphaCode s a) (unshifted s a t) := by
  revert ht hn hr
  induction t with
  | parameter p => intro ht hn hr; trivial
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, Comparison.Normal]
    | false =>
      simp only [unshifted, h, Bool.cond_false, Comparison.Normal]
      refine ⟨iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2, ?_⟩
      change SourceNormalSum
        (denote (alphaCode s a) (unshifted s a t) + denote (alphaCode s a) (unshifted s a u))
        (denote (alphaCode s a) (unshifted s a t)) (denote (alphaCode s a) (unshifted s a u))
      rw [unshifted_value s a ha t hc.1 hs.1, unshifted_value s a ha u hc.2 hs.2]
      exact hn.2.2
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      rw [unshifted_below s a ha _ ht ((restricted_theta_zero s a t).mp hr).1]
      trivial
    | succ k =>
      rw [unshifted_theta_succ s a k ha t ht hr]
      exact ih (BaseTransformation.theta_argument_check _ (k + 1) t ht) hn
        ((restricted_theta_succ s a k t).mp hr)

/-- This bound compares two actual ALPHA presentations, rather than using
the original source presentation's height as a surrogate for ht_alpha. -/
theorem transform_height_le_unshifted (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true) (hr : Restricted s a t) :
    (transform s a t).height ≤ (unshifted s a t).height - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact le_rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    have hh := iht hc.1 hs.1
    have hh' := ihu hc.2 hs.2
    cases h : small s a (.sum t u) <;>
      simp only [transform, unshifted, h, Bool.cond_true, Bool.cond_false, height] <;> omega
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero s a t).mp hr).1
      rw [transform_below s a ha _ ht hb, unshifted_below s a ha _ ht hb]
      exact le_rfl
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ s a k t).mp hr
      have hh := ih hc hs
      rw [transform_theta_succ s a k ha t ht hr, unshifted_theta_succ s a k ha t ht hr]
      simp only [height]
      omega

theorem unshifted_spec (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    check (alphaCode s a) (unshifted s a t) = true ∧
      Comparison.Normal (alphaCode s a) (unshifted s a t) ∧
      denote (alphaCode s a) (unshifted s a t) = denote (contextCode s) t :=
  ⟨unshifted_checked s a ha t ht hr, unshifted_normal s a ha t ht hn hr,
    unshifted_value s a ha t ht hr⟩

theorem transform_canonical_height_lt (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t)
    (hb : interpretation (contextCode s) a < denote (contextCode s) t) :
    CanonicalHeight.canonicalHeightCode (alphaCode s a) (transform s a t).code <
      CanonicalHeight.canonicalHeightCode (alphaCode s a) (unshifted s a t).code := by
  have hu := unshifted_spec s a ha t ht hn hr
  have hh := transform_height_le_unshifted s a ha t ht hr
  have hp : 0 < (unshifted s a t).height := by
    by_contra h
    have hz : (unshifted s a t).height = 0 := by omega
    have hb' := (CanonicalHeight.canonicalHeightCode_zero_iff_below_base (alphaCode s a)
      (unshifted s a t).code (by simpa only [checkCode_code] using hu.1)).mp
      (by rw [canonical_height_normal _ _ hu.1 hu.2.1, hz])
    rw [interpretation_code, hu.2.2, alpha_base s a ha] at hb'
    exact hb.not_ge hb'.le
  rw [canonical_height_normal _ _ (transform_checked s a ha t ht hr)
      (transform_normal s a ha t ht hn hr), canonical_height_normal _ _ hu.1 hu.2.1]
  omega

/-- The right height is ht_alpha of the ORIGINAL value, independently of
which original admitted alpha code represents it. No normality guard on
that alpha representation is needed. -/
theorem transform_canonical_height_lt_representation (s a : Nat) (ha : rootCheck s a = true)
    (t u : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t)
    (hu : check (alphaCode s a) u = true)
    (hv : denote (alphaCode s a) u = denote (contextCode s) t)
    (hb : interpretation (contextCode s) a < denote (contextCode s) t) :
    CanonicalHeight.canonicalHeightCode (alphaCode s a) (transform s a t).code <
      CanonicalHeight.canonicalHeightCode (alphaCode s a) u.code := by
  have hs := unshifted_spec s a ha t ht hn hr
  have he := CanonicalHeight.canonicalHeightCode_invariant (alphaCode s a)
    (unshifted s a t).code u.code
    (by simpa only [checkCode_code] using hs.1) (by simpa only [checkCode_code] using hu)
    (by simpa only [interpretation_code] using hs.2.2.trans hv.symm)
  rw [← he]
  exact transform_canonical_height_lt s a ha t ht hn hr hb

/-- Lemma 2.46(b), including a constructed alpha representation of xi.
The original source-star domain and xi > alpha are the only source guards. -/
theorem source_lemma_2_46_b (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t)
    (hr : sourceStar (contextCode s) t < interpretation (contextCode s) a)
    (hb : interpretation (contextCode s) a < denote (contextCode s) t) :
    ∃ u : RelativeTerm Nat, check (alphaCode s a) u = true ∧
      Comparison.Normal (alphaCode s a) u ∧
      denote (alphaCode s a) u = denote (contextCode s) t ∧
      CanonicalHeight.canonicalHeightCode (alphaCode s a) (transform s a t).code <
        CanonicalHeight.canonicalHeightCode (alphaCode s a) u.code := by
  have hrt := (restricted_iff_sourceStar s a ha t ht hn).mpr hr
  have hu := unshifted_spec s a ha t ht hn hrt
  exact ⟨unshifted s a t, hu.1, hu.2.1, hu.2.2,
    transform_canonical_height_lt s a ha t ht hn hrt hb⟩

theorem literalCode_canonical_height_lt (s a c d : Nat)
    (hi : inputCheck s a c = true) (hd : checkCode (alphaCode s a) d = true)
    (hv : interpretation (alphaCode s a) d = interpretation (contextCode s) c)
    (hb : interpretation (contextCode s) a < interpretation (contextCode s) c) :
    CanonicalHeight.canonicalHeightCode (alphaCode s a) (literalCode s a c) <
      CanonicalHeight.canonicalHeightCode (alphaCode s a) d := by
  obtain ⟨ha, t, rfl, ht, hn, hr⟩ := (inputCheck_exact s a c).mp hi
  obtain ⟨u, he, hu⟩ := (checkCode_exact _ d).mp hd
  have hrt := (restricted_iff_sourceStar s a ha t ht hn).mpr hr
  have hh := transform_canonical_height_lt_representation s a ha t u ht hn hrt hu
    (by simpa only [← he, interpretation_code] using hv)
    (by simpa only [interpretation_code] using hb)
  simpa only [literalCode, hi, Bool.cond_true, stateCode_code, ← he] using hh

theorem inverse_lift_height (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    (Inverse.lift s t).height ≤
      max (CanonicalHeight.canonicalHeightCode (contextCode s) a) (t.height + 1) := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact (inverse_atom_height s a p ha (NativeContext.checked_admissible _ _ ht).1).trans
      (le_max_left _ _)
  | sum t u iht ihu =>
    intro ht
    have hc := BaseTransformation.sum_checks _ t u ht
    have hh := iht hc.1
    have hh' := ihu hc.2
    simp only [Inverse.lift, height]
    omega
  | theta k t ih =>
    intro ht
    have hh := ih (BaseTransformation.theta_argument_check _ k t ht)
    simp only [Inverse.lift, height]
    omega

/-- Exact Lemma 2.46(c) for the constructed semantic inverse, on ALL
original admitted target expressions, including nonnormal presentations. -/
theorem inverse_canonical_height_le (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    CanonicalHeight.canonicalHeightCode (contextCode s) (Inverse.inverse s a t).code ≤
      max (CanonicalHeight.canonicalHeightCode (contextCode s) a)
        (CanonicalHeight.canonicalHeightCode (alphaCode s a) t.code + 1) := by
  have hs := Inverse.inverse_spec s a ha t ht
  have hn := Normalization.normalize_checked (alphaCode s a) t ht
  have hh := inverse_lift_height s a ha _ hn.1
  have he : (Normalization.normalize (alphaCode s a) t).height =
      CanonicalHeight.canonicalHeightCode (alphaCode s a) t.code := by
    simp only [CanonicalHeight.canonicalHeightCode, Normalization.normalizeCode,
      checkCode_code, ht, Bool.cond_true, ThetaCourse.rawTree_code, heightCode_code]
  rw [canonical_height_normal _ _ hs.1 hs.2.1]
  simpa only [Inverse.inverse, he] using hh

theorem source_lemma_2_46_c (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true) :
    CanonicalHeight.canonicalHeightCode (contextCode s) (Inverse.inverse s a t).code ≤
      max (CanonicalHeight.canonicalHeightCode (contextCode s) a)
        (CanonicalHeight.canonicalHeightCode (alphaCode s a) t.code + 1) :=
  inverse_canonical_height_le s a ha t ht

theorem inverseCode_canonical_height_le (s a c : Nat)
    (hi : Inverse.inverseInput s a c = true) :
    CanonicalHeight.canonicalHeightCode (contextCode s) (Inverse.inverseCode s a c) ≤
      max (CanonicalHeight.canonicalHeightCode (contextCode s) a)
        (CanonicalHeight.canonicalHeightCode (alphaCode s a) c + 1) := by
  obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hi
  obtain ⟨t, he, ht⟩ := (checkCode_exact _ c).mp hc
  have hh := inverse_canonical_height_le s a ha t ht
  simpa only [Inverse.inverseCode, hi, Bool.cond_true, ← he, ThetaCourse.rawTree_code] using hh

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota
