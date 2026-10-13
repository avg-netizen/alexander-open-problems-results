import Alexander313.Wilken.SourceOneNativeIotaCanonicalHeightSupport

/-!
# Printed source-one iota height clauses at the actual alpha base

The unshifted map constructs a genuine SAME-VALUE Normal alpha presentation
by retaining positive theta indices and atomizing only original subtrees
below alpha. Positive-family identity follows from the actual finite hull
recursion. Thus the strict descent compares ht_alpha of the ORIGINAL value,
not a source-one height surrogate. Every inverse atom has original height
bounded by the original alpha height; the genuine target normalizer and
structural lift prove the exact maximum bound for every admitted target.
No height, representative, caller or collapse agreement oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota

open OrderSupport HeightSupport
open NativeContext.Iota.HeightSupport (canonical_height_normal)

def unshifted (a : Nat) : RelativeTerm Nat → RelativeTerm Nat
  | .parameter p => .parameter (parameterCode (.parameter p))
  | .sum t u => cond (small a (.sum t u)) (.parameter (parameterCode (.sum t u)))
      (.sum (unshifted a t) (unshifted a u))
  | .theta k t => cond (small a (.theta k t)) (.parameter (parameterCode (.theta k t)))
      (.theta k (unshifted a t))

theorem unshifted_below (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hb : denote 0 t < interpretation 0 a) :
    unshifted a t = .parameter (parameterCode t) := by
  have hs := (small_exact a ha t ht).mpr hb
  cases t <;> simp only [unshifted, hs, Bool.cond_true]

theorem unshifted_theta_succ (a k : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 (.theta (k + 1) t) = true) (hr : Restricted a (.theta (k + 1) t)) :
    unshifted a (.theta (k + 1) t) = .theta (k + 1) (unshifted a t) := by
  have hf : small a (.theta (k + 1) t) = false := by
    cases h : small a (.theta (k + 1) t) with
    | false => rfl
    | true =>
      have hl := (small_iff_outerSort a ha _ ht hr).mp h
      simp only [RelativeTerm.outerSort] at hl
      omega
  simp only [unshifted, hf, Bool.cond_false]

theorem unshifted_outerSort (a : Nat) (t : RelativeTerm Nat) :
    (unshifted a t).outerSort ≤ t.outerSort := by
  induction t with
  | parameter p => exact le_rfl
  | sum t u iht ihu =>
    cases h : small a (.sum t u) <;>
      simp only [unshifted, h, Bool.cond_true, Bool.cond_false, RelativeTerm.outerSort] <;> omega
  | theta k t ih =>
    cases h : small a (.theta k t) <;>
      simp only [unshifted, h, Bool.cond_true, Bool.cond_false, RelativeTerm.outerSort] <;> omega

theorem unshifted_checked (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    NativeContext.check (alphaCode a) (unshifted a t) = true := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hb := restricted_low_below a ha (.parameter p) ht hr (Nat.zero_le _)
    have hp := (parameterCode_spec a ha (.parameter p) ht hb).1
    simpa only [unshifted, NativeContext.check, alphaCode_baseCheck a ha,
      NativeContext.finiteCheck_parameter, hp, Bool.true_and]
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true =>
      have hp := (parameterCode_spec a ha (.sum t u) ht ((small_exact a ha _ ht).mp h)).1
      simp only [unshifted, h, Bool.cond_true, NativeContext.check, alphaCode_baseCheck a ha,
        NativeContext.finiteCheck_parameter, hp, Bool.true_and]
    | false =>
      simp only [unshifted, h, Bool.cond_false]
      exact NativeContext.Iota.Inverse.checked_sum _ _ _ (iht hc.1 hs.1) (ihu hc.2 hs.2)
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero a t).mp hr).1
      rw [unshifted_below a ha _ ht hb]
      have hp := (parameterCode_spec a ha (.theta 0 t) ht hb).1
      simp only [NativeContext.check, alphaCode_baseCheck a ha,
        NativeContext.finiteCheck_parameter, hp, Bool.true_and]
    | succ k =>
      rw [unshifted_theta_succ a k ha t ht hr]
      have hc := argument_checked (k + 1) t ht
      have hs := (restricted_theta_succ a k t).mp hr
      have hf : finiteCheck 0 (SourceOne.PublicCodes.fragment (.theta (k + 1) t)) t = true ∧
          k + 1 < SourceOne.PublicCodes.fragment (.theta (k + 1) t) ∧ t.outerSort ≤ k + 1 + 2 := by
        simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
      exact NativeContext.Iota.Inverse.checked_theta _ (k + 1) _ (ih hc hs)
        ((unshifted_outerSort a t).trans hf.2.2)

theorem unshifted_value (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    NativeContext.denote (alphaCode a) (unshifted a t) = denote 0 t := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    exact (parameterCode_spec a ha (.parameter p) ht
      (restricted_low_below a ha _ ht hr (Nat.zero_le _))).2
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true =>
      simpa only [unshifted, h, Bool.cond_true] using
        (parameterCode_spec a ha (.sum t u) ht ((small_exact a ha _ ht).mp h)).2
    | false =>
      simp only [unshifted, h, Bool.cond_false]
      change NativeContext.denote (alphaCode a) (unshifted a t) +
        NativeContext.denote (alphaCode a) (unshifted a u) = denote 0 t + denote 0 u
      rw [iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero a t).mp hr).1
      rw [unshifted_below a ha _ ht hb]
      exact (parameterCode_spec a ha (.theta 0 t) ht hb).2
    | succ k =>
      have hc := argument_checked (k + 1) t ht
      have hs := (restricted_theta_succ a k t).mp hr
      have hu := unshifted_checked a ha (.theta (k + 1) t) ht hr
      rw [unshifted_theta_succ a k ha t ht hr] at hu ⊢
      exact root_positive_theta_value a (k + 1) ha t (unshifted a t) (by omega) ht hu (ih hc hs)

theorem unshifted_normal (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    NativeContext.Comparison.Normal (alphaCode a) (unshifted a t) := by
  revert ht hn hr
  induction t with
  | parameter p => intro ht hn hr; trivial
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, NativeContext.Comparison.Normal]
    | false =>
      simp only [unshifted, h, Bool.cond_false, NativeContext.Comparison.Normal]
      refine ⟨iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2, ?_⟩
      change SourceNormalSum
        (NativeContext.denote (alphaCode a) (unshifted a t) + NativeContext.denote (alphaCode a) (unshifted a u))
        (NativeContext.denote (alphaCode a) (unshifted a t)) (NativeContext.denote (alphaCode a) (unshifted a u))
      rw [unshifted_value a ha t hc.1 hs.1, unshifted_value a ha u hc.2 hs.2]
      exact hn.2.2
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      rw [unshifted_below a ha _ ht ((restricted_theta_zero a t).mp hr).1]
      trivial
    | succ k =>
      rw [unshifted_theta_succ a k ha t ht hr]
      exact ih (argument_checked (k + 1) t ht) hn ((restricted_theta_succ a k t).mp hr)

theorem transform_height_le_unshifted (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    (transform a t).height ≤ (unshifted a t).height - 1 := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; exact le_rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    have hh := iht hc.1 hs.1
    have hh' := ihu hc.2 hs.2
    cases h : small a (.sum t u) <;>
      simp only [transform, unshifted, h, Bool.cond_true, Bool.cond_false, RelativeTerm.height] <;> omega
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      have hb := ((restricted_theta_zero a t).mp hr).1
      rw [transform_below a ha _ ht hb, unshifted_below a ha _ ht hb]
      exact le_rfl
    | succ k =>
      have hc := argument_checked (k + 1) t ht
      have hs := (restricted_theta_succ a k t).mp hr
      have hh := ih hc hs
      rw [transform_theta_succ a k ha t ht hr, unshifted_theta_succ a k ha t ht hr]
      simp only [RelativeTerm.height]
      omega

theorem unshifted_spec (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    NativeContext.check (alphaCode a) (unshifted a t) = true ∧
      NativeContext.Comparison.Normal (alphaCode a) (unshifted a t) ∧
      NativeContext.denote (alphaCode a) (unshifted a t) = denote 0 t :=
  ⟨unshifted_checked a ha t ht hr, unshifted_normal a ha t ht hn hr, unshifted_value a ha t ht hr⟩

theorem transform_canonical_height_lt (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t)
    (hb : interpretation 0 a < denote 0 t) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (transform a t).code <
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (unshifted a t).code := by
  have hu := unshifted_spec a ha t ht hn hr
  have hh := transform_height_le_unshifted a ha t ht hr
  have hp : 0 < (unshifted a t).height := by
    by_contra h
    have hz : (unshifted a t).height = 0 := by omega
    have hb' := (NativeContext.CanonicalHeight.canonicalHeightCode_zero_iff_below_base (alphaCode a)
      (unshifted a t).code (by simpa only [NativeContext.checkCode_code] using hu.1)).mp
      (by rw [canonical_height_normal _ _ hu.1 hu.2.1, hz])
    rw [NativeContext.interpretation_code, hu.2.2, alpha_base a ha] at hb'
    exact hb.not_ge hb'.le
  rw [canonical_height_normal _ _ (transform_checked a ha t ht hr) (transform_normal a ha t ht hn hr),
    canonical_height_normal _ _ hu.1 hu.2.1]
  omega

theorem transform_canonical_height_lt_representation (a : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : Restricted a t)
    (hu : NativeContext.check (alphaCode a) u = true)
    (hv : NativeContext.denote (alphaCode a) u = denote 0 t) (hb : interpretation 0 a < denote 0 t) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (transform a t).code <
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) u.code := by
  have hs := unshifted_spec a ha t ht hn hr
  have he := NativeContext.CanonicalHeight.canonicalHeightCode_invariant (alphaCode a)
    (unshifted a t).code u.code (by simpa only [NativeContext.checkCode_code] using hs.1)
    (by simpa only [NativeContext.checkCode_code] using hu)
    (by simpa only [NativeContext.interpretation_code] using hs.2.2.trans hv.symm)
  rw [← he]
  exact transform_canonical_height_lt a ha t ht hn hr hb

theorem source_lemma_2_46_b (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hr : sourceStar t < interpretation 0 a)
    (hb : interpretation 0 a < denote 0 t) :
    ∃ u : RelativeTerm Nat, NativeContext.check (alphaCode a) u = true ∧
      NativeContext.Comparison.Normal (alphaCode a) u ∧ NativeContext.denote (alphaCode a) u = denote 0 t ∧
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (transform a t).code <
        NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) u.code := by
  have hrt := (restricted_iff_sourceStar a ha t ht hn).mpr hr
  have hu := unshifted_spec a ha t ht hn hrt
  exact ⟨unshifted a t, hu.1, hu.2.1, hu.2.2, transform_canonical_height_lt a ha t ht hn hrt hb⟩

theorem literalCode_canonical_height_lt (a c d : Nat) (hi : inputCheck a c = true)
    (hd : NativeContext.checkCode (alphaCode a) d = true)
    (hv : NativeContext.interpretation (alphaCode a) d = interpretation 0 c)
    (hb : interpretation 0 a < interpretation 0 c) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (literalCode a c) <
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) d := by
  obtain ⟨ha, t, rfl, ht, hn, hr⟩ := (inputCheck_exact a c).mp hi
  obtain ⟨u, he, hu⟩ := (NativeContext.checkCode_exact _ d).mp hd
  have hrt := (restricted_iff_sourceStar a ha t ht hn).mpr hr
  have hh := transform_canonical_height_lt_representation a ha t u ht hn hrt hu
    (by simpa only [← he, NativeContext.interpretation_code, interpretation_code] using hv)
    (by simpa only [interpretation_code] using hb)
  simpa only [literalCode, hi, Bool.cond_true, stateCode_code, ← he] using hh

theorem inverse_lift_height (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) :
    (Inverse.lift t).height ≤ max (SourceOne.CanonicalHeight.canonicalHeightCode a) (t.height + 1) := by
  revert ht
  induction t with
  | parameter p =>
    intro ht
    exact (inverse_atom_height a p ha (NativeContext.checked_admissible _ _ ht).1).trans (le_max_left _ _)
  | sum t u iht ihu =>
    intro ht
    have hc := NativeContext.BaseTransformation.sum_checks _ t u ht
    have hh := iht hc.1
    have hh' := ihu hc.2
    simp only [Inverse.lift, RelativeTerm.height]
    omega
  | theta k t ih =>
    intro ht
    have hh := ih (NativeContext.BaseTransformation.theta_argument_check _ k t ht)
    simp only [Inverse.lift, RelativeTerm.height]
    omega

theorem inverse_canonical_height_le (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) :
    SourceOne.CanonicalHeight.canonicalHeightCode (Inverse.inverse a t).code ≤
      max (SourceOne.CanonicalHeight.canonicalHeightCode a)
        (NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) t.code + 1) := by
  have hs := Inverse.inverse_spec a ha t ht
  have hn := NativeContext.Normalization.normalize_checked (alphaCode a) t ht
  have hh := inverse_lift_height a ha _ hn.1
  have he : (NativeContext.Normalization.normalize (alphaCode a) t).height =
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) t.code := by
    simp only [NativeContext.CanonicalHeight.canonicalHeightCode, NativeContext.Normalization.normalizeCode,
      NativeContext.checkCode_code, ht, Bool.cond_true, ThetaCourse.rawTree_code, heightCode_code]
  rw [source_canonical_height_normal _ hs.1 hs.2.1]
  simpa only [Inverse.inverse, he] using hh

theorem source_lemma_2_46_c (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : NativeContext.check (alphaCode a) t = true) :
    SourceOne.CanonicalHeight.canonicalHeightCode (Inverse.inverse a t).code ≤
      max (SourceOne.CanonicalHeight.canonicalHeightCode a)
        (NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) t.code + 1) :=
  inverse_canonical_height_le a ha t ht

theorem inverseCode_canonical_height_le (a c : Nat) (hi : Inverse.inverseInput a c = true) :
    SourceOne.CanonicalHeight.canonicalHeightCode (Inverse.inverseCode a c) ≤
      max (SourceOne.CanonicalHeight.canonicalHeightCode a)
        (NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) c + 1) := by
  obtain ⟨ha, hc⟩ := Bool.and_eq_true.mp hi
  obtain ⟨t, he, ht⟩ := (NativeContext.checkCode_exact _ c).mp hc
  have hh := inverse_canonical_height_le a ha t ht
  simpa only [Inverse.inverseCode, hi, Bool.cond_true, ← he, ThetaCourse.rawTree_code] using hh

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota
