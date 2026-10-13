import Alexander313.Wilken.HereditaryNativeIota
import Alexander313.Wilken.HereditaryNativeBaseTransformation

/-!
# The original restricted-domain gap for iota base change

Both roots belong to the SAME positive public source context. On the original
gamma restriction, an admitted subtree is either below gamma or at least the
source Omega1. Parameters and theta0 nodes give the first alternative; higher
theta nodes give the second; epsilon addition closes the first alternative.
Thus the actual original comparators below gamma and alpha agree. The public
parameterCode depends only on the source and the original subtree. Every
atomized subtree consequently supplies its real parameter bound below gamma.
This derives target payloads and the atomic-stop Par bound for pi, without
assuming target admission, presentation invariance or Lemma 2.46.
All candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange

open NativePublicBridge (contextCode contextCode_checked)

theorem rootBelowBoundary (s a : Nat) (ha : rootCheck s a = true) :
    interpretation (contextCode s) a < omegaSequence (base (contextCode s)) 1 := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact s a).mp ha
  rw [interpretation_code]
  exact (denote_lt_iff_outerSort_le _ _ ht 1 (Nat.succ_pos 0)).mpr (by
    simp only [RelativeTerm.outerSort]; omega)

theorem restricted_mono (s g a : Nat)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (hr : Restricted s g t) : Restricted s a t :=
  fun u hu => (hr u hu).trans hga

theorem restricted_argument (s g k : Nat) (t : RelativeTerm Nat)
    (hr : Restricted s g (.theta k t)) : Restricted s g t := by
  cases k with
  | zero => exact ((restricted_theta_zero s g t).mp hr).2
  | succ k => exact (restricted_theta_succ s g k t).mp hr

/-- This is a statement about each ORIGINAL written subtree, with its actual
source value. No transformed-value comparison is supplied as a premise. -/
theorem restricted_gap (s g : Nat) (hg : rootCheck s g = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s g t) :
    denote (contextCode s) t < interpretation (contextCode s) g ∨
      omegaSequence (base (contextCode s)) 1 ≤ denote (contextCode s) t := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    exact Or.inl ((checked_parameters _ (.parameter p) ht p
      (by simp [RelativeTerm.parameters])).2.trans_le (root_base_le s g hg))
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s g t u).mp hr
    rcases iht hc.1 hs.1 with hl | hh
    · rcases ihu hc.2 hs.2 with hl' | hh'
      · apply Or.inl
        have he := (alphaCode_spec s g hg).2
        have ha := BaseTransformation.base_additive (alphaCode s g)
          (alphaCode_baseCheck s g hg)
        change Ordinal.IsPrincipal (· + ·) (unionInterpretation (alphaCode s g)) at ha
        rw [he] at ha
        exact ha hl hl'
      · apply Or.inr
        exact hh'.trans (show denote (contextCode s) u ≤ denote (contextCode s) (.sum t u) from le_add_self)
    · apply Or.inr
      exact hh.trans (show denote (contextCode s) t ≤ denote (contextCode s) (.sum t u) from le_self_add)
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero => exact Or.inl ((restricted_theta_zero s g t).mp hr).1
    | succ k =>
      apply Or.inr
      apply le_of_not_gt
      intro hl
      have hs := (denote_lt_iff_outerSort_le _ _ ht 1 (Nat.succ_pos 0)).mp hl
      simp only [RelativeTerm.outerSort] at hs
      omega

theorem below_alpha_iff_below_gamma (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s g t) :
    denote (contextCode s) t < interpretation (contextCode s) a ↔
      denote (contextCode s) t < interpretation (contextCode s) g := by
  constructor
  · intro hl
    rcases restricted_gap s g hg t ht hr with hs | hh
    · exact hs
    · exact False.elim ((not_lt_of_ge hh) (hl.trans (rootBelowBoundary s a ha)))
  · exact fun hl => hl.trans hga

theorem small_agree (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s g t) : small s a t = small s g t := by
  have he : small s a t = true ↔ small s g t = true := by
    rw [small_exact s a ha t ht, small_exact s g hg t ht]
    exact below_alpha_iff_below_gamma s g a hg ha hga t ht hr
  cases hα : small s a t <;> cases hγ : small s g t <;> simp_all

/-- Both literal iota maps execute the same finite recursion on the original
restricted presentation. The code of each public atom is literally equal. -/
theorem transform_eq (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s g t) : transform s a t = transform s g t := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s g t u).mp hr
    simp only [transform, small_agree s g a hg ha hga _ ht hr,
      iht hc.1 hs.1, ihu hc.2 hs.2]
  | theta k t ih =>
    intro ht hr
    have hc := BaseTransformation.theta_argument_check _ k t ht
    have hs := restricted_argument s g k t hr
    simp only [transform, small_agree s g a hg ha hga _ ht hr, ih hc hs]

/-- Individual public-parameter bounds derive all gamma payloads of the
alpha output. In particular, atomizing a sum does not assume a Par oracle. -/
theorem transform_payloads_gamma (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s g t) : Payloads (alphaCode s g) (transform s a t) := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    have hl : denote (contextCode s) (.parameter p) < interpretation (contextCode s) g :=
      (checked_parameters _ (.parameter p) ht p
        (by simp [RelativeTerm.parameters])).2.trans_le (root_base_le s g hg)
    exact (parameterCode_spec s g hg (.parameter p) ht hl).1
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s g t u).mp hr
    cases hb : small s a (.sum t u) with
    | true =>
      have hl := (below_alpha_iff_below_gamma s g a hg ha hga _ ht hr).mp
        ((small_exact s a ha _ ht).mp hb)
      simpa only [transform, hb, Bool.cond_true, Payloads] using
        (parameterCode_spec s g hg (.sum t u) ht hl).1
    | false =>
      simpa only [transform, hb, Bool.cond_false, Payloads] using
        And.intro (iht hc.1 hs.1) (ihu hc.2 hs.2)
  | theta k t ih =>
    intro ht hr
    cases hb : small s a (.theta k t) with
    | true =>
      have hl := (below_alpha_iff_below_gamma s g a hg ha hga _ ht hr).mp
        ((small_exact s a ha _ ht).mp hb)
      simpa only [transform, hb, Bool.cond_true, Payloads] using
        (parameterCode_spec s g hg (.theta k t) ht hl).1
    | false =>
      simpa only [transform, hb, Bool.cond_false, Payloads] using
        ih (BaseTransformation.theta_argument_check _ k t ht) (restricted_argument s g k t hr)

theorem transform_parBounded (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s g t) :
    BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) (transform s a t) := by
  exact (BaseTransformation.parBounded_iff_payloads _ _ _
    (transform_checked s a ha t ht (restricted_mono s g a hga t hr))
    (alphaCode_baseCheck s g hg)).mpr (transform_payloads_gamma s g a hg ha hga t ht hr)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange
