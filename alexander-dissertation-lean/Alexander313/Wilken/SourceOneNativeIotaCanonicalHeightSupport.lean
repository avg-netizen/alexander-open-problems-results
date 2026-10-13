import Alexander313.Wilken.SourceOneNativeIotaInverse
import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeightSupport

/-!
# Genuine source-one height and same-alpha cardinal suffix

The original source-one canonical minimum is computed by its actual
normalizer. Every inverse atom returns below the original root and hence
below its true height endpoint. Positive-index source and target collapse
families agree by the actual finite hull recursion, using only the genuine
cardinal suffix equality on one<=alpha<Omega-one. No height or collapse
agreement oracle occurs. Original source-one dictionaries remain explicit.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.HeightSupport

open OrderSupport

theorem source_accepted (t : RelativeTerm Nat) (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    SourceOne.Comparison.acceptedCode t.code = true := by
  have ha := (finiteCheck_iff 0 (SourceOne.PublicCodes.fragment t) t).mp ht
  exact (SourceOne.Comparison.acceptedCode_iff _).mpr
    ⟨t, rfl, by simpa only [check_zero] using ht,
      by simpa only [SourceOne.Normal, finiteBase_zero, parameters_zero] using hn.finite ha⟩

theorem source_canonical_height_normal (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) :
    SourceOne.CanonicalHeight.canonicalHeightCode t.code = t.height := by
  rw [SourceOne.CanonicalHeight.canonicalHeightCode_normal _ (source_accepted t ht hn), heightCode_code]

theorem root_source_accepted (a : Nat) (ha : rootCheck a = true) :
    SourceOne.Comparison.acceptedCode a = true := by
  obtain ⟨t, rfl, ht, hn, hs⟩ := (rootCheck_exact a).mp ha
  exact source_accepted _ ht hn

theorem source_low_height_le_root (a : Nat) (ha : rootCheck a = true) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hn : Theta.Normal 0 t) (hl : t.outerSort ≤ 1)
    (hb : denote 0 t < interpretation 0 a) :
    t.height ≤ SourceOne.CanonicalHeight.canonicalHeightCode a := by
  have hc : SourceOne.PublicCodes.lowCheckCode t.code = true := by
    have hs : lowCheckCode 0 t.code = true := by
      simp only [lowCheckCode_code, lowCheck, ht, hl, decide_true, Bool.true_and]
    simpa only [lowCheckCode_zero] using hs
  have hr := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint
    (SourceOne.CanonicalHeight.canonicalHeightCode a) a
    (by simpa only [lowCheckCode_zero] using root_low a ha)).mp le_rfl
  have hh := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint
    (SourceOne.CanonicalHeight.canonicalHeightCode a) t.code hc).mpr
    (by simpa only [SourceOne.PublicCodes.interpretation_code] using hb.trans hr)
  simpa only [source_canonical_height_normal t ht hn] using hh

theorem inverse_atom_height (a p : Nat) (ha : rootCheck a = true)
    (hp : NativeContext.parameterCheck (alphaCode a) p = true) :
    (Inverse.atomTerm p).height ≤ SourceOne.CanonicalHeight.canonicalHeightCode a := by
  have hs := Inverse.atom_spec a p ha hp
  apply source_low_height_le_root a ha _ hs.1 hs.2.1 hs.2.2.1
  rw [hs.2.2.2]
  simpa only [alpha_base a ha] using NativeContext.parameter_sound _ p hp

theorem root_omegaSequence_succ (a k : Nat) (ha : rootCheck a = true) :
    omegaSequence 1 (k + 1) = omegaSequence (NativeContext.base (alphaCode a)) (k + 1) := by
  have hzero := NativeContext.Iota.HeightSupport.levelCardinal_zero_eq_of_interval 1
    (interpretation 0 a) (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)).le (root_lt_first a ha)
  rw [← alpha_base a ha] at hzero
  exact congrArg Cardinal.ord
    (NativeContext.Iota.HeightSupport.levelCardinal_eq_of_zero_eq _ _ hzero (k + 1))

theorem root_positive_finiteCollapse (a n k : Nat) (ha : rootCheck a = true)
    (hk : 0 < k) (hkn : k < n) (ξ : Ordinal.{0}) :
    sourceFiniteCollapse 1 n k ξ = sourceFiniteCollapse (NativeContext.base (alphaCode a)) n k ξ := by
  apply NativeContext.Iota.HeightSupport.finiteCollapse_suffix_congr _ _ n 1 k _ (by omega) hkn ξ
  intro j hj
  cases j with
  | zero => omega
  | succ j => exact root_omegaSequence_succ a j ha

theorem root_positive_theta_value (a k : Nat) (ha : rootCheck a = true)
    (t u : RelativeTerm Nat) (hk : 0 < k) (ht : check 0 (.theta k t) = true)
    (hu : NativeContext.check (alphaCode a) (.theta k u) = true)
    (hv : NativeContext.denote (alphaCode a) u = denote 0 t) :
    NativeContext.denote (alphaCode a) (.theta k u) = denote 0 (.theta k t) := by
  let n := max (SourceOne.PublicCodes.fragment (.theta k t)) (SourceOne.PublicCodes.fragment (.theta k u))
  have htn := Theta.checked_admissible 0 n (.theta k t) ht
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_left _ _))
  have hun := NativeContext.Comparison.checked_admissible _ n (.theta k u) hu
    ((SourceOne.PublicCodes.height_le_fragment _).trans (le_max_right _ _))
  have hkn : k < n := by
    cases htn.2 with
    | theta h0k hkn hsort ht => exact hkn
  have hta := Theta.admitted_theta_argument htn
  have hua := NativeContext.Comparison.admitted_argument hun
  rw [NativeContext.denote_eq_finite _ n (alphaCode_baseCheck a ha) _ hun.2,
    denote_eq_finite 0 n _ htn.2]
  change sourceFiniteCollapse (NativeContext.base (alphaCode a)) n k
      (NativeContext.finiteDenote _ n u) = sourceFiniteCollapse 1 n k (finiteDenote 0 n t)
  rw [← NativeContext.denote_eq_finite _ n (alphaCode_baseCheck a ha) u hua.2,
    ← denote_eq_finite 0 n t hta.2, hv, root_positive_finiteCollapse a n k ha hk hkn]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.HeightSupport
