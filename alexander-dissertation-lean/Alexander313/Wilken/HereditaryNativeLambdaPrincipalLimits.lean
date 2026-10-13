import Alexander313.Wilken.HereditaryNativeLambdaPrincipalLimitsSupport
import Alexander313.Wilken.HereditaryNativeLambdaRawAlphaPlus

/-!
# Source Lemma 2.48(a) on both actual lambda branches

The high branch has positive actual iota(Delta), by the proved original
domain order embedding and the original nonzero high part. Its epsilon root
belongs to the L class of proper-limit omega exponents. In the low branch,
the genuine low-collapse formula and strict-supremum zeta branch derive the
same zero characterization, including all epsilon-plus-finite exceptions.
Both original normal and raw executing proper-root domains are covered.
No branch, class, normalization-invariance or positivity oracle is supplied.
All proof candidates are uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.PrincipalLimits

open NativePublicBridge (contextCode contextCode_checked)

theorem literalDelta_positive (s a : Nat) (ha : Iota.rootCheck s a = true) :
    0 < interpretation (Iota.alphaCode s a) (Iota.literalCode s a (Lambda.deltaCode a)) := by
  have hi := Lambda.delta_input s a ha
  obtain ⟨_, t, he, ht, hn, hs⟩ := (Iota.inputCheck_exact s a _).mp hi
  have hr := (Iota.restricted_iff_sourceStar s a ha t ht hn).mpr hs
  have hp : 0 < denote (contextCode s) t := pos_iff_ne_zero.mpr (by
    simpa only [he, interpretation_code] using Lambda.delta_nonzero s a ha)
  let z := Normalization.zeroTree
  have hz : check (contextCode s) z = true := Normalization.zeroTree_checked _ (contextCode_checked s)
  have hzn : Comparison.Normal (contextCode s) z := Normalization.zeroTree_normal _
  have hzr : Iota.Restricted s a z := by
    intro u hu
    exact False.elim (by simpa only [z, Normalization.zeroTree, Iota.fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] using hu)
  have hsmall : z.outerSort ≤ 1 := by
    change (0 : Nat) ≤ 1
    omega
  have hv := Iota.transform_low_value s a ha z hz hzr hsmall
  have hlt := (Iota.transform_lt_iff s a ha z t hz ht hzn hn hzr hr).mpr
    (by simpa only [z, Normalization.zeroTree_denote] using hp)
  have hout : Iota.literalCode s a (Lambda.deltaCode a) = (Iota.transform s a t).code := by
    simp only [Iota.literalCode, hi, Bool.cond_true, he, Iota.stateCode_code]
  simpa only [hout, interpretation_code, hv, z, Normalization.zeroTree_denote] using hlt

theorem high_value_positive (s a : Nat) (ha : Iota.rootCheck s a = true) :
    0 < Branches.sourceValue s a := by
  simp only [Branches.sourceValue, ha, if_true]
  exact (literalDelta_positive s a ha).trans_le le_self_add

/-- The original non-epsilon branch is matched to the actual class L,
using the full epsilon-plus-finite low exponent formula. -/
theorem low_value_zero_iff (s a : Nat) (ha : Branches.inputCheck s a = true)
    (hh : Iota.rootCheck s a = false) :
    Branches.sourceValue s a = 0 ↔ ¬ PrincipalLimit (interpretation (contextCode s) a) := by
  classical
  obtain ⟨t, he, ht, hn, hp⟩ := (Branches.inputCheck_exact s a).mp ha
  let q := contextCode s
  have hq := contextCode_checked s
  have hc := FixedPoint.checked_theta_argument q 0 t ht
  have hsort : t.outerSort ≤ 1 := by
    by_contra hnot
    have htHigh : 1 < t.outerSort := by omega
    have hf := (Iota.rootCheck_exact s a).mpr ⟨t, he, ht, hn, htHigh⟩
    simp only [hh, Bool.false_eq_true] at hf
  have hl := (denote_lt_iff_outerSort_le q t hc 1 (by omega)).mpr hsort
  have hpos : 0 < denote q t := pos_iff_ne_zero.mpr
    ((SourceChi.Arithmetic.proper_theta_zero_iff q t ht hn).mp hp)
  have hroot : interpretation q a = Ordinal.omega0 ^ lowOmegaExponent (base q) (denote q t) := by
    simp only [he, interpretation_code]
    change globalCollapse (base q) 0 (denote q t) = _
    exact globalCollapse_low_eq_omegaPower (base q) (Or.inr ((baseCheck_exact q).mp hq).2)
      (denote q t) hl
  have hz : SourceZeta.sourceValue s a = 0 ↔
      ¬ Order.IsSuccLimit (lowOmegaExponent (base q) (denote q t)) := by
    simpa only [SourceZeta.sourceValue, SourceZeta.argumentCode, he,
      Localization.argumentCode_theta, FixedPoint.residual, interpretation_code,
      Ordinal.mod_eq_of_lt hl] using low_zeta_zero_iff q t ht hn hl hpos
  simpa only [Branches.sourceValue, hh, Bool.false_eq_true, if_false,
    hroot, omega_principalLimit_iff] using hz

/-- Full source Lemma 2.48(a) for the actual two-branch source value.
The sole guard is the original admitted weak-normal proper theta-zero root. -/
theorem source_value_zero_iff (s a : Nat) (ha : Branches.inputCheck s a = true) :
    Branches.sourceValue s a = 0 ↔ ¬ PrincipalLimit (interpretation (contextCode s) a) := by
  cases hh : Iota.rootCheck s a with
  | false => exact low_value_zero_iff s a ha hh
  | true =>
    have he := (Branches.high_iff_epsilon s a ha).mp hh
    have hL := epsilon_principalLimit _ he
    have hp := high_value_positive s a hh
    exact ⟨fun hz => False.elim ((ne_of_gt hp) hz), fun h => False.elim (h hL)⟩

/-- Every actual normal two-branch output is zero exactly when its
ORIGINAL root fails to be a proper limit of additive principal numbers. -/
theorem execute_zero_iff (s a out : Nat) (ho : out ∈ Branches.execute s a) :
    interpretation (Branches.outputContext s a) out = 0 ↔
      ¬ PrincipalLimit (interpretation (contextCode s) a) := by
  have hs := Branches.execute_spec s a out ho
  rw [hs.2.2]
  exact source_value_zero_iff s a hs.1

/-- Full original raw proper-root execution retains the same genuine
source L characterization by actual root-normalizer value fidelity. -/
theorem raw_execute_zero_iff (s a out : Nat) (ho : out ∈ Branches.Raw.execute s a) :
    interpretation (Branches.outputContext s (Branches.Raw.normalizedRoot s a)) out = 0 ↔
      ¬ PrincipalLimit (interpretation (contextCode s) a) := by
  have ha := (Branches.Raw.execute_spec s a out ho).1
  have hb : out ∈ Branches.execute s (Branches.Raw.normalizedRoot s a) := by
    simpa only [Branches.Raw.execute, ha, Bool.cond_true] using ho
  have hc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1
  have hv := (Normalization.normalizeCode_accepted (contextCode s) a hc).2
  simpa only [Branches.Raw.normalizedRoot, hv] using
    execute_zero_iff s (Branches.Raw.normalizedRoot s a) out hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.PrincipalLimits
