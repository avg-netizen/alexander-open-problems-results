import Alexander313.Wilken.PublicEpsilonNativeMappedOmegaQuotientSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaAddition
import Alexander313.Wilken.PublicEpsilonNativeUnboundedOmegaQuotient

/-!
# Actual epsilon-base arithmetic and mapped quotient callers

The real all-level minimum formula derives the zero-family threshold,
left quotient and absorption rules at the actual target epsilon. Genuine
normal source addition and full order reflection identify the mapped
middle subtraction. No multiplication, subtraction, normalized addition
or relative collapse equation is assumed. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MappedOmegaQuotient

open OrderSupport
open Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaQuotient
  (baseTerm thresholdTerm baseTerm_spec thresholdTerm_spec globalCollapse_low_eq_power
   not_offset_below_threshold epsilon_above_absorbs)

-- These six scalar identities were proved for ANY actual epsilon base,
-- without a root or endpoint premise; reuse their original ordinal proofs.
open PublicEpsilonIota.MappedOmegaQuotient
  (theta_zero_unit zero_threshold_lt_first theta_zero_below_threshold
   theta_zero_shifted_quotient theta_zero_above_threshold principal_above_first_absorbs)

private theorem zero_restricted (q root : Nat) : Restricted q root Normalization.zeroTree :=
  OmegaQuotient.Support.zero_restricted q root

theorem baseTerm_restricted (q root : Nat) : Restricted q root baseTerm :=
  (restricted_theta_succ q root 0 _).mpr (zero_restricted q root)

theorem thresholdTerm_restricted (q root : Nat) : Restricted q root thresholdTerm := by
  apply (restricted_theta_succ q root 0 _).mpr
  intro x hx
  simp only [thresholdTerm, LogEndZero.unitCode, ThetaCourse.rawTree_code, fullList,
    RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hx

theorem mapped_baseTerm (q root : Nat) (ha : rootCheck q root = true) :
    denote (betaCode q root) (transform q root baseTerm) = base (betaCode q root) := by
  have hs := baseTerm_spec q (source_checked q root ha)
  rw [baseTerm, transform_theta_succ q root 0 ha _ hs.1 (baseTerm_restricted q root)]
  change globalCollapse (base (betaCode q root)) 0
    (denote (betaCode q root) (transform q root Normalization.zeroTree)) = _
  rw [transform_low_value q root ha _ (Normalization.zeroTree_checked q (source_checked q root ha))
    (zero_restricted q root) (Nat.zero_le _), Normalization.zeroTree_denote]
  simpa only [omegaSequence_zero] using globalCollapse_zero (base (betaCode q root))
    (base_pos _ (betaCode_baseCheck q root ha))
    (BaseTransformation.base_additive _ (betaCode_baseCheck q root ha)) 0

theorem mapped_thresholdTerm (q root : Nat) (ha : rootCheck q root = true) :
    denote (betaCode q root) (transform q root thresholdTerm) =
      base (betaCode q root) * Ordinal.omega0 := by
  have hs := thresholdTerm_spec q (source_checked q root ha)
  have hu := Decomposition.input_tree q _ (LogEndZero.unitCode_accepted q (source_checked q root ha))
  have hur : Restricted q root (ThetaCourse.rawTree LogEndZero.unitCode) := by
    intro x hx
    simp only [LogEndZero.unitCode, ThetaCourse.rawTree_code, fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hx
  have hv : denote q (ThetaCourse.rawTree LogEndZero.unitCode) = 1 := by
    rw [← Decomposition.input_value q _ (LogEndZero.unitCode_accepted q (source_checked q root ha)),
      LogEndZero.unitCode_value]
  rw [thresholdTerm, transform_theta_succ q root 0 ha _ hs.1 (thresholdTerm_restricted q root)]
  change globalCollapse (base (betaCode q root)) 0
    (denote (betaCode q root) (transform q root (ThetaCourse.rawTree LogEndZero.unitCode))) = _
  rw [transform_low_value q root ha _ hu.1 hur (by
    simp only [LogEndZero.unitCode, ThetaCourse.rawTree_code, RelativeTerm.outerSort]; omega), hv]
  exact theta_zero_unit _ ((baseCheck_exact _).mp (betaCode_baseCheck q root ha)).2

/-- Actual normalized source addition, rather than a raw Normal-sum
assumption, identifies the mapped left subtraction with target subtraction. -/
theorem mapped_subtract_base (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q root t) (hle : omegaSequence (base q) 1 ≤ denote q t) :
    denote (betaCode q root) (transform q root (Arithmetic.subtractTerm q baseTerm.code t.code)) =
      denote (betaCode q root) (transform q root t) - base (betaCode q root) := by
  have hq := source_checked q root ha
  have hb := baseTerm_spec q hq
  have hbc : checkCode q baseTerm.code = true := by simpa only [checkCode_code] using hb.1
  have htc : checkCode q t.code = true := by simpa only [checkCode_code] using ht
  have hs := Arithmetic.subtractTerm_spec q baseTerm.code t.code hbc htc
  have hsc := Comparison.admitted_checked q _ hq _ hs.1
  have hsr := OmegaQuotient.Support.subtract_restricted q root baseTerm.code t.code htc
    (by simpa only [ThetaCourse.rawTree_code] using hr)
  have hv : denote q (Arithmetic.subtractTerm q baseTerm.code t.code) =
      denote q t - omegaSequence (base q) 1 := by
    simpa only [interpretation_code, hb.2.2] using hs.2.2
  have hadd := Addition.sourceSum_spec q root ha baseTerm _ hb.1 hsc hb.2.1 hs.2.1
    (baseTerm_restricted q root) hsr
  have he : denote q (Addition.sourceSum q baseTerm (Arithmetic.subtractTerm q baseTerm.code t.code)) =
      denote q t := by
    rw [hadd.2.2.2.1, hb.2.2, hv, Ordinal.add_sub_cancel_of_le hle]
  have hm := (transform_eq_iff q root ha _ t hadd.1 ht hadd.2.1 hn hadd.2.2.1 hr).mpr he
  have hsum : base (betaCode q root) +
      denote (betaCode q root) (transform q root (Arithmetic.subtractTerm q baseTerm.code t.code)) =
        denote (betaCode q root) (transform q root t) := by
    rw [← mapped_baseTerm q root ha, ← hadd.2.2.2.2]
    exact hm
  calc
    denote (betaCode q root) (transform q root (Arithmetic.subtractTerm q baseTerm.code t.code)) =
        (base (betaCode q root) +
          denote (betaCode q root) (transform q root (Arithmetic.subtractTerm q baseTerm.code t.code))) -
          base (betaCode q root) := (Ordinal.add_sub_cancel _ _).symm
    _ = denote (betaCode q root) (transform q root t) - base (betaCode q root) := by rw [hsum]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.MappedOmegaQuotient
