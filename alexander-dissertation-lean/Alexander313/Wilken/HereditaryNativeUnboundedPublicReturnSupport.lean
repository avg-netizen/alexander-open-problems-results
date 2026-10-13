import Alexander313.Wilken.PublicEpsilonNativeRootCompleteScalarCollapse
import Alexander313.Wilken.HereditaryNativeLowArithmetic
import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeightSupport

/-!
# Original positive-source callers for unbounded SAME-value return

The actual high root at contextCode s supplies the original complete scalar
guard. Every admitted target parameter has a finite LOW return at the SAME
original source, licensed by p < root < finiteBase(s+2). Actual positive
cardinal suffix equality transfers every recursive sort caller. No endpoint
bound on the target term, chosen representation, or collapse oracle is used.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UnboundedPublicReturn

open NativePublicBridge (contextCode contextCode_primrec)
open ThetaCourse

theorem scalar_root (s a : Nat) (ha : Iota.rootCheck s a = true) :
    RootLowCollapse.rootCheck (contextCode s) a = true := by
  obtain ⟨t, he, ht, hn, hh⟩ := (Iota.rootCheck_exact s a).mp ha
  exact (RootLowCollapse.rootCheck_exact _ a).mpr ⟨t, he, ht, hn, hh⟩

/-- Every original target payload has a concrete finite source return.
Original stored public levels need not be minimal. -/
theorem parameter_return (s a p : Nat) (ha : Iota.rootCheck s a = true)
    (hp : parameterCheck (Iota.alphaCode s a) p = true) :
    Comparison.acceptedCode (contextCode s)
        (LowArithmetic.returnCode s (Canonical.canonicalize p)) = true ∧
      lowCheckCode (contextCode s)
        (LowArithmetic.returnCode s (Canonical.canonicalize p)) = true ∧
      interpretation (contextCode s)
        (LowArithmetic.returnCode s (Canonical.canonicalize p)) = parameters p := by
  have hpc := (parameterCheck_exact _ p).mp hp
  have hval := Canonical.canonicalize_value p hpc.1
  have hb : unionInterpretation (Canonical.canonicalize p) < finiteBase ((s + 1) + 1) := by
    rw [hval]
    exact (show parameters p < interpretation (contextCode s) a from by
      simpa only [Iota.alpha_base s a ha] using hpc.2.2).trans
        (LowArithmetic.lowInput_bound s a (Iota.root_low s a ha))
  have hr := LowArithmetic.returnCode_spec s (Canonical.canonicalize p)
    (Canonical.canonicalize_check p hpc.1) hb
  exact ⟨hr.2.1, hr.1, hr.2.2.trans hval⟩

/-- Genuine SAME-value recursive outputs inherit EVERY positive sort
bound from the original target term. -/
theorem returned_sort (s a : Nat) (ha : Iota.rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (Iota.alphaCode s a) t = true)
    (out k : Nat) (ho : Comparison.acceptedCode (contextCode s) out = true)
    (hv : interpretation (contextCode s) out = denote (Iota.alphaCode s a) t)
    (hk : 0 < k) (hs : t.outerSort ≤ k) : (rawTree out).outerSort ≤ k := by
  have hc := ((Comparison.acceptedCode_exact _ out).mp ho).1
  apply (denote_lt_iff_outerSort_le (contextCode s) _ (Arithmetic.raw_checked _ out hc) k hk).mp
  have he : k - 1 + 1 = k := by omega
  have hω : omegaSequence (base (contextCode s)) k = omegaSequence (base (Iota.alphaCode s a)) k := by
    simpa only [he] using Iota.HeightSupport.root_omegaSequence_succ s a (k - 1) ha
  rw [Arithmetic.raw_value _ out hc, hv, hω]
  exact (denote_lt_iff_outerSort_le _ t ht k hk).mpr hs

/-- The complete scalar caller is derived from original theta admission
and the genuine recursive source value, including all hidden arguments. -/
theorem scalar_caller (s a k : Nat) (ha : Iota.rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (Iota.alphaCode s a) (.theta k t) = true)
    (out : Nat) (ho : Comparison.acceptedCode (contextCode s) out = true)
    (hv : interpretation (contextCode s) out = denote (Iota.alphaCode s a) t) :
    RootCompleteScalarCollapse.inputCheck (contextCode s) a k out = true := by
  have htc := FixedPoint.checked_theta_argument _ k t ht
  have hts := (denote_lt_iff_outerSort_le _ t htc (k + 2) (by omega)).mp
    (FixedPoint.checked_theta_sort _ k t ht)
  exact (RootCompleteScalarCollapse.inputCheck_exact _ a k out).mpr
    ⟨scalar_root s a ha, ho, returned_sort s a ha t htc out (k + 2) ho hv (by omega) hts⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UnboundedPublicReturn
