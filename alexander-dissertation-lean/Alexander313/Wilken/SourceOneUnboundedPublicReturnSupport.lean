import Alexander313.Wilken.SourceOneRootScalarCollapse

/-!
# Original source-one callers for unbounded SAME-value return

Every admitted target payload has a genuine finite original source0 return
because it lies below the actual original root and finiteBase1. Positive
cardinal suffix equality transfers every recursive theta sort. All syntax
and output admission use original check0/Theta.Normal0, never native base1.
No endpoint or supplied representation. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.UnboundedPublicReturn

open ThetaCourse

theorem parameter_return (b p : Nat) (hb : rootCheck b = true)
    (hp : NativeContext.parameterCheck (alphaCode b) p = true) :
    RootScalar.argumentCheck (SourceZeta.Transport.returnCode 0 (Canonical.canonicalize p)) = true ∧
      lowCheckCode 0 (SourceZeta.Transport.returnCode 0 (Canonical.canonicalize p)) = true ∧
      interpretation 0 (SourceZeta.Transport.returnCode 0 (Canonical.canonicalize p)) = NativeContext.parameters p := by
  have hs := (NativeContext.parameterCheck_exact _ p).mp hp
  have hv := Canonical.canonicalize_value p hs.1
  have hbound : unionInterpretation (Canonical.canonicalize p) < finiteBase (0 + 1) := by
    rw [hv]
    exact (show NativeContext.parameters p < interpretation 0 b from by
      simpa only [alpha_base b hb] using hs.2.2).trans
        (RootScalar.low_public_bound b (root_low b hb))
  have hr := SourceZeta.Transport.returnCode_spec 0 (Canonical.canonicalize p)
    (Canonical.canonicalize_check p hs.1) hbound
  have ha := RootScalar.acceptedLow_to_accepted _ hr.1
  exact ⟨ha.1, ha.2, hr.2.trans hv⟩

theorem returned_sort (b : Nat) (hb : rootCheck b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode b) t = true)
    (out k : Nat) (ho : RootScalar.argumentCheck out = true)
    (hv : interpretation 0 out = NativeContext.denote (alphaCode b) t)
    (hk : 0 < k) (hs : t.outerSort ≤ k) : (rawTree out).outerSort ≤ k := by
  apply (denote_lt_iff_outerSort_le 0 _ (RootScalar.raw_checked out ho) k hk).mp
  have hω : omegaSequence (finiteBase 0) k = omegaSequence (NativeContext.base (alphaCode b)) k := by
    simpa only [finiteBase_zero, alpha_base b hb] using RootScalar.root_omegaSequence_pos b k hb hk
  rw [RootScalar.raw_value out ho, hv, hω]
  exact (NativeContext.denote_lt_iff_outerSort_le _ t ht k hk).mpr hs

theorem scalar_caller (b k : Nat) (hb : rootCheck b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode b) (.theta k t) = true)
    (out : Nat) (ho : RootScalar.argumentCheck out = true)
    (hv : interpretation 0 out = NativeContext.denote (alphaCode b) t) :
    RootScalar.inputCheck b k out = true := by
  have hac := NativeContext.FixedPoint.checked_theta_argument _ k t ht
  have hs := (NativeContext.denote_lt_iff_outerSort_le _ t hac (k + 2) (by omega)).mp
    (NativeContext.FixedPoint.checked_theta_sort _ k t ht)
  exact (RootScalar.inputCheck_exact b k out).mpr
    ⟨hb, ho, returned_sort b hb t hac out (k + 2) ho hv (by omega) hs⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.UnboundedPublicReturn
