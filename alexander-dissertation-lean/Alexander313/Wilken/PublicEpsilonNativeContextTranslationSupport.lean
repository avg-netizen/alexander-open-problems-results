import Alexander313.Wilken.HereditaryNativeUniformPublicReturn
import Alexander313.Wilken.PublicEpsilonNativeRootLowCollapseSupport
import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive
import Alexander313.Wilken.HereditaryNativeLogEndSupport

/-!
# Genuine high-root coverage for contextual SAME-value translation

Actual LOW interval coverage supplies a checked finite representation.
The original normalizer and its real final principal atom then construct
an admitted high theta-zero root of the SAME epsilon value. Parameter
shape, positive theta indices and the exceptional base epsilon are all
excluded by the actual admission and strict base bound. No root, code,
normalizer or translation oracle is supplied. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.Support

open ThetaCourse

def rootAtomCode (q c : Nat) : Nat := LogEndZero.endCode (Normalization.normalizeCode q c)

theorem rootAtomCode_primrec : Primrec₂ rootAtomCode :=
  (Primrec.comp LogEndZero.endCode_primrec Normalization.Effective.normalizeCode_primrec).to₂

private theorem rawTree_code_eq (q c : Nat) (hc : checkCode q c = true) :
    (rawTree c).code = c := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  rw [← he, rawTree_code]

/-- The real normalizer and final-atom producer return an ORIGINAL high
root of the SAME value on every RAW LOW epsilon strictly above its base. -/
theorem rootAtomCode_spec (q c : Nat) (hc : lowCheckCode q c = true)
    (hp : base q < interpretation q c)
    (he : Ordinal.omega0 ^ interpretation q c = interpretation q c) :
    RootLowCollapse.rootCheck q (rootAtomCode q c) = true ∧
      interpretation q (rootAtomCode q c) = interpretation q c := by
  have hcheck : checkCode q c = true := (Bool.and_eq_true.mp hc).1
  have hn := Normalization.normalizeCode_accepted q c hcheck
  have hnc := (Comparison.acceptedCode_exact q _).mp hn.1
  have hlow : lowCheckCode q (Normalization.normalizeCode q c) = true :=
    OmegaPowers.low_of_bound q _ hnc.1 (by
      rw [hn.2]
      exact (HeightBoundary.input_spec q c hc).2.2)
  have hpos : 0 < interpretation q c := (base_pos q
    (HeightBoundary.input_spec q c hc).2.1).trans hp
  have hpnc : 0 < interpretation q (Normalization.normalizeCode q c) := by
    rw [hn.2]; exact hpos
  have hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation q c) := by
    rw [← he]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hs := LogEnd.Support.endCode_spec q (Normalization.normalizeCode q c)
    hlow hn.1 (ne_of_gt hpnc)
  have hv : interpretation q (rootAtomCode q c) = interpretation q c := by
    rw [rootAtomCode, LogEndZero.endCode_value q _ hn.1, hn.2,
      SourceChi.Powers.endValue_principal _ hpos hprincipal]
  have ha := (Comparison.acceptedCode_exact q _).mp hs.2.1
  have hraw := Arithmetic.raw_checked q _ ha.1
  have hcode := rawTree_code_eq q _ ha.1
  rcases hs.2.2.2.2.2 with ⟨p, hshape⟩ | ⟨k, a, hshape⟩
  · have ht : check q (.parameter p) = true := by
      simpa only [hshape] using hraw
    have hb := (checked_parameters q (.parameter p) ht p
      (by simp only [RelativeTerm.parameters, List.mem_singleton])).2
    have heval : interpretation q (rootAtomCode q c) = parameters p := by
      rw [rootAtomCode, ← Arithmetic.raw_value q _ ha.1, hshape]
      rfl
    have hlt : interpretation q c < base q := by rw [← hv, heval]; exact hb
    exact False.elim ((not_lt_of_ge (le_of_lt hp)) hlt)
  · have hrootcode : rootAtomCode q c = (.theta k a : RelativeTerm Nat).code := by
      exact hcode.symm.trans (congrArg RelativeTerm.code hshape)
    have hk : k = 0 := LogEnd.Support.theta_low_index q k a (by
      rw [← hrootcode]
      exact hs.1)
    subst k
    have ht : check q (.theta 0 a) = true := by simpa only [hshape] using hraw
    have hna : Comparison.Normal q a := by
      simpa only [hshape, Comparison.Normal] using ha.2
    have hval : denote q (.theta 0 a) = interpretation q c := by
      simpa only [hrootcode, interpretation_code] using hv
    have hhigh : omegaSequence (base q) 1 ≤ denote q a := by
      rcases (OmegaPowers.theta_epsilon_iff q a ht).mp
        (by simpa only [hval] using he) with hb | hh
      · exact False.elim ((ne_of_gt hp) (hval.symm.trans hb))
      · exact hh
    have hacheck := BaseTransformation.theta_argument_check q 0 a ht
    have hsort : 1 < a.outerSort := by
      apply lt_of_not_ge
      intro hle
      exact (not_lt_of_ge hhigh)
        ((denote_lt_iff_outerSort_le q a hacheck 1 (by omega)).mpr hle)
    exact ⟨(RootLowCollapse.rootCheck_exact q _).mpr ⟨a, hrootcode, ht, hna, hsort⟩, hv⟩

/-- Actual native LOW boundary coverage gives a genuine finite high-root
representation of EVERY epsilon in the strict interval above this base. -/
theorem root_exists_of_boundary (q : Nat) (hq : baseCheck q = true)
    (xi : Ordinal.{0}) (hp : base q < xi)
    (he : Ordinal.omega0 ^ xi = xi) (hb : xi < globalBoundary (base q) 0) :
    ∃ c, RootLowCollapse.rootCheck q c = true ∧ interpretation q c = xi := by
  obtain ⟨c, hc, hv⟩ := (lt_boundary_iff_code q hq xi).mp hb
  have hs := rootAtomCode_spec q c hc (by simpa only [hv] using hp)
    (by simpa only [hv] using he)
  exact ⟨rootAtomCode q c, hs.1, hs.2.trans hv⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.Support
