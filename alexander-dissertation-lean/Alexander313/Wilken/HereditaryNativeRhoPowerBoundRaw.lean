import Alexander313.Wilken.HereditaryNativeRhoPowerBound

/-!
# Strong corrected rho bound on the original raw LOW query domain

Actual normalization derives the Normal query and its real indicator.
An actual normalized-query rho execution exists by the proved domain;
real same-value execution invariance transfers its bound to the original
raw execution. No Normal query, normalized output or correction oracle is
supplied. Arithmetic coefficient hypotheses remain explicit. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.PowerBound

theorem rho_add_base_le_corrected_power_raw (q c k b out : Nat)
    (hc : lowCheckCode q c = true) (hn : Comparison.acceptedCode q c = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (hA : 0 < interpretation q c + (k : Ordinal.{0}))
    (hχ : SourceChi.rawChiCode q b = false) (ho : out ∈ execute q b)
    (hb : interpretation q b < Ordinal.omega0 ^
      (interpretation q c + cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 +
        (k : Ordinal.{0}))) :
    interpretation q out + base q ≤ base q * (interpretation q c + (k : Ordinal.{0})) := by
  have hi := (execute_domain q b).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hcheck := (Bool.and_eq_true.mp hi).1
  have hnormal := Normalization.normalizeCode_accepted q b hcheck
  have hlow := LogEnd.normalized_low q b hi
  obtain ⟨other, hother⟩ := Part.dom_iff_mem.mp ((execute_domain q _).mpr hlow)
  have hraw : SourceChi.rawInputCheck q b = true :=
    (SourceChi.rawInputCheck_exact q b).mpr hcheck
  have hχnormal : SourceChi.chiCode q (Normalization.normalizeCode q b) = false := by
    simpa only [SourceChi.rawChiCode, hraw, Bool.true_and] using hχ
  have hbound := rho_add_base_le_corrected_power q c k _ other hc hn hlim hA
    hnormal.1 hχnormal hother (by rw [hnormal.2]; exact hb)
  have hvalue := execute_value_invariant q b _ out other ho hother hnormal.2.symm
  rwa [← hvalue] at hbound

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.PowerBound
