import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeight
import Alexander313.Wilken.HereditaryNativeIotaAddition
import Alexander313.Wilken.HereditaryNativeLambda

/-!
# Actual principal and exposed query bounds for iota enclosure

These bounds use original native admission, Normality, actual source atom
values and actual theta comparison. The same-index exposed support bound
is a consequence of the real comparison theorem at an expression with
itself. No cross-base enclosure, epsilon successor or alpha-plus oracle is
supplied. Uncompiled proof candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Enclosure

open NativePublicBridge (contextCode contextCode_checked)
open OrderInduction

theorem source_atom_value_le (q : Nat) (t x : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t) (hx : x ∈ Comparison.atoms t) :
    denote q x ≤ denote q t := by
  have h := principalSum_mem_le (List.mem_map.mpr ⟨x, hx, rfl⟩ :
    denote q x ∈ (Comparison.atoms t).map (denote q))
  simpa only [source_atoms_value q t ht hn] using h

theorem unshifted_theta_checked (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta k t) = true)
    (hr : Restricted s a t) :
    check (alphaCode s a) (.theta k (unshifted s a t)) = true := by
  have hc := BaseTransformation.theta_argument_check _ k t ht
  have hs : finiteCheck (contextCode s) (SourceOne.PublicCodes.fragment (.theta k t)) t = true ∧
      k < SourceOne.PublicCodes.fragment (.theta k t) ∧ t.outerSort ≤ k + 2 := by
    simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
      (Bool.and_eq_true.mp ht).2
  exact Inverse.checked_theta _ k _ (unshifted_checked s a ha t hc hr)
    ((unshifted_outerSort s a t).trans hs.2.2)

theorem unshifted_positive_theta_value (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta k t) = true)
    (hr : Restricted s a t) (hk : 0 < k) :
    denote (alphaCode s a) (.theta k (unshifted s a t)) =
      denote (contextCode s) (.theta k t) :=
  HeightSupport.root_positive_theta_value s a k ha t (unshifted s a t) hk ht
    (unshifted_theta_checked s a k ha t ht hr)
    (unshifted_value s a ha t (BaseTransformation.theta_argument_check _ k t ht) hr)

/-- Actual exposed support is strictly below its own admitted collapse.
This follows from the proved native comparison law, including its second
support-witness branch; it is not an additional star condition. -/
theorem source_exposed_lt_root (q k : Nat) (t x : RelativeTerm Nat)
    (ht : check q (.theta k t) = true) (hn : Comparison.Normal q t)
    (hx : x ∈ exposedThetaList k t) : denote q x < denote q (.theta k t) := by
  apply lt_of_not_ge
  intro hge
  exact (lt_irrefl (denote q (.theta k t)))
    ((checked_theta_lt_iff_exposed q k t t ht ht hn hn).mpr (Or.inr ⟨x, hx, hge⟩))

theorem exposed_shape (k : Nat) (t x : RelativeTerm Nat)
    (hx : x ∈ exposedThetaList k t) : ∃ u, x = .theta k u := by
  have hs := exposedTheta_isThetaAt k t x ((mem_exposedThetaList_iff k t x).mp hx)
  cases x with
  | parameter p => cases hs
  | sum u v => cases hs
  | theta j u =>
    have hj : j = k := hs
    subst j
    exact ⟨u, rfl⟩

theorem low_transform_lt_theta (s a k : Nat) (ha : rootCheck s a = true)
    (x t : RelativeTerm Nat) (hx : check (contextCode s) x = true)
    (hrx : Restricted s a x) (hl : x.outerSort ≤ 1)
    (ht : check (alphaCode s a) (.theta k t) = true) :
    denote (alphaCode s a) (transform s a x) < denote (alphaCode s a) (.theta k t) := by
  have hv : denote (alphaCode s a) (transform s a x) < base (alphaCode s a) := by
    rw [transform_low_value s a ha x hx hrx hl, alpha_base s a ha]
    exact restricted_low_below s a ha x hx hrx hl
  exact hv.trans_le (((omegaSequence_strictMono (base (alphaCode s a))).monotone
    (Nat.zero_le k)).trans (FixedPoint.checked_theta_range _ k t ht).1)

theorem shifted_theta_lt_positive_theta (s a j k : Nat) (ha : rootCheck s a = true)
    (u t : RelativeTerm Nat) (hu : check (contextCode s) (.theta (j + 1) u) = true)
    (hru : Restricted s a (.theta (j + 1) u)) (hjk : j + 1 ≤ k)
    (ht : check (alphaCode s a) (.theta k t) = true) :
    denote (alphaCode s a) (transform s a (.theta (j + 1) u)) <
      denote (alphaCode s a) (.theta k t) := by
  have hc := transform_checked s a ha (.theta (j + 1) u) hu hru
  rw [transform_theta_succ s a j ha u hu hru] at hc ⊢
  exact (FixedPoint.checked_theta_range _ j _ hc).2.trans_le
    (((omegaSequence_strictMono (base (alphaCode s a))).monotone hjk).trans
      (FixedPoint.checked_theta_range _ k t ht).1)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Enclosure
