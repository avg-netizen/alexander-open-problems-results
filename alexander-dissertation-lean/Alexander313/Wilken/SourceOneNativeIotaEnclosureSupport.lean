import Alexander313.Wilken.SourceOneNativeLambda
import Alexander313.Wilken.HereditaryNativeIotaEnclosureSupport

/-!
# Actual source-zero principal and exposed bounds for enclosure

These supporting facts use the ORIGINAL zero-parameter theta atom list,
source-zero admission and Normality. They construct genuine alpha theta
callers at original argument values and bound all original exposed calls
by their actual source theta node. No enclosure or endpoint oracle is used.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Enclosure

open OrderSupport
open NativeContext.Iota.OrderInduction (checked_theta_pos_principal checked_theta_lt_iff_exposed)

theorem source_atom_value_le (t x : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hx : x ∈ thetaAtoms t) : denote 0 x ≤ denote 0 t := by
  have h := principalSum_mem_le (List.mem_map.mpr ⟨x, hx, rfl⟩ :
    denote 0 x ∈ (thetaAtoms t).map (denote 0))
  simpa only [source_atoms_value t ht hn] using h

theorem unshifted_theta_checked (a k : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 (.theta k t) = true) (hr : Restricted a t) :
    NativeContext.check (alphaCode a) (.theta k (unshifted a t)) = true := by
  have hc := argument_checked k t ht
  have hs : finiteCheck 0 (SourceOne.PublicCodes.fragment (.theta k t)) t = true ∧
      k < SourceOne.PublicCodes.fragment (.theta k t) ∧ t.outerSort ≤ k + 2 := by
    simpa only [finiteCheck_theta, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using ht
  exact NativeContext.Iota.Inverse.checked_theta _ k _ (unshifted_checked a ha t hc hr)
    ((unshifted_outerSort a t).trans hs.2.2)

theorem unshifted_positive_theta_value (a k : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 (.theta k t) = true) (hr : Restricted a t) (hk : 0 < k) :
    NativeContext.denote (alphaCode a) (.theta k (unshifted a t)) = denote 0 (.theta k t) :=
  HeightSupport.root_positive_theta_value a k ha t (unshifted a t) hk ht
    (unshifted_theta_checked a k ha t ht hr) (unshifted_value a ha t (argument_checked k t ht) hr)

theorem source_exposed_lt_root (k : Nat) (t x : RelativeTerm Nat)
    (ht : check 0 (.theta k t) = true) (hn : Theta.Normal 0 t)
    (hx : x ∈ exposedThetaList k t) : denote 0 x < denote 0 (.theta k t) := by
  apply lt_of_not_ge
  intro hge
  exact (lt_irrefl (denote 0 (.theta k t)))
    ((checked_source_theta_lt_iff_exposed k t t ht ht hn hn).mpr (Or.inr ⟨x, hx, hge⟩))

theorem exposed_shape (k : Nat) (t x : RelativeTerm Nat)
    (hx : x ∈ exposedThetaList k t) : ∃ u, x = .theta k u :=
  NativeContext.Iota.Enclosure.exposed_shape k t x hx

theorem atoms_shape (t x : RelativeTerm Nat) (hx : x ∈ thetaAtoms t) :
    ∃ k b, x = .theta k b := by
  revert hx
  induction t with
  | parameter p => intro hx; simp only [thetaAtoms, List.not_mem_nil] at hx
  | sum t u iht ihu =>
    intro hx
    exact (List.mem_append.mp hx).elim iht ihu
  | theta k b =>
    intro hx
    exact ⟨k, b, List.mem_singleton.mp hx⟩

theorem low_transform_lt_theta (a k : Nat) (ha : rootCheck a = true)
    (x t : RelativeTerm Nat) (hx : check 0 x = true) (hrx : Restricted a x)
    (hl : x.outerSort ≤ 1) (ht : NativeContext.check (alphaCode a) (.theta k t) = true) :
    NativeContext.denote (alphaCode a) (transform a x) < NativeContext.denote (alphaCode a) (.theta k t) := by
  have hv : NativeContext.denote (alphaCode a) (transform a x) < NativeContext.base (alphaCode a) := by
    rw [transform_low_value a ha x hx hrx hl, alpha_base a ha]
    exact restricted_low_below a ha x hx hrx hl
  exact hv.trans_le (((omegaSequence_strictMono (NativeContext.base (alphaCode a))).monotone
    (Nat.zero_le k)).trans (NativeContext.FixedPoint.checked_theta_range _ k t ht).1)

theorem shifted_theta_lt_positive_theta (a j k : Nat) (ha : rootCheck a = true)
    (u t : RelativeTerm Nat) (hu : check 0 (.theta (j + 1) u) = true)
    (hru : Restricted a (.theta (j + 1) u)) (hjk : j + 1 ≤ k)
    (ht : NativeContext.check (alphaCode a) (.theta k t) = true) :
    NativeContext.denote (alphaCode a) (transform a (.theta (j + 1) u)) <
      NativeContext.denote (alphaCode a) (.theta k t) := by
  have hc := transform_checked a ha (.theta (j + 1) u) hu hru
  rw [transform_theta_succ a j ha u hu hru] at hc ⊢
  exact (NativeContext.FixedPoint.checked_theta_range _ j _ hc).2.trans_le
    (((omegaSequence_strictMono (NativeContext.base (alphaCode a))).monotone hjk).trans
      (NativeContext.FixedPoint.checked_theta_range _ k t ht).1)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Enclosure
