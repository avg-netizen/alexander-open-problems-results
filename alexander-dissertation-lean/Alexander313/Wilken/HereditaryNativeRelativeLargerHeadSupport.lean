import Alexander313.Wilken.HereditaryNativeIotaEnclosureSupport
import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapseSupport

/-!
# Actual support witness for a larger source head

An argument strictly above the original root argument cannot collapse to
the identical root value. If its collapse lies below that root, the actual
comparison theorem selects an exposed original subtree above the head
collapse and strictly below the root. Every subtree admission, Normality
and theta-zero shape follows from the original written root.

These are genuine source-support conclusions, without a localization or
relative-collapse oracle. The finite cutoff and executing HIGH recoder
remain separate. Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeLargerHeadSupport

open Iota.OrderInduction Iota.Enclosure ThetaCourse

/-- In the actual larger-argument case, the comparison law has precisely
its exposed-support alternative. -/
theorem above_argument_lt_iff_support (q k : Nat) (a c : RelativeTerm Nat)
    (ha : check q (.theta k a) = true) (hc : check q (.theta k c) = true)
    (hna : Comparison.Normal q a) (hnc : Comparison.Normal q c)
    (hac : denote q a < denote q c) :
    denote q (.theta k c) < denote q (.theta k a) ↔
      ∃ s ∈ exposedThetaList k a, denote q (.theta k c) ≤ denote q s := by
  constructor
  · intro h
    rcases (checked_theta_lt_iff_exposed q k c a hc ha hnc hna).mp h with hfirst | hsupport
    · exact False.elim ((not_lt_of_gt hac) hfirst.1)
    · exact hsupport
  · intro h
    exact (checked_theta_lt_iff_exposed q k c a hc ha hnc hna).mpr (Or.inr h)

/-- Equality is impossible here: the original root's own exposed support
is strictly smaller, so the reversed comparison would be strict. -/
theorem above_argument_le_iff_support (q k : Nat) (a c : RelativeTerm Nat)
    (ha : check q (.theta k a) = true) (hc : check q (.theta k c) = true)
    (hna : Comparison.Normal q a) (hnc : Comparison.Normal q c)
    (hac : denote q a < denote q c) :
    denote q (.theta k c) ≤ denote q (.theta k a) ↔
      ∃ s ∈ exposedThetaList k a, denote q (.theta k c) ≤ denote q s := by
  constructor
  · intro hle
    have hlt : denote q (.theta k c) < denote q (.theta k a) := by
      by_contra hn
      have he : denote q (.theta k c) = denote q (.theta k a) :=
        le_antisymm hle (le_of_not_gt hn)
      have hr : denote q (.theta k a) < denote q (.theta k c) :=
        (checked_theta_lt_iff_exposed q k a c ha hc hna hnc).mpr (Or.inl
          ⟨hac, fun s hs => (source_exposed_lt_root q k a s ha hna hs).trans_le he.symm.le⟩)
      exact (not_lt_of_ge hle) hr
    exact (above_argument_lt_iff_support q k a c ha hc hna hnc hac).mp hlt
  · intro h
    exact ((above_argument_lt_iff_support q k a c ha hc hna hnc hac).mpr h).le

/-- An actual original high root and checked Normal larger head derive a
genuine written Normal theta-zero support node strictly below the root. -/
theorem original_larger_head_support (q b c : Nat)
    (hb : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true)
    (hs : interpretation q c < omegaSequence (base q) 2)
    (habove : interpretation q (RootEndpointCollapse.argumentCode b) < interpretation q c)
    (hle : interpretation q (OmegaPowers.thetaCode c) ≤ interpretation q b) :
    ∃ s ∈ exposedThetaList 0 (rawTree (RootEndpointCollapse.argumentCode b)),
      check q s = true ∧ Comparison.Normal q s ∧
      interpretation q (OmegaPowers.thetaCode c) ≤ denote q s ∧
      denote q s < interpretation q b ∧ ∃ u, s = .theta 0 u := by
  have harg := (Comparison.acceptedCode_exact q _).mp
    (RootEndpointCollapse.argument_accepted q b hb)
  have hraw := (Comparison.acceptedCode_exact q c).mp hc
  have ht := SourceChi.Powers.checked_theta_zero q (rawTree c)
    (Arithmetic.raw_checked q c hraw.1) (by rw [Arithmetic.raw_value q c hraw.1]; exact hs)
  obtain ⟨a, he, ha, hna, hh⟩ := (RootLowCollapse.rootCheck_exact q b).mp hb
  have hearg : rawTree (RootEndpointCollapse.argumentCode b) = a := by
    simp only [RootEndpointCollapse.argumentCode, he, Localization.argumentCode_theta, rawTree_code]
  have hval : interpretation q b = denote q (.theta 0 a) := by rw [he, interpretation_code]
  have hhead : interpretation q (OmegaPowers.thetaCode c) = denote q (.theta 0 (rawTree c)) := by
    simp only [OmegaPowers.thetaCode, interpretation_code]
  have hac : denote q a < denote q (rawTree c) := by
    rw [← hearg, Arithmetic.raw_value q _ harg.1, Arithmetic.raw_value q c hraw.1]
    exact habove
  obtain ⟨s, hmem, hbound⟩ := (above_argument_le_iff_support q 0 a (rawTree c)
    ha ht hna hraw.2 hac).mp (by rw [← hhead, ← hval]; exact hle)
  have hchecked := exposed_checked_normal q 0 a s
    (FixedPoint.checked_theta_argument q 0 a ha) hna hmem
  refine ⟨s, by rw [hearg]; exact hmem, hchecked.1, hchecked.2, ?_, ?_, ?_⟩
  · rw [hhead]; exact hbound
  · rw [hval]; exact source_exposed_lt_root q 0 a s ha hna hmem
  · exact exposed_shape 0 a s hmem

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeLargerHeadSupport
