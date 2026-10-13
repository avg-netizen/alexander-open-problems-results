import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingBounds
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingLastFactor
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingBranches

/-!
# Joint executing bounds for both printed additive branches

The actual append/insertion dispatcher derives a genuine tracker, the
all-entry upper bound, the final lower bound and the canonical final MNF
factor in one statement. These are the strengthened inductive conclusions
needed by the full factor-descent procedure. The recursive headword and
its honest bounds remain hypotheses to be derived there. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.BranchBounds

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Alexander313.Wilken.MultiplicativeNormalForm

theorem execute_spec (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation q head ≤ prefix)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    SourceTrackingRaw.trackingCheck q out = true ∧ out ≠ [] ∧
      interpretation q factor ≤ interpretation q (lastCode out) ∧
        (∀ d ∈ out, interpretation q d ≤ prefix * interpretation q factor) ∧
          lf (interpretation q (lastCode out)) = interpretation q factor := by
  have ht := Branches.execute_tracking q factor heads out hh hf hm hone hb ho
  refine ⟨ht, ((SourceTrackingRaw.trackingCheck_conditions q out).mp ht).1, ?_⟩
  rcases Branches.execute_branch q factor heads out ho with ⟨hc, he⟩ | ⟨hc, hi⟩
  · rw [he]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [lastCode_append_singleton] using
        (le_rfl : interpretation q factor ≤ interpretation q factor)
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact (hbound d hd).trans (Ordinal.le_mul_left prefix hm.1)
      · rw [List.mem_singleton.mp hd]
        exact Ordinal.le_mul_right _ hp
    · rw [lastCode_append_singleton]
      exact lf_multiplicative hm
  · have hs := Bounds.execute_bounds q factor heads out hh hf hm hb prefix hp hbound hi
    exact ⟨hs.2.1, hs.2.2, LastFactor.execute_last_factor q factor heads out hh hf hm hone hb hi⟩

theorem execute_last_bounds (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (prefix input : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation q head ≤ prefix)
    (hinput : input = prefix * interpretation q factor)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    SourceTrackingRaw.trackingCheck q out = true ∧
      interpretation q factor ≤ interpretation q (lastCode out) ∧
        interpretation q (lastCode out) ≤ input ∧
          (∀ d ∈ out, interpretation q d ≤ input) ∧
            lf (interpretation q (lastCode out)) = interpretation q factor := by
  have hs := execute_spec q factor heads out hh hf hm hone hb prefix hp hbound ho
  rw [hinput]
  exact ⟨hs.1, hs.2.2.1, hs.2.2.2.1 _ (lastCode_mem out hs.2.1),
    hs.2.2.2.1, hs.2.2.2.2⟩

theorem execute_prefix_last (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation q head ≤ prefix)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    interpretation q (lastCode out) =
      factorProduct (factorPrefix (canonicalMNF (interpretation q (lastCode out)))) * interpretation q factor := by
  have hs := execute_spec q factor heads out hh hf hm hone hb prefix hp hbound ho
  have ht := (SourceTrackingRaw.trackingCheck_conditions q out).mp hs.1
  simpa only [hs.2.2.2.2] using source_prefix_last ht.2.2.2.1 ht.2.2.2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.BranchBounds
