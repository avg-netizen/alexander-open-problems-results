import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBounds
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingLastFactor
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBranches

/-!
# Joint executing bounds for both printed additive branches

The actual append/insertion dispatcher derives a genuine tracker, the
all-entry upper bound, the final lower bound and the canonical final MNF
factor in one statement. These are the strengthened inductive conclusions
needed by the full factor-descent procedure. The recursive headword and
its honest bounds remain hypotheses to be derived there. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.BranchBounds

open NativeContext.SourceTrackingSequences
open Alexander313.Wilken.MultiplicativeNormalForm

theorem execute_spec (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation 0 head ≤ prefix)
    (ho : out ∈ Branches.execute (factor, heads)) :
    SourceTrackingRaw.trackingCheck out = true ∧ out ≠ [] ∧
      interpretation 0 factor ≤ interpretation 0 (lastCode out) ∧
        (∀ d ∈ out, interpretation 0 d ≤ prefix * interpretation 0 factor) ∧
          lf (interpretation 0 (lastCode out)) = interpretation 0 factor := by
  have ht := Branches.execute_tracking factor heads out hh hf hm hone hb ho
  refine ⟨ht, ((SourceTrackingRaw.trackingCheck_exact out).mp ht).1, ?_⟩
  rcases Branches.execute_branch factor heads out ho with ⟨hc, he⟩ | ⟨hc, hi⟩
  · rw [he]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [lastCode_append_singleton] using
        (le_rfl : interpretation 0 factor ≤ interpretation 0 factor)
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact (hbound d hd).trans (Ordinal.le_mul_left prefix hm.1)
      · rw [List.mem_singleton.mp hd]
        exact Ordinal.le_mul_right _ hp
    · rw [lastCode_append_singleton]
      exact lf_multiplicative hm
  · have hs := Bounds.execute_bounds factor heads out hh hf hm hb prefix hp hbound hi
    exact ⟨hs.2.1, hs.2.2, LastFactor.execute_last_factor factor heads out hh hf hm hone hb hi⟩

theorem execute_last_bounds (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (prefix input : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation 0 head ≤ prefix)
    (hinput : input = prefix * interpretation 0 factor)
    (ho : out ∈ Branches.execute (factor, heads)) :
    SourceTrackingRaw.trackingCheck out = true ∧
      interpretation 0 factor ≤ interpretation 0 (lastCode out) ∧
        interpretation 0 (lastCode out) ≤ input ∧
          (∀ d ∈ out, interpretation 0 d ≤ input) ∧
            lf (interpretation 0 (lastCode out)) = interpretation 0 factor := by
  have hs := execute_spec factor heads out hh hf hm hone hb prefix hp hbound ho
  rw [hinput]
  exact ⟨hs.1, hs.2.2.1, hs.2.2.2.1 _ (lastCode_mem out hs.2.1),
    hs.2.2.2.1, hs.2.2.2.2⟩

theorem execute_prefix_last (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation 0 head ≤ prefix)
    (ho : out ∈ Branches.execute (factor, heads)) :
    interpretation 0 (lastCode out) =
      factorProduct (factorPrefix (canonicalMNF (interpretation 0 (lastCode out)))) * interpretation 0 factor := by
  have hs := execute_spec factor heads out hh hf hm hone hb prefix hp hbound ho
  have ht := (SourceTrackingRaw.trackingCheck_exact out).mp hs.1
  simpa only [hs.2.2.2.2] using source_prefix_last ht.2.2.2.1 ht.2.2.2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.BranchBounds
