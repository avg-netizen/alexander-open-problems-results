import Alexander313.Wilken.MultiplicativeLastFactorProduct
import Alexander313.Wilken.SourceAdditiveTrackingWordBoundsSupport
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertionFidelity

/-!
# Genuine canonical final factor of the executing insertion

The actual raised M word ends at the factor and whole value recoding
preserves that final value. The actual singleton product has that same
canonical last MNF factor by real ordinal arithmetic. Actual greatest
insertion preserves the selected replacement final position. Thus every
executed output satisfies the printed normal-form terminal-factor clause.
No output factorization or last-value equality with the input is assumed.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.LastFactor

open NativeContext.SourceTrackingSequences
open Hereditary.SourceAdditiveTrackingWordBounds
open Alexander313.Wilken.MultiplicativeNormalForm

theorem conditional_last_factor (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute head factor) :
    lf (interpretation 0 (lastCode out)) = interpretation 0 factor := by
  have hs := ConditionalReplacement.execute_spec heads hh head factor hhead hf hm hb out ho
  rcases hs.2.2.2.2 with hraised | hsmall
  · have hr := (ConditionalReplacement.raised_member_caller heads hh head factor
      hhead hraised.1 hb).2
    obtain ⟨word, hw, he, ht, hv, hlen, hc⟩ :=
      Replacement.raisedReplacement_spec head factor out hr hf hm hraised.1 hraised.2
    have hsword := ReplacementSupport.raisedWord_spec head factor word hr hf hm hraised.1 hw
    rw [(lastCode_values_eq _ _ out word hs.1 hv).trans hsword.2.1]
    exact lf_multiplicative hm
  · obtain ⟨d, he, hv⟩ := hsmall.2
    rw [he, lastCode_singleton, hv]
    have hp := ConditionalReplacement.tracking_member_principal heads hh head hhead
    exact LastFactorProduct.lf_principal_mul _ _ hp.2.1 hp.2.2 hm hone

theorem execute_last_factor (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (ho : out ∈ Insertion.execute (factor, heads)) :
    lf (interpretation 0 (lastCode out)) = interpretation 0 factor := by
  obtain ⟨rows, hr, hheads, hout, hchecked, hbranch⟩ :=
    Insertion.execute_spec factor heads out hh hf hm hb ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hrow : ∀ row ∈ rows, lf (interpretation 0 (lastCode row.2)) = interpretation 0 factor := by
    intro row hmrow
    have hs := InsertionSupport.relation_members factor hrel row hmrow
    exact conditional_last_factor heads hh row.1 factor hs.1 hf hm hone hb row.2 hs.2
  rcases hbranch with ⟨first, rest, he, hword, hnone⟩ |
      ⟨before, current, after, hne, he, hword, hcover, hnone⟩
  · rw [hword]
    exact hrow first (by rw [he]; exact List.mem_cons_self)
  · have hc : current ∈ rows := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
    rw [hword, lastCode_append_nonempty _ _ (hchecked current hc).1]
    exact hrow current hc

/-- Both the canonical prefix and its final factor are the actual MNF
of the final output value. This is the printed NF assertion of 3.21.2. -/
theorem execute_prefix_last (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (ho : out ∈ Insertion.execute (factor, heads)) :
    interpretation 0 (lastCode out) =
      factorProduct (factorPrefix (canonicalMNF (interpretation 0 (lastCode out)))) *
        interpretation 0 factor := by
  have ht := (SourceTrackingRaw.trackingCheck_exact out).mp
    (InsertionFidelity.execute_tracking factor heads out hh hf hm hb ho)
  simpa only [execute_last_factor factor heads out hh hf hm hone hb ho] using
    source_prefix_last ht.2.2.2.1 ht.2.2.2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.LastFactor
