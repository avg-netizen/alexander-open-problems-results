import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextSelectionValues
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextAppendCheck

/-!
# Whole actual append-or-insert value covariance

Actual strict FIRST and the previous-entry test derive append eligibility
in both original and lower contexts. On the false branch, actual paired
replacement rows and genuine own-interval mu derive identical greatest
selection. Thus both independently executing source dispatchers preserve
the entire value word. The operational original-headword adapter derives
OWN and the returned tracking relation from real source return execution.
No full assignment composition or suffix-cut invariant is asserted.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextBranchValues

open PublicEpsilonUnboundedIota SourceTrackingSequences
open ReplacementFidelity (SameEntry)
open Hereditary.FinePredecessor (stripLast)

theorem branches_values_eq (q alpha input factor otherFactor : Nat)
    (heads returnedHeads word returnedWord : List Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (ho : heads ∈ Assignment.execute (betaCode q alpha) input)
    (hstrict : base (betaCode q alpha) < interpretation (betaCode q alpha) input)
    (hown : interpretation (betaCode q alpha) input < Enclosure.sourceAlphaPlus q alpha)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads returnedHeads)
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (betaCode q alpha) factor))
    (hb : interpretation (betaCode q alpha) factor ≤ interpretation (betaCode q alpha) (lastCode heads))
    (hs : word ∈ Branches.execute (((betaCode q alpha), factor), heads))
    (ht : returnedWord ∈ Branches.execute ((q, otherFactor), returnedHeads)) :
    returnedWord.map (interpretation q) = word.map (interpretation (betaCode q alpha)) := by
  have hc := ContextAppendCheck.assignment_appendCheck_eq q alpha input factor otherFactor
    heads returnedHeads ha ho hstrict hown hrel hf hd
  cases he : BranchesSupport.appendCheck (betaCode q alpha) factor heads with
  | true =>
    have htarget : BranchesSupport.appendCheck q otherFactor returnedHeads = true := hc.trans he
    have hword : word = heads ++ [factor] := by
      simpa only [Branches.execute, he, Bool.cond_true, Part.mem_some_iff] using hs
    have hreturned : returnedWord = returnedHeads ++ [otherFactor] := by
      simpa only [Branches.execute, htarget, Bool.cond_true, Part.mem_some_iff] using ht
    simp only [hword, hreturned, List.map_append, List.map_singleton,
      ContextRowValues.returned_values hrel, hd.2.2]
  | false =>
    have htarget : BranchesSupport.appendCheck q otherFactor returnedHeads = false := hc.trans he
    have hs' : word ∈ Insertion.execute (((betaCode q alpha), factor), heads) := by
      simpa only [Branches.execute, he, Bool.cond_false] using hs
    have ht' : returnedWord ∈ Insertion.execute ((q, otherFactor), returnedHeads) := by
      simpa only [Branches.execute, htarget, Bool.cond_false] using ht
    exact ContextSelectionValues.insertion_values_eq q alpha input factor otherFactor
      heads returnedHeads word returnedWord ha ho hown hrel hf hd hm hb hs' ht'

/-- The independently executing lower assignment is bounded by the actual
original headword FINAL. Every OWN interval and target caller follows from
the original checked tracker and its concrete finite source return. -/
theorem returned_branches_values_eq (q : Nat) (original : List Nat) (head input factor otherFactor : Nat)
    (heads returnedHeads word returnedWord : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (ho : heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hstrict : base (ReplacementSupport.raisedBaseCode q head) <
      interpretation (ReplacementSupport.raisedBaseCode q head) input)
    (hinput : interpretation (ReplacementSupport.raisedBaseCode q head) input ≤
      interpretation q (lastCode original))
    (hr : returnedHeads ∈ Replacement.returnWord q (ReplacementSupport.raisedBaseCode q head) heads)
    (hf : lowCheckCode (ReplacementSupport.raisedBaseCode q head) factor = true)
    (hd : SameEntry q (ReplacementSupport.raisedBaseCode q head) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (ReplacementSupport.raisedBaseCode q head) factor))
    (hb : interpretation (ReplacementSupport.raisedBaseCode q head) factor ≤
      interpretation (ReplacementSupport.raisedBaseCode q head) (lastCode heads))
    (hs : word ∈ Branches.execute (((ReplacementSupport.raisedBaseCode q head), factor), heads))
    (ht : returnedWord ∈ Branches.execute ((q, otherFactor), returnedHeads)) :
    returnedWord.map (interpretation q) = word.map (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
  have ht' := (SourceTrackingRaw.trackingCheck_conditions q original).mp hw
  have hhead := ht'.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec q head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_betaCode q head hhead
  have hne : stripLast original ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints q original hw hne head hh
  have hown := hinput.trans_lt hend
  have hreturn := ContextAssignmentReturn.assignment_return_spec q original head input heads returnedHeads
    hw hh ho hinput hr
  simpa only [he] using branches_values_eq q (SourceTrackingRaw.Support.rootCode q head)
    input factor otherFactor heads returnedHeads word returnedWord hroot
    (by simpa only [he] using ho) (by simpa only [he] using hstrict)
    (by simpa only [he] using hown) (by simpa only [he] using hreturn.2.1)
    (by simpa only [he] using hf) (by simpa only [he] using hd)
    (by simpa only [he] using hm) (by simpa only [he] using hb)
    (by simpa only [he] using hs) ht

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextBranchValues
