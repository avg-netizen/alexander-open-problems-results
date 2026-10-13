import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextInsertionCutSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextBranchValues

/-!
# Actual branch dispatch retains a genuinely covered source cut

The real strict FIRST link makes the append test independent of an earlier
literal reference prefix. A true append therefore acts on the suffix alone.
For false append, actual conditional output bounds derive the passing cut,
and the genuine finite table reconstruction gives an independently executing
suffix insertion. Thus both printed branch alternatives expose the same
suffix dispatcher, without a supplied suffix execution or composition law.
Whole contextual Assignment accumulation remains separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextBranchCutSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open InsertionFidelitySupport (stripLast_append_nonempty)
open PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)
open Hereditary.SourceAdditiveTrackingWordBounds (lastCode_append_nonempty)
open ReplacementFidelity (SameEntry)

/-- The actual singleton FIRST link supplies both strict floors. With two
or more suffix entries the literal previous code is unchanged. -/
theorem appendCheck_at_cut (q factor : Nat) (before : List Nat) (first : Nat)
    (rest : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ first :: rest) = true)
    (ht : SourceTrackingRaw.trackingCheck q (first :: rest) = true)
    (hfront : interpretation q (lastCode before) < interpretation q first) :
    BranchesSupport.appendCheck q factor (before ++ first :: rest) =
      BranchesSupport.appendCheck q factor (first :: rest) := by
  have hlast : lastCode (before ++ first :: rest) = lastCode (first :: rest) :=
    lastCode_append_nonempty _ _ (List.cons_ne_nil _ _)
  apply Bool.eq_iff_iff.mpr
  rw [BranchesSupport.appendCheck_exact q factor _ hh,
    BranchesSupport.appendCheck_exact q factor _ ht]
  cases rest with
  | nil =>
    have hstrip : stripLast (before ++ [first]) = before := stripLast_append_singleton _ _
    have hn := (SourceTrackingRaw.trackingCheck_conditions q (before ++ [first])).mp hh
    have hraw := hn.2.1.nodes (lastCode before) (by
      rw [hstrip]
      exact lastCode_mem before hne)
    have hbase := ((SourceTrackingRaw.Support.inputCheck_exact q _).mp hraw).2.1.trans hfront
    simp only [hlast, hstrip, stripLast_singleton, if_neg hne, if_pos rfl,
      lastCode_singleton, hfront, hbase, true_and]
  | cons next rest =>
    have hstripne : stripLast (first :: next :: rest) ≠ [] := by
      rw [stripLast_cons_nonempty first (next :: rest) (List.cons_ne_nil _ _)]
      exact List.cons_ne_nil _ _
    have hstrip : stripLast (before ++ first :: next :: rest) =
        before ++ stripLast (first :: next :: rest) :=
      stripLast_append_nonempty before _ (List.cons_ne_nil _ _)
    have hfullne : before ++ stripLast (first :: next :: rest) ≠ [] := by
      intro he
      exact hstripne (List.append_eq_nil_iff.mp he).2
    simp only [hlast, hstrip, if_neg hfullne, if_neg hstripne,
      lastCode_append_nonempty before _ hstripne]

/-- Actual full branch execution and its genuine source bounds construct
an independent suffix branch execution with the literal retained prefix. -/
theorem branches_covered_cut (q factor : Nat) (before : List Nat) (first : Nat)
    (rest out : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ first :: rest) = true)
    (ht : SourceTrackingRaw.trackingCheck q (first :: rest) = true)
    (hfront : interpretation q (lastCode before) < interpretation q first)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode (before ++ first :: rest)))
    (eta : Ordinal.{0}) (heta : 0 < eta)
    (hbound : ∀ c ∈ before ++ first :: rest, interpretation q c ≤ eta)
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hcover : eta * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q (lastCode before))
    (ho : out ∈ Branches.execute ((q, factor), before ++ first :: rest)) :
    ∃ suffix, suffix ∈ Branches.execute ((q, factor), first :: rest) ∧
      out = before ++ suffix := by
  have hflag := appendCheck_at_cut q factor before first rest hne hh ht hfront
  rcases Branches.execute_branch q factor (before ++ first :: rest) out ho with
    ⟨ha, he⟩ | ⟨ha, hi⟩
  · have hsflag : BranchesSupport.appendCheck q factor (first :: rest) = true := hflag.symm.trans ha
    refine ⟨(first :: rest) ++ [factor], ?_, ?_⟩
    · simpa only [Branches.execute, hsflag, Bool.cond_true] using
        Part.mem_some ((first :: rest) ++ [factor])
    · simpa only [List.append_assoc] using he
  · have hsflag : BranchesSupport.appendCheck q factor (first :: rest) = false := hflag.symm.trans ha
    obtain ⟨suffix, hs, he⟩ := ContextInsertionCutSupport.insertion_covered_cut q factor
      before first rest out hne hh hf hm hb eta heta hbound hraw hcover hi
    exact ⟨suffix, by simpa only [Branches.execute, hsflag, Bool.cond_false] using hs, he⟩

/-- A genuine independently executing lower Assignment derives the target
RAW suffix and strict FIRST. The actual full branch then retains the cut
and performs exactly the lower branch update in VALUES. -/
theorem contextual_update_at_cut (q alpha input factor otherFactor : Nat)
    (before heads returnedHeads word out : List Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (ho : heads ∈ Assignment.execute (betaCode q alpha) input)
    (hstrict : base (betaCode q alpha) < interpretation (betaCode q alpha) input)
    (hown : interpretation (betaCode q alpha) input < Enclosure.sourceAlphaPlus q alpha)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads returnedHeads)
    (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ returnedHeads) = true)
    (hbefore : interpretation q (lastCode before) < base (betaCode q alpha))
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (betaCode q alpha) factor))
    (hb : interpretation (betaCode q alpha) factor ≤
      interpretation (betaCode q alpha) (lastCode heads))
    (eta : Ordinal.{0}) (heta : 0 < eta)
    (hbound : ∀ c ∈ before ++ returnedHeads, interpretation q c ≤ eta)
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hcover : eta * interpretation q otherFactor ≤ SourceTrackingRaw.Support.muValue q (lastCode before))
    (hw : word ∈ Branches.execute (((betaCode q alpha), factor), heads))
    (hu : out ∈ Branches.execute ((q, otherFactor), before ++ returnedHeads)) :
    out.map (interpretation q) = before.map (interpretation q) ++
      word.map (interpretation (betaCode q alpha)) := by
  have hlower := Assignment.execute_tracking _ input heads ho
  have hall := (Assignment.execute_spec _ input heads ho).2.1.2.1
  have htarget := ContextAssignmentReturn.raw_tracking_return q alpha ha heads returnedHeads
    hlower hrel (fun c hc => (hall c hc).trans_lt hown)
  have hreturnedNe := ((SourceTrackingRaw.trackingCheck_conditions q returnedHeads).mp htarget).1
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation (betaCode q alpha)) returnedHeads heads hreturnedNe
      (ContextRowValues.returned_values hrel)
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q otherFactor) := by
    rw [hd.2.2]
    exact hm
  have hb' : interpretation q otherFactor ≤ interpretation q (lastCode (before ++ returnedHeads)) := by
    rw [lastCode_append_nonempty before returnedHeads hreturnedNe, hd.2.2, hlast]
    exact hb
  obtain ⟨first, rest, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty _ input heads ho)
  have hr := hrel
  rw [hheads] at hr
  obtain ⟨other, otherRest, hfirst, htail, hreturned⟩ := List.forall₂_cons_left_iff.mp hr
  have hfirstStrict := AssignmentFirst.execute_first_gt_base _ input first rest
    (by simpa only [hheads] using ho) hstrict
  have hfront : interpretation q (lastCode before) < interpretation q other := by
    rw [hfirst.2.2]
    exact hbefore.trans hfirstStrict
  obtain ⟨suffix, hsuffix, hcut⟩ := branches_covered_cut q otherFactor before other otherRest out hne
    (by simpa only [hreturned] using hh) (by simpa only [hreturned] using htarget) hfront hd.1 hm'
    (by simpa only [hreturned] using hb') eta heta
    (by simpa only [hreturned] using hbound) hraw hcover
    (by simpa only [hreturned] using hu)
  have hv := ContextBranchValues.branches_values_eq q alpha input factor otherFactor
    heads returnedHeads word suffix ha ho hstrict hown hrel hf hd hm hb hw
      (by simpa only [hreturned] using hsuffix)
  simp only [hcut, List.map_append, hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextBranchCutSupport
