import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextInsertionCutSupport
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextBranchValues

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

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextBranchesCut

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceAdditiveTracking.InsertionFidelitySupport (stripLast_append_nonempty)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)
open Hereditary.SourceAdditiveTrackingWordBounds (lastCode_append_nonempty)

/-- The actual singleton FIRST link supplies both strict floors. With two
or more suffix entries the literal previous code is unchanged. -/
theorem appendCheck_at_cut (factor : Nat) (before : List Nat) (first : Nat)
    (rest : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (before ++ first :: rest) = true)
    (ht : SourceTrackingRaw.trackingCheck (first :: rest) = true)
    (hfront : interpretation 0 (lastCode before) < interpretation 0 first) :
    BranchesSupport.appendCheck factor (before ++ first :: rest) =
      BranchesSupport.appendCheck factor (first :: rest) := by
  have hlast : lastCode (before ++ first :: rest) = lastCode (first :: rest) :=
    lastCode_append_nonempty _ _ (List.cons_ne_nil _ _)
  apply Bool.eq_iff_iff.mpr
  rw [BranchesSupport.appendCheck_exact factor _ hh,
    BranchesSupport.appendCheck_exact factor _ ht]
  cases rest with
  | nil =>
    have hstrip : stripLast (before ++ [first]) = before := stripLast_append_singleton _ _
    have hn := (SourceTrackingRaw.trackingCheck_exact (before ++ [first])).mp hh
    have hraw := hn.2.1.nodes (lastCode before) (by
      rw [hstrip]
      exact lastCode_mem before hne)
    have hbase := ((SourceTrackingRaw.Support.inputCheck_exact _).mp hraw).2.1.trans hfront
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
theorem branches_covered_cut (factor : Nat) (before : List Nat) (first : Nat)
    (rest out : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (before ++ first :: rest) = true)
    (ht : SourceTrackingRaw.trackingCheck (first :: rest) = true)
    (hfront : interpretation 0 (lastCode before) < interpretation 0 first)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode (before ++ first :: rest)))
    (eta : Ordinal.{0}) (heta : 0 < eta)
    (hbound : ∀ c ∈ before ++ first :: rest, interpretation 0 c ≤ eta)
    (hraw : SourceTrackingRaw.Support.inputCheck (lastCode before) = true)
    (hcover : eta * interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue (lastCode before))
    (ho : out ∈ Branches.execute (factor, before ++ first :: rest)) :
    ∃ suffix, suffix ∈ Branches.execute (factor, first :: rest) ∧
      out = before ++ suffix := by
  have hflag := appendCheck_at_cut factor before first rest hne hh ht hfront
  rcases Branches.execute_branch factor (before ++ first :: rest) out ho with
    ⟨ha, he⟩ | ⟨ha, hi⟩
  · have hsflag : BranchesSupport.appendCheck factor (first :: rest) = true := hflag.symm.trans ha
    refine ⟨(first :: rest) ++ [factor], ?_, ?_⟩
    · simpa only [Branches.execute, hsflag, Bool.cond_true] using
        Part.mem_some ((first :: rest) ++ [factor])
    · simpa only [List.append_assoc] using he
  · have hsflag : BranchesSupport.appendCheck factor (first :: rest) = false := hflag.symm.trans ha
    obtain ⟨suffix, hs, he⟩ := ContextInsertionCutSupport.insertion_covered_cut factor
      before first rest out hne hh hf hm hb eta heta hbound hraw hcover hi
    exact ⟨suffix, by simpa only [Branches.execute, hsflag, Bool.cond_false] using hs, he⟩

/-- The genuine lower Assignment, original tracker FINAL and literal finite
return derive the suffix tracker, strict FIRST and every actual update caller.
The covered source dispatcher then agrees with the independently executing
lower branch in VALUES, preceded by the unchanged written original prefix.
The real lower input is retained; no residual-only substitution is made. -/
theorem returned_contextual_update_at_cut (original : List Nat)
    (head input factor otherFactor : Nat) (before heads word out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true)
    (hh : head ∈ stripLast original)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode original))
    (hne : before ≠ [])
    (hfull : SourceTrackingRaw.trackingCheck (before ++ Replacement.returnWord head heads) = true)
    (hbefore : ∀ c ∈ before, interpretation 0 c ≤ interpretation 0 head)
    (hf : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) otherFactor = true)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) otherFactor factor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor))
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor ≤
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) (lastCode heads))
    (hcover : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input *
      interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue (lastCode before))
    (ht : word ∈ NativeContext.SourceAdditiveTracking.Branches.execute
      ((ReplacementSupport.raisedBaseCode head, otherFactor), heads))
    (hu : out ∈ Branches.execute (factor, before ++ Replacement.returnWord head heads)) :
    out.map (interpretation 0) = before.map (interpretation 0) ++
      word.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
  have horiginal := (SourceTrackingRaw.trackingCheck_exact original).mp hw
  have hhead := horiginal.2.1.nodes head hh
  have hheadSpec := (SourceTrackingRaw.Support.inputCheck_exact head).mp hhead
  have hbase := (ReplacementSupport.raisedBaseCode_spec head hhead).2.1
  have hreturn := ContextAssignmentReturn.assignment_return original head input heads hw hh ho hinput
  have hreturnedNe := ((SourceTrackingRaw.trackingCheck_exact _).mp hreturn.1).1
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input heads ho).2.1.2.1
  have hpos : 0 < NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input :=
    (zero_lt_one.trans hheadSpec.2.1).trans (by simpa only [hbase] using hstrict)
  have hbound : ∀ c ∈ before ++ Replacement.returnWord head heads,
      interpretation 0 c ≤ NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (hbefore c hc).trans (by simpa only [hbase] using hstrict.le)
    · have hmapped : interpretation 0 c ∈ heads.map
          (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
        rw [← hreturn.2.2.1]
        exact List.mem_map_of_mem hc
      obtain ⟨d, hdmem, he⟩ := List.mem_map.mp hmapped
      rw [← he]
      exact hall d hdmem
  have hraw : SourceTrackingRaw.Support.inputCheck (lastCode before) = true := by
    apply ((SourceTrackingRaw.trackingCheck_exact _).mp hfull).2.1.nodes
    rw [stripLast_append_nonempty before _ hreturnedNe]
    exact List.mem_append_left _ (lastCode_mem before hne)
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation 0) (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head))
    (Replacement.returnWord head heads) heads hreturnedNe hreturn.2.2.1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor) := by
    rw [hd.2]
    exact hm
  have hb' : interpretation 0 factor ≤ interpretation 0
      (lastCode (before ++ Replacement.returnWord head heads)) := by
    rw [lastCode_append_nonempty before _ hreturnedNe, hd.2, hlast]
    exact hb
  obtain ⟨first, rest, hheads⟩ := List.exists_cons_of_ne_nil
    (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty _ input heads ho)
  have hr := hreturn.2.1
  rw [hheads] at hr
  obtain ⟨other, otherRest, hfirst, htail, hreturned⟩ := List.forall₂_cons_left_iff.mp hr
  have hfirstStrict := NativeContext.SourceAdditiveTracking.AssignmentFirst.execute_first_gt_base
    _ input first rest (by simpa only [hheads] using ho) hstrict
  have hfront : interpretation 0 (lastCode before) < interpretation 0 other := by
    rw [hfirst.2]
    exact (by simpa only [hbase] using hbefore _ (lastCode_mem before hne)).trans_lt hfirstStrict
  obtain ⟨suffix, hsuffix, hcut⟩ := branches_covered_cut factor before other otherRest out hne
    (by simpa only [hreturned] using hfull) (by simpa only [hreturned] using hreturn.1)
    hfront ((Theta.acceptedLowCode_iff 0 factor).mp hd.1).1 hm'
    (by simpa only [hreturned] using hb')
    (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) hpos
    (by simpa only [hreturned] using hbound) hraw hcover
    (by simpa only [hreturned] using hu)
  have hv := ContextBranchValues.returned_branches_values_eq original head input factor otherFactor
    heads suffix word hw hh ho hstrict hinput hf hd hm hb
    (by simpa only [hreturned] using hsuffix) ht
  simp only [hcut, List.map_append, hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextBranchesCut
