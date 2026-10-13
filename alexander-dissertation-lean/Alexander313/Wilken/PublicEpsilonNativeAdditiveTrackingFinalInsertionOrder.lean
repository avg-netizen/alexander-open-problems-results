import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFinalInsertionOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingIntervalFactors

/-!
# Strict order on the actual final insertion of a multiplicative child

The independently executing greater assignment has a genuine M child.
Its actual false-append table selects its final row, witnessed by the
computed index and table length. That row is the ordinary child*factor
singleton, while its actual retained prefix has an independent M execution.
The computed cover derives the smaller direct-cover caller; below or at
the retained endpoint the genuine M comparison or same-value theorem applies.
Earlier selected raised rows and full nonM-right order remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FinalInsertionOrder

open PublicEpsilonUnboundedIota SourceTrackingSequences
open InsertionSupport (Row)
open FinalInsertionOrderSupport

theorem execute_final_insertion_lex (q left greater prefix factor : Nat)
    (rows : List Row) (n : Nat) (replacement out other : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q greater)
    (hm : SourceMultiplicativePrincipal.inputCheck q prefix = true)
    (happend : BranchesSupport.appendCheck q factor
      (SourceMultiplicativeTracking.rawWord q prefix) = false)
    (hr : rows ∈ InsertionSupport.executeRows q factor
      (SourceMultiplicativeTracking.rawWord q prefix))
    (hs : Insertion.choose q rows = some (n, replacement))
    (hn : n + 1 = rows.length)
    (hlt : interpretation q left < interpretation q greater)
    (ho : out ∈ Assignment.execute q left)
    (ht : other ∈ Assignment.execute q greater) :
    List.Lex (· < ·) (out.map (interpretation q)) (other.map (interpretation q)) := by
  obtain ⟨_, _, _, hlow, _, _, _, _, hmul, _, hproduct, _, _⟩ :=
    Factor.execute_spec q greater (prefix, factor) hf
  have hsmall := Factor.Bounds.execute_last_le_prefix q greater (prefix, factor) hf
  have hchild := Assignment.execute_multiplicative q prefix hm
  have htrack := (Assignment.execute_spec q prefix _ hchild).2.1.1
  obtain ⟨heads, hh, hb⟩ := IntervalFactors.actual_factor_child q greater prefix factor other hf ht
  have he : heads = SourceMultiplicativeTracking.rawWord q prefix := Part.mem_unique hh hchild
  subst heads
  have hins : other ∈ Insertion.execute
      ((q, factor), SourceMultiplicativeTracking.rawWord q prefix) := by
    simpa only [Branches.execute, happend, Bool.cond_false] using hb
  have hout : other = Insertion.word q rows :=
    Part.mem_unique hins (Part.mem_map (Insertion.word q) hr)
  obtain ⟨before, current, hne, hrows, hreplacement, hword, hcover⟩ :=
    choose_final q rows n replacement hs hn
  have hrel := InsertionSupport.executeRows_relation q factor _ rows hr
  have hmap := InsertionSupport.relation_heads q factor hrel
  have hlast : current.1 = prefix := by
    calc
      current.1 = lastCode (SourceMultiplicativeTracking.rawWord q prefix) := by
        rw [← hmap, hrows, List.map_append, List.map_singleton, lastCode_append_singleton]
      _ = prefix := SourceMultiplicativeTracking.rawWord_last q prefix
  have hshape : SourceMultiplicativeTracking.rawWord q prefix =
      before.map Prod.fst ++ [prefix] := by
    simpa only [hrows, List.map_append, List.map_singleton, hlast] using hmap.symm
  have hbne : before.map Prod.fst ≠ [] := fun he => hne (List.map_eq_nil_iff.mp he)
  have hrow : current ∈ rows := by
    rw [hrows]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hcond : current.2 ∈ ConditionalReplacement.execute q prefix factor := by
    simpa only [hlast] using (InsertionSupport.relation_members q factor hrel current hrow).2
  have hpne := Assignment.execute_nonempty q prefix _ hchild
  have hbound : interpretation q factor ≤
      interpretation q (lastCode (SourceMultiplicativeTracking.rawWord q prefix)) := by
    simpa only [SourceMultiplicativeTracking.rawWord_last] using hsmall
  obtain ⟨d, hd, hdLow, hv⟩ := EpsilonSingletonIntervalOrderSupport.conditional_small
    q (SourceMultiplicativeTracking.rawWord q prefix) htrack prefix factor
    (by simpa only [SourceMultiplicativeTracking.rawWord_last] using
      lastCode_mem (SourceMultiplicativeTracking.rawWord q prefix) hpne)
    hlow hmul hbound hsmall current.2 hcond
  have hdValue : interpretation q d = interpretation q greater := hv.trans hproduct.symm
  have hc := (Insertion.coverCheck_exact q _ _).mp hcover
  have hge : interpretation q greater ≤
      SourceTrackingRaw.Support.muValue q (lastCode (before.map Prod.fst)) := by
    simpa only [hd, Insertion.firstCode, List.head?_cons, Option.getD_some, hdValue] using hc.2.2
  obtain ⟨hraw, hmb, initial, hi, hiv⟩ :=
    retained_prefix_execution q prefix (before.map Prod.fst) hm hbne hshape
  have hother : other.map (interpretation q) =
      (before.map Prod.fst).map (interpretation q) ++ [interpretation q greater] := by
    rw [hout, hword, hd, List.map_append, List.map_singleton, hdValue]
  rw [hother]
  by_cases hbefore : interpretation q left < interpretation q (lastCode (before.map Prod.fst))
  · have hlex := AssignmentCoverPrefix.execute_right_multiplicative_lex q left
      (lastCode (before.map Prod.fst)) out initial hmb hbefore ho hi
    rw [hiv] at hlex
    exact List.Lex.append_right (· < ·) [interpretation q greater] hlex
  · have hble : interpretation q (lastCode (before.map Prod.fst)) ≤ interpretation q left :=
      le_of_not_gt hbefore
    by_cases heq : interpretation q left = interpretation q (lastCode (before.map Prod.fst))
    · have hvalues := Assignment.ValueInvariance.execute_values_eq q left
        (lastCode (before.map Prod.fst)) out initial ho hi heq
      rw [hvalues, hiv]
      simpa only [List.append_nil] using List.Lex.append_left (· < ·)
        (show List.Lex (· < ·) [] [interpretation q greater] from .nil)
        ((before.map Prod.fst).map (interpretation q))
    · have hbl : interpretation q (lastCode (before.map Prod.fst)) < interpretation q left :=
        lt_of_le_of_ne hble (Ne.symm heq)
      have hprefix := execute_raw_cover_prefix q (lastCode (before.map Prod.fst)) left
        initial out hraw hbl (hlt.le.trans hge) hi ho
      rw [hiv] at hprefix
      exact SourceMultiplicativeTracking.OrderSupport.prefix_lex_singleton _ _ _ hprefix
        (fun a ha => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
          exact ((Assignment.execute_spec q left out ho).2.1.2.1 c hc).trans_lt hlt)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FinalInsertionOrder
