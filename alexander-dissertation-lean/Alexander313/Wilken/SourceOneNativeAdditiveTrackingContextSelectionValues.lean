import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextSelectorSupport

/-!
# Independently executing original-zero and lower-context insertions

Real chronological replacement executions derive every paired row's
admitted head, nonempty LOW replacement and chronological VALUES. Only
proper lower predecessors enter the actual OWN contextual mu theorem.
The original tracker FINAL and complete lower assignment bounds derive
those intervals, so the actual greatest insertion scan agrees in position
and VALUES. No returned tracker, selected index or composition is supplied.
Source-only uncompiled; original source parsing remains literal check zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextSelectionValues

open NativeContext.SourceTrackingSequences (lastCode)
open Hereditary.FinePredecessor (stripLast)
open ContextSelectorSupport (RowMatches)

private theorem selected_returned_head_values {q : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (Replacement.EntryMatches q) xs ys) :
    ys.map (interpretation 0) = xs.map (NativeContext.interpretation q) := by
  induction hr with
  | nil => rfl
  | cons hd ht ih => simp only [List.map_cons, hd.2, ih]

theorem relations_row_match (q factor otherFactor : Nat) (full otherFull : List Nat)
    (hh : SourceTrackingRaw.trackingCheck full = true)
    (ht : NativeContext.SourceTrackingRaw.trackingCheck q otherFull = true)
    (hf : lowCheckCode 0 factor = true) (hg : NativeContext.lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode full))
    (hc : NativeContext.interpretation q otherFactor ≤ NativeContext.interpretation q (lastCode otherFull))
    (he : interpretation 0 factor = NativeContext.interpretation q otherFactor)
    (heads otherHeads : List Nat) (rows otherRows : List InsertionSupport.Row)
    (hs : ∀ a ∈ heads, a ∈ full) (hu : ∀ a ∈ otherHeads, a ∈ otherFull)
    (hrel : List.Forall₂ (Replacement.EntryMatches q) otherHeads heads)
    (hr : List.Forall₂ (InsertionSupport.Matches factor) heads rows)
    (ho : List.Forall₂ (NativeContext.SourceAdditiveTracking.InsertionSupport.Matches q otherFactor)
      otherHeads otherRows) :
    List.Forall₂ (RowMatches q) rows otherRows := by
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation q otherFactor) := by rw [← he]; exact hm
  induction otherHeads generalizing heads rows otherRows with
  | nil =>
    cases hrel
    cases hr
    cases ho
    exact .nil
  | cons b otherHeads ih =>
    cases hrel with
    | cons hhead htail =>
      cases hr with
      | cons hrow hrest =>
        cases ho with
        | cons hother hotherRest =>
          have ha := ConditionalReplacement.execute_spec full hh _ factor
            (hs _ List.mem_cons_self) hf hm hb _ (by simpa only [hrow.1] using hrow.2)
          have hn := NativeContext.SourceAdditiveTracking.ConditionalReplacement.execute_spec
            q otherFull ht b otherFactor (hu b List.mem_cons_self) hg hm' hc _
            (by simpa only [hother.1] using hother.2)
          have hv := ContextConditionalValues.conditional_values_eq q full otherFull hh ht
            _ b factor otherFactor (hs _ List.mem_cons_self) (hu b List.mem_cons_self)
            hf hg hm hb hc hhead.2 he _ _
            (by simpa only [hrow.1] using hrow.2)
            (by simpa only [hother.1] using hother.2)
          refine .cons ?_ (ih _ _ _
            (fun c h => hs c (List.mem_cons_of_mem _ h))
            (fun c h => hu c (List.mem_cons_of_mem _ h)) htail hrest hotherRest)
          exact ⟨by simpa only [hrow.1, hother.1] using hhead, ha.1,
            fun c h => ((Theta.acceptedLowCode_iff 0 c).mp (ha.2.1 c h)).1,
            hn.1, fun c h => (hn.2.1 c h).1, hv⟩

/-- The complete actual lower assignment derives every proper row's RAW
and OWN caller. Both independently executing insertion words then agree. -/
theorem insertion_values_eq (root input factor otherFactor : Nat)
    (heads otherHeads word otherWord : List Nat)
    (ha : Mu.inputCheck root = true)
    (ho : otherHeads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode root) input)
    (hown : NativeContext.interpretation (alphaCode root) input < Enclosure.sourceAlphaPlus root)
    (hrel : List.Forall₂ (Replacement.EntryMatches (alphaCode root)) otherHeads heads)
    (hf : NativeContext.lowCheckCode (alphaCode root) otherFactor = true)
    (hd : Replacement.EntryMatches (alphaCode root) otherFactor factor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (alphaCode root) otherFactor))
    (hb : NativeContext.interpretation (alphaCode root) otherFactor ≤
      NativeContext.interpretation (alphaCode root) (lastCode otherHeads))
    (hs : word ∈ Insertion.execute (factor, heads))
    (ht : otherWord ∈ NativeContext.SourceAdditiveTracking.Insertion.execute
      (((alphaCode root), otherFactor), otherHeads)) :
    word.map (interpretation 0) = otherWord.map (NativeContext.interpretation (alphaCode root)) := by
  have hlower := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input otherHeads ho
  have hconditions := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ otherHeads).mp hlower
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input otherHeads ho).2.1.2.1
  have hbounds : ∀ c ∈ otherHeads,
      NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root :=
    fun c hc => (hall c hc).trans_lt hown
  have htarget := ContextAssignmentReturn.raw_tracking_return root ha otherHeads heads hlower hrel hbounds
  have hv := selected_returned_head_values hrel
  have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq (interpretation 0)
    (NativeContext.interpretation (alphaCode root)) heads otherHeads
    ((SourceTrackingRaw.trackingCheck_exact heads).mp htarget).1 hv
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor) := by
    rw [hd.2]; exact hm
  have hbound : interpretation 0 factor ≤ interpretation 0 (lastCode heads) := by
    rw [hd.2, hlast]; exact hb
  obtain ⟨rows, hr, rfl⟩ := (Part.mem_map_iff Insertion.word).mp hs
  obtain ⟨otherRows, hout, rfl⟩ :=
    (Part.mem_map_iff (NativeContext.SourceAdditiveTracking.Insertion.word (alphaCode root))).mp ht
  have hr' := InsertionSupport.executeRows_relation factor heads rows hr
  have ht' := NativeContext.SourceAdditiveTracking.InsertionSupport.executeRows_relation
    (alphaCode root) otherFactor otherHeads otherRows hout
  have hreturn := relations_row_match (alphaCode root) factor otherFactor heads otherHeads
    htarget hlower ((Theta.acceptedLowCode_iff 0 factor).mp hd.1).1 hf hm' hbound hb hd.2
    heads otherHeads rows otherRows (fun _ h => h) (fun _ h => h) hrel hr' ht'
  apply ContextSelectorSupport.insertion_word_values_eq root rows otherRows ha hreturn
  intro row hrow
  have hheads := NativeContext.SourceAdditiveTracking.InsertionSupport.relation_heads
    (alphaCode root) otherFactor ht'
  have hmember : row.1 ∈ stripLast otherHeads := by
    rw [← hheads]
    have hh : row.1 ∈ (stripLast otherRows).map Prod.fst := List.mem_map.mpr ⟨row, hrow, rfl⟩
    simpa only [stripLast, List.map_reverse, List.map_tail] using hh
  exact ⟨hconditions.2.1.nodes row.1 hmember,
    hbounds row.1 (Hereditary.FinePredecessor.stripLast_mem _ _ hmember)⟩

/-- The original checked tracker and its written proper head derive OWN
and the literal finite return before both actual insertions are compared. -/
theorem returned_insertion_values_eq (original : List Nat) (head input factor otherFactor : Nat)
    (heads word otherWord : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode original))
    (hf : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) otherFactor = true)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) otherFactor factor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor))
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor ≤
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) (lastCode heads))
    (hs : word ∈ Insertion.execute (factor, Replacement.returnWord head heads))
    (ht : otherWord ∈ NativeContext.SourceAdditiveTracking.Insertion.execute
      (((ReplacementSupport.raisedBaseCode head), otherFactor), heads)) :
    word.map (interpretation 0) =
      otherWord.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
  have ht' := (SourceTrackingRaw.trackingCheck_exact original).mp hw
  have hhead := ht'.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hne : stripLast original ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints original hw hne head hh
  have hown := hinput.trans_lt hend
  have hreturn := ContextAssignmentReturn.assignment_return original head input heads hw hh ho hinput
  simpa only [he] using insertion_values_eq (SourceTrackingRaw.Support.rootCode head)
    input factor otherFactor (Replacement.returnWord head heads) heads word otherWord hroot
    (by simpa only [he] using ho) (by simpa only [he] using hown)
    (by simpa only [he] using hreturn.2.1) (by simpa only [he] using hf)
    (by simpa only [he] using hd) (by simpa only [he] using hm)
    (by simpa only [he] using hb) hs (by simpa only [he] using ht)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextSelectionValues
