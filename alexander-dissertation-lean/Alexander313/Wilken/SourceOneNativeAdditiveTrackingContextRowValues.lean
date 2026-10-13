import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextConditionalValues
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertionSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueSupport
import Alexander313.Wilken.SourceAdditiveTrackingWordBoundsSupport

/-!
# Actual original-zero and lower-context replacement rows

Independently executing sequential replacement tables preserve their head
and complete replacement VALUES through the actual conditional agreement.
At a genuine lower RAW predecessor the actual parser and original OWN
interval give the real original mu identity, so the concrete cover checks
agree. An independently executed lower assignment derives every proper
predecessor's OWN caller from its ALL bound and the original tracker FINAL.
No chosen insertion position, mu column, whole assignment equality or
composition law is supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextRowValues

open NativeContext.SourceTrackingSequences (lastCode lastCode_mem)
open Hereditary.FinePredecessor (stripLast)

noncomputable def rowValues (row : InsertionSupport.Row) : Ordinal.{0} × List Ordinal.{0} :=
  (interpretation 0 row.1, row.2.map (interpretation 0))

/-- Actual chronological table relations derive every row value pair.
The real complete trackers and both factor-to-FINAL bounds are retained. -/
theorem relations_values_eq (q factor otherFactor : Nat) (full otherFull : List Nat)
    (hh : SourceTrackingRaw.trackingCheck full = true)
    (ht : NativeContext.SourceTrackingRaw.trackingCheck q otherFull = true)
    (hf : lowCheckCode 0 factor = true) (hg : NativeContext.lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode full))
    (hc : NativeContext.interpretation q otherFactor ≤ NativeContext.interpretation q (lastCode otherFull))
    (he : interpretation 0 factor = NativeContext.interpretation q otherFactor)
    (heads otherHeads : List Nat) (rows otherRows : List InsertionSupport.Row)
    (hs : ∀ a ∈ heads, a ∈ full) (hu : ∀ a ∈ otherHeads, a ∈ otherFull)
    (hv : heads.map (interpretation 0) = otherHeads.map (NativeContext.interpretation q))
    (hr : List.Forall₂ (InsertionSupport.Matches factor) heads rows)
    (ho : List.Forall₂ (NativeContext.SourceAdditiveTracking.InsertionSupport.Matches q otherFactor)
      otherHeads otherRows) :
    rows.map rowValues = otherRows.map (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues q) := by
  induction heads generalizing otherHeads rows otherRows with
  | nil =>
    cases hr
    have hn : otherHeads = [] := List.map_eq_nil_iff.mp hv.symm
    subst otherHeads
    cases ho
    rfl
  | cons a heads ih =>
    cases hr with
    | cons hrow hrest =>
      cases otherHeads with
      | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
      | cons b otherHeads =>
        cases ho with
        | cons hother htail =>
          have hvalues := List.cons.inj hv
          have hwords := ContextConditionalValues.conditional_values_eq q full otherFull hh ht
            a b factor otherFactor (hs a List.mem_cons_self) (hu b List.mem_cons_self)
            hf hg hm hb hc hvalues.1 he _ _
            (by simpa only [hrow.1] using hrow.2)
            (by simpa only [hother.1] using hother.2)
          have hrows := ih otherHeads _ _
            (fun d hd => hs d (List.mem_cons_of_mem _ hd))
            (fun d hd => hu d (List.mem_cons_of_mem _ hd)) hvalues.2 hrest htail
          simp only [List.map_cons, rowValues,
            NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues,
            hrow.1, hother.1, hvalues.1, hwords, hrows]

theorem executeRows_values_eq (q factor otherFactor : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (ht : NativeContext.SourceTrackingRaw.trackingCheck q otherHeads = true)
    (hf : lowCheckCode 0 factor = true) (hg : NativeContext.lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (hc : NativeContext.interpretation q otherFactor ≤ NativeContext.interpretation q (lastCode otherHeads))
    (he : interpretation 0 factor = NativeContext.interpretation q otherFactor)
    (hv : heads.map (interpretation 0) = otherHeads.map (NativeContext.interpretation q))
    (rows otherRows : List InsertionSupport.Row)
    (hr : rows ∈ InsertionSupport.executeRows factor heads)
    (ho : otherRows ∈ NativeContext.SourceAdditiveTracking.InsertionSupport.executeRows q otherFactor otherHeads) :
    rows.map rowValues = otherRows.map (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues q) :=
  relations_values_eq q factor otherFactor heads otherHeads hh ht hf hg hm hb hc he
    heads otherHeads rows otherRows (fun _ h => h) (fun _ h => h) hv
    (InsertionSupport.executeRows_relation factor heads rows hr)
    (NativeContext.SourceAdditiveTracking.InsertionSupport.executeRows_relation q otherFactor otherHeads otherRows ho)

/-- The actual lower RAW caller and OWN bound derive the original raw
caller and mu identity before either concrete cover checker is rewritten. -/
theorem coverCheck_eq (root previous returned current otherCurrent : Nat)
    (ha : Mu.inputCheck root = true)
    (hp : NativeContext.SourceTrackingRaw.Support.inputCheck (alphaCode root) previous = true)
    (hr : Replacement.EntryMatches (alphaCode root) previous returned)
    (hb : NativeContext.interpretation (alphaCode root) previous < Enclosure.sourceAlphaPlus root)
    (hc : lowCheckCode 0 current = true)
    (hd : NativeContext.lowCheckCode (alphaCode root) otherCurrent = true)
    (hv : interpretation 0 current = NativeContext.interpretation (alphaCode root) otherCurrent) :
    Insertion.coverCheck returned current =
      NativeContext.SourceAdditiveTracking.Insertion.coverCheck (alphaCode root) previous otherCurrent := by
  have hm := ContextAssignmentReturn.contextual_raw_entry root previous returned ha hp hr hb
  apply Bool.eq_iff_iff.mpr
  change (Insertion.coverCheck returned current = true) ↔
    (NativeContext.SourceAdditiveTracking.Insertion.coverCheck (alphaCode root) previous otherCurrent = true)
  rw [Insertion.coverCheck_exact, NativeContext.SourceAdditiveTracking.Insertion.coverCheck_exact]
  simp only [hm.1, hp, hc, hd, hv, hm.2]

/-- Every real proper entry of an independently executing lower assignment
derives its contextual original RAW mu, using only the original tracker
FINAL bound. Its returned entry may have any genuine original spelling. -/
theorem assignment_proper_mu (word : List Nat) (head input : Nat) (xs : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (hh : head ∈ stripLast word)
    (ho : xs ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode word))
    (c d : Nat) (hc : c ∈ stripLast xs)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) c d) :
    SourceTrackingRaw.Support.inputCheck d = true ∧ SourceTrackingRaw.Support.muValue d =
      NativeContext.SourceTrackingRaw.Support.muValue (ReplacementSupport.raisedBaseCode head) c := by
  have ht := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hhead := ht.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hn : stripLast word ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints word hw hn head hh
  have hs := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ xs).mp
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input xs ho)
  have hp := hs.2.1.nodes c hc
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input xs ho).2.1.2.1
  have hown := ((hall c (Hereditary.FinePredecessor.stripLast_mem _ _ hc)).trans hb).trans_lt hend
  have hm := ContextAssignmentReturn.contextual_raw_entry (SourceTrackingRaw.Support.rootCode head) c d
    hroot (by simpa only [he] using hp) (by simpa only [he] using hd)
    (by simpa only [he] using hown)
  simpa only [he] using hm

/-- At every actual proper lower predecessor, its literal original-zero
return has the same concrete cover flag. The finite return, RAW and OWN
callers are all consequences of the real assignment and original FINAL. -/
theorem assignment_returned_coverCheck_eq (word : List Nat) (head input : Nat) (xs : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (hh : head ∈ stripLast word)
    (ho : xs ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode word))
    (previous : Nat) (hp : previous ∈ stripLast xs) (current otherCurrent : Nat)
    (hc : lowCheckCode 0 current = true)
    (hd : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) otherCurrent = true)
    (hv : interpretation 0 current =
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherCurrent) :
    Insertion.coverCheck
        (SkSourcePathSupport.entryCode (ReplacementSupport.raisedBaseCode head) previous) current =
      NativeContext.SourceAdditiveTracking.Insertion.coverCheck
        (ReplacementSupport.raisedBaseCode head) previous otherCurrent := by
  have ht := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hs := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ xs).mp
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input xs ho)
  have hl := ((NativeContext.SourceTrackingRaw.trackingCheck_exact _ xs).mp
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input xs ho)).source_domain
  have hm := Hereditary.FinePredecessor.stripLast_mem _ _ hp
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input xs ho).2.1.2.1
  have hfinite := ((hall previous hm).trans hb).trans_lt
    (SourceTrackingRaw.Support.original_bound _ ht.2.2.1)
  have hr := SkSourcePathSupport.entryCode_spec _ previous (hl previous hm).1 hfinite
  have hmu := assignment_proper_mu word head input xs hw hh ho hb previous _ hp hr
  apply Bool.eq_iff_iff.mpr
  change (Insertion.coverCheck
      (SkSourcePathSupport.entryCode (ReplacementSupport.raisedBaseCode head) previous) current = true) ↔
    (NativeContext.SourceAdditiveTracking.Insertion.coverCheck
      (ReplacementSupport.raisedBaseCode head) previous otherCurrent = true)
  rw [Insertion.coverCheck_exact, NativeContext.SourceAdditiveTracking.Insertion.coverCheck_exact]
  simp only [hmu.1, hs.2.1.nodes previous hp, hc, hd, hv, hmu.2]

/-- The actual lower assignment and literal original-zero return derive
both complete tracker callers before independently executing the two row
tables. Only the original headword FINAL bound and real factor caller remain. -/
theorem assignment_executeRows_values_eq (word : List Nat) (head input : Nat) (xs : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (hh : head ∈ stripLast word)
    (ho : xs ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode word))
    (factor otherFactor : Nat)
    (hf : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) factor = true)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) factor))
    (hfactor : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) factor ≤
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) (lastCode xs))
    (rows otherRows : List InsertionSupport.Row)
    (hr : rows ∈ InsertionSupport.executeRows otherFactor (Replacement.returnWord head xs))
    (ht : otherRows ∈ NativeContext.SourceAdditiveTracking.InsertionSupport.executeRows
      (ReplacementSupport.raisedBaseCode head) factor xs) :
    rows.map rowValues = otherRows.map
      (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues (ReplacementSupport.raisedBaseCode head)) := by
  have hs := ContextAssignmentReturn.assignment_return word head input xs hw hh ho hb
  have hlower := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input xs ho
  have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq (interpretation 0)
    (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head))
    (Replacement.returnWord head xs) xs ((SourceTrackingRaw.trackingCheck_exact _).mp hs.1).1 hs.2.2.1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 otherFactor) := by
    rw [hd.2]; exact hm
  have hbound : interpretation 0 otherFactor ≤ interpretation 0 (lastCode (Replacement.returnWord head xs)) := by
    rw [hd.2, hlast]; exact hfactor
  exact executeRows_values_eq (ReplacementSupport.raisedBaseCode head) otherFactor factor
    (Replacement.returnWord head xs) xs hs.1 hlower ((Theta.acceptedLowCode_iff 0 _).mp hd.1).1
    hf hm' hbound hfactor hd.2 hs.2.2.1 rows otherRows hr ht

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextRowValues
