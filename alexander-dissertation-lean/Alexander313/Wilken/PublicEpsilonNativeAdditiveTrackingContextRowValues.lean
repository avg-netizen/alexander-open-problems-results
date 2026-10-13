import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextConditionalValues
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextAssignmentReturn

/-!
# Genuine cross-context row values and contextual cover tests

Each replacement row retains both actual tracker and factor-to-LAST callers.
Canonical raised inputs and real ordinary products derive row VALUE equality.
For an original head's actual lower context, the RAW root parser and genuine
OWN theorem derive each returned proper mu and hence its Boolean cover test.
The finite source-return relation derives the target tracker before it is
used as a row caller. No selected index, mu column or composition is assumed.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextRowValues

open PublicEpsilonUnboundedIota SourceTrackingSequences
open ReplacementFidelity (SameEntry)
open AssignmentValueSupport (rowValues)

theorem returned_values {q r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (SameEntry q r) xs ys) :
    ys.map (interpretation q) = xs.map (interpretation r) := by
  induction hr with
  | nil => rfl
  | cons hd ht ih => simp only [List.map_cons, hd.2.2, ih]

/-- Both genuinely executing chronological row lists retain their own
context callers; actual paired head VALUES derive every replacement VALUE. -/
theorem relations_values_eq (q r factor otherFactor : Nat) (full otherFull : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q full = true)
    (ht : SourceTrackingRaw.trackingCheck r otherFull = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode r otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode full))
    (hc : interpretation r otherFactor ≤ interpretation r (lastCode otherFull))
    (he : interpretation q factor = interpretation r otherFactor)
    (heads otherHeads : List Nat) (rows otherRows : List InsertionSupport.Row)
    (hs : ∀ a ∈ heads, a ∈ full) (hu : ∀ a ∈ otherHeads, a ∈ otherFull)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation r))
    (hr : List.Forall₂ (InsertionSupport.Matches q factor) heads rows)
    (ho : List.Forall₂ (InsertionSupport.Matches r otherFactor) otherHeads otherRows) :
    rows.map (rowValues q) = otherRows.map (rowValues r) := by
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
          have hwords := ContextConditionalValues.conditional_values_eq q r full otherFull hh ht
            a b factor otherFactor (hs a List.mem_cons_self) (hu b List.mem_cons_self)
            hf hg hm hb hc hvalues.1 he _ _
            (by simpa only [hrow.1] using hrow.2)
            (by simpa only [hother.1] using hother.2)
          have hrows := ih otherHeads _ _
            (fun d hd => hs d (List.mem_cons_of_mem _ hd))
            (fun d hd => hu d (List.mem_cons_of_mem _ hd)) hvalues.2 hrest htail
          simp only [List.map_cons, rowValues, hrow.1, hother.1, hvalues.1, hwords, hrows]

theorem executeRows_values_eq (q r factor otherFactor : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck r otherHeads = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode r otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : interpretation r otherFactor ≤ interpretation r (lastCode otherHeads))
    (he : interpretation q factor = interpretation r otherFactor)
    (hv : heads.map (interpretation q) = otherHeads.map (interpretation r))
    (rows otherRows : List InsertionSupport.Row)
    (hr : rows ∈ InsertionSupport.executeRows q factor heads)
    (ho : otherRows ∈ InsertionSupport.executeRows r otherFactor otherHeads) :
    rows.map (rowValues q) = otherRows.map (rowValues r) :=
  relations_values_eq q r factor otherFactor heads otherHeads hh ht hf hg hm hb hc he
    heads otherHeads rows otherRows (fun _ h => h) (fun _ h => h) hv
    (InsertionSupport.executeRows_relation q factor heads rows hr)
    (InsertionSupport.executeRows_relation r otherFactor otherHeads otherRows ho)

/-- The actual OWN contextual mu theorem derives the complete Boolean
cover identity at a proper raw lower-context row. The final row is not
asserted to have a RAW caller merely because its VALUES are returned. -/
theorem returned_cover_eq (q alpha source target current otherCurrent : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hs : SourceTrackingRaw.Support.inputCheck (betaCode q alpha) source = true)
    (hd : SameEntry q (betaCode q alpha) source target)
    (hb : interpretation (betaCode q alpha) source < Enclosure.sourceAlphaPlus q alpha)
    (hc : lowCheckCode (betaCode q alpha) current = true)
    (he : SameEntry q (betaCode q alpha) current otherCurrent) :
    Insertion.coverCheck q target otherCurrent =
      Insertion.coverCheck (betaCode q alpha) source current := by
  have hm := ContextAssignmentReturn.contextual_raw_entry q alpha source target ha hs hd hb
  apply Bool.eq_iff_iff.mpr
  change (Insertion.coverCheck q target otherCurrent = true) ↔
    Insertion.coverCheck (betaCode q alpha) source current = true
  rw [Insertion.coverCheck_exact, Insertion.coverCheck_exact]
  simp only [hm.1, hs, he.1, hc, he.2.2, hm.2, true_and]

/-- A real RAW lower tracker and its genuine finite original return derive
the dual executing row VALUE identity, including all target callers. -/
theorem returned_executeRows_values_eq (q alpha factor otherFactor : Nat)
    (heads returnedHeads : List Nat) (rows returnedRows : List InsertionSupport.Row)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hh : SourceTrackingRaw.trackingCheck (betaCode q alpha) heads = true)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads returnedHeads)
    (hown : ∀ c ∈ heads, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha)
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (betaCode q alpha) factor))
    (hb : interpretation (betaCode q alpha) factor ≤ interpretation (betaCode q alpha) (lastCode heads))
    (hr : rows ∈ InsertionSupport.executeRows (betaCode q alpha) factor heads)
    (ho : returnedRows ∈ InsertionSupport.executeRows q otherFactor returnedHeads) :
    returnedRows.map (rowValues q) = rows.map (rowValues (betaCode q alpha)) := by
  have ht := ContextAssignmentReturn.raw_tracking_return q alpha ha heads returnedHeads hh hrel hown
  have hv := returned_values hrel
  have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation (betaCode q alpha)) returnedHeads heads
    ((SourceTrackingRaw.trackingCheck_conditions q returnedHeads).mp ht).1 hv
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q otherFactor) := by
    rw [hd.2.2]; exact hm
  have hbound : interpretation q otherFactor ≤ interpretation q (lastCode returnedHeads) := by
    rw [hd.2.2, hlast]; exact hb
  exact executeRows_values_eq q (betaCode q alpha) otherFactor factor returnedHeads heads
    ht hh hd.1 hf hm' hbound hb hd.2.2 hv returnedRows rows ho hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextRowValues
