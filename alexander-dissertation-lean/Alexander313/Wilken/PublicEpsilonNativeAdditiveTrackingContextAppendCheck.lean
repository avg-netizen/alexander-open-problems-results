import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextRowValues
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentFirst

/-!
# Genuine append-guard covariance of an actual lower-context assignment

RAW proper entries have genuine contextual mu returns. The final entry may
lie below the lower base, so its two RAW guards are not identified wholesale.
The true previous-entry comparison forces every eligible final epsilon above
that lower base. At a singleton, strict FIRST is derived from actual execution
above the lower base. These actual callers derive both directions of the
append Boolean identity. No branch-composition or assignment equality is
asserted. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAppendCheck

open PublicEpsilonUnboundedIota SourceTrackingSequences
open ReplacementFidelity (SameEntry)
open Hereditary.FinePredecessor (stripLast stripLast_split)

private theorem append_return_relation_last {q r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (SameEntry q r) xs ys) (hne : xs ≠ []) :
    SameEntry q r (lastCode xs) (lastCode ys) := by
  revert hne
  induction hr with
  | nil => intro hn; exact False.elim (hn rfl)
  | @cons c d xs ys hd ht ih =>
    intro hn
    by_cases hx : xs = []
    · subst xs
      cases ht
      simpa only [lastCode_singleton] using hd
    · have hy : ys ≠ [] := by
        intro hy
        have he := ht.length_eq
        rw [hy, List.length_nil] at he
        exact hx (List.length_eq_zero_iff.mp he)
      rw [SkTracking.Support.lastCode_cons_nonempty c xs hx,
        SkTracking.Support.lastCode_cons_nonempty d ys hy]
      exact ih hx

/-- Actual lower execution above its base supplies strict singleton FIRST;
all OWN contextual callers are derived from its actual ALL bound. -/
theorem assignment_appendCheck_eq (q alpha input factor otherFactor : Nat)
    (heads returnedHeads : List Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (ho : heads ∈ Assignment.execute (betaCode q alpha) input)
    (hstrict : base (betaCode q alpha) < interpretation (betaCode q alpha) input)
    (hown : interpretation (betaCode q alpha) input < Enclosure.sourceAlphaPlus q alpha)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads returnedHeads)
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor) :
    BranchesSupport.appendCheck q otherFactor returnedHeads =
      BranchesSupport.appendCheck (betaCode q alpha) factor heads := by
  have htrack := Assignment.execute_tracking _ input heads ho
  have hs := (SourceTrackingRaw.trackingCheck_conditions _ heads).mp htrack
  have hall := (Assignment.execute_spec _ input heads ho).2.1.2.1
  have hbounds : ∀ c ∈ heads, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha :=
    fun c hc => (hall c hc).trans_lt hown
  have hreturned := ContextAssignmentReturn.raw_tracking_return q alpha ha heads returnedHeads
    htrack hrel hbounds
  have ht := (SourceTrackingRaw.trackingCheck_conditions q returnedHeads).mp hreturned
  have hl := append_return_relation_last hrel hs.1
  have hv := ContextRowValues.returned_values hrel
  have hp : (stripLast returnedHeads).map (interpretation q) =
      (stripLast heads).map (interpretation (betaCode q alpha)) := by
    have he := congrArg (fun vs : List Ordinal.{0} => vs.reverse.tail.reverse) hv
    simpa only [stripLast, List.map_reverse, List.map_tail] using he
  have hempty : stripLast returnedHeads = [] ↔ stripLast heads = [] := by
    constructor
    · intro he
      exact List.map_eq_nil_iff.mp (by simpa only [he, List.map_nil] using hp.symm)
    · intro he
      exact List.map_eq_nil_iff.mp (by simpa only [he, List.map_nil] using hp)
  have hfloor : base q ≤ base (betaCode q alpha) := by
    rw [beta_base q alpha ha]
    exact root_base_le q alpha ha
  have hsingleton : stripLast heads = [] →
      base (betaCode q alpha) < interpretation (betaCode q alpha) (lastCode heads) := by
    intro he
    obtain ⟨last, hw, hm⟩ := stripLast_split heads hs.1
    have hlast : lastCode heads = last := by rw [hw, lastCode_append_singleton]
    have hword : heads = [lastCode heads] := by simpa only [he, List.nil_append, hlast] using hw
    have hfirst := AssignmentFirst.execute_firstCode_gt_base _ input heads ho hstrict
    simpa only [hword, Insertion.firstCode, List.head?_cons, Option.getD_some] using hfirst
  have hprevious :
      (if stripLast returnedHeads = [] then base q < interpretation q (lastCode returnedHeads)
       else interpretation q (lastCode (stripLast returnedHeads)) < interpretation q (lastCode returnedHeads)) ↔
      (if stripLast heads = [] then base (betaCode q alpha) < interpretation (betaCode q alpha) (lastCode heads)
       else interpretation (betaCode q alpha) (lastCode (stripLast heads)) < interpretation (betaCode q alpha) (lastCode heads)) := by
    by_cases he : stripLast heads = []
    · have hy := hempty.mpr he
      have hlow := hsingleton he
      simp only [if_pos he, if_pos hy, hl.2.2]
      exact iff_of_true (hfloor.trans_lt hlow) hlow
    · have hy : stripLast returnedHeads ≠ [] := fun hy => he (hempty.mp hy)
      have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq
        (interpretation q) (interpretation (betaCode q alpha))
        (stripLast returnedHeads) (stripLast heads) hy hp
      simp only [if_neg he, if_neg hy, hl.2.2, hlast]
  have hprevious_floor :
      (if stripLast heads = [] then base (betaCode q alpha) < interpretation (betaCode q alpha) (lastCode heads)
       else interpretation (betaCode q alpha) (lastCode (stripLast heads)) < interpretation (betaCode q alpha) (lastCode heads)) →
      base (betaCode q alpha) < interpretation (betaCode q alpha) (lastCode heads) := by
    intro hc
    by_cases he : stripLast heads = []
    · simpa only [if_pos he] using hc
    · have hroot := hs.2.1.nodes _ (lastCode_mem _ he)
      have hbase := ((SourceTrackingRaw.Support.inputCheck_exact _ _).mp hroot).2.1
      exact hbase.trans (by simpa only [if_neg he] using hc)
  apply Bool.eq_iff_iff.mpr
  change (BranchesSupport.appendCheck q otherFactor returnedHeads = true) ↔
    BranchesSupport.appendCheck (betaCode q alpha) factor heads = true
  rw [BranchesSupport.appendCheck_exact q otherFactor returnedHeads hreturned,
    BranchesSupport.appendCheck_exact (betaCode q alpha) factor heads htrack]
  constructor
  · rintro ⟨hroot, hprev, hfactor, hcover⟩
    have hprev' := hprevious.mp hprev
    have hepsilon := ((SourceTrackingRaw.Support.inputCheck_exact q _).mp hroot).2.2
    have hsource : SourceTrackingRaw.Support.inputCheck (betaCode q alpha) (lastCode heads) = true :=
      (SourceTrackingRaw.Support.inputCheck_exact _ _).mpr
        ⟨hs.2.2.1, hprevious_floor hprev', by simpa only [hl.2.2] using hepsilon⟩
    have hmu := ContextAssignmentReturn.contextual_raw_entry q alpha _ _ ha hsource hl
      (hbounds _ (lastCode_mem _ hs.1))
    refine ⟨hsource, hprev', hf, ?_⟩
    simpa only [hd.2.2, hmu.2] using hcover
  · rintro ⟨hroot, hprev, hfactor, hcover⟩
    have hmu := ContextAssignmentReturn.contextual_raw_entry q alpha _ _ ha hroot hl
      (hbounds _ (lastCode_mem _ hs.1))
    refine ⟨hmu.1, hprevious.mpr hprev, hd.1, ?_⟩
    simpa only [hd.2.2, hmu.2] using hcover

/-- The actual original tracker supplies the proper head and its nested
OWN endpoint. The independently executing lower word and its real finite
return therefore have the same computed append flag, with no endpoint or
returned tracker premise. -/
theorem returned_assignment_appendCheck_eq (q : Nat) (word : List Nat)
    (head input factor otherFactor : Nat) (heads returnedHeads : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true)
    (hh : head ∈ stripLast word)
    (ho : heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hstrict : base (ReplacementSupport.raisedBaseCode q head) <
      interpretation (ReplacementSupport.raisedBaseCode q head) input)
    (hb : interpretation (ReplacementSupport.raisedBaseCode q head) input ≤
      interpretation q (lastCode word))
    (hr : returnedHeads ∈ Replacement.returnWord q (ReplacementSupport.raisedBaseCode q head) heads)
    (hf : lowCheckCode (ReplacementSupport.raisedBaseCode q head) factor = true)
    (hd : SameEntry q (ReplacementSupport.raisedBaseCode q head) factor otherFactor) :
    BranchesSupport.appendCheck q otherFactor returnedHeads =
      BranchesSupport.appendCheck (ReplacementSupport.raisedBaseCode q head) factor heads := by
  have ht := (SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  have hhead := ht.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec q head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_betaCode q head hhead
  have hne : stripLast word ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints q word hw hne head hh
  have hs := ContextAssignmentReturn.assignment_return_spec q word head input heads returnedHeads
    hw hh ho hb hr
  have hown : interpretation (ReplacementSupport.raisedBaseCode q head) input <
      Enclosure.sourceAlphaPlus q (SourceTrackingRaw.Support.rootCode q head) := hb.trans_lt hend
  simpa only [he] using assignment_appendCheck_eq q (SourceTrackingRaw.Support.rootCode q head)
    input factor otherFactor heads returnedHeads hroot
    (by simpa only [he] using ho) (by simpa only [he] using hstrict)
    (by simpa only [he] using hown) (by simpa only [he] using hs.2.1)
    (by simpa only [he] using hf) (by simpa only [he] using hd)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextAppendCheck
