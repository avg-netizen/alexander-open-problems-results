import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextRowValues
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentFirst
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBranchesSupport

/-!
# Genuine original-zero and lower-context append-guard covariance

The original floor remains literal one in the actual check-zero dictionary.
The final lower-context entry need not be a RAW root. Its genuine preceding
strict comparison supplies the lower-base floor when it is append-eligible;
for a singleton the real full assignment supplies strict FIRST. The actual
OWN mu theorem then derives the concrete cover identity in both directions.
Every original tracker and OWN caller follows from the real lower execution
and original headword FINAL bound. No contextual assignment composition or
wholesale final RAW input equivalence is claimed. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextAppendCheck

open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (lastCode_cons_nonempty)

private theorem append_source_relation_last {r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (Replacement.EntryMatches r) xs ys) (hne : xs ≠ []) :
    Replacement.EntryMatches r (lastCode xs) (lastCode ys) := by
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
      rw [lastCode_cons_nonempty c xs hx, lastCode_cons_nonempty d ys hy]
      exact ih hx

private theorem append_source_returned_values {r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (Replacement.EntryMatches r) xs ys) :
    ys.map (interpretation 0) = xs.map (NativeContext.interpretation r) := by
  induction hr with
  | nil => rfl
  | cons hd ht ih => simp only [List.map_cons, hd.2, ih]

/-- Both append flags follow from actual execution and actual returns.
The final RAW caller is derived only under its true strict preceding test. -/
theorem assignment_appendCheck_eq (root input factor otherFactor : Nat)
    (heads returnedHeads : List Nat) (ha : Mu.inputCheck root = true)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode root) input)
    (hstrict : NativeContext.base (alphaCode root) < NativeContext.interpretation (alphaCode root) input)
    (hown : NativeContext.interpretation (alphaCode root) input < Enclosure.sourceAlphaPlus root)
    (hrel : List.Forall₂ (Replacement.EntryMatches (alphaCode root)) heads returnedHeads)
    (hf : NativeContext.lowCheckCode (alphaCode root) factor = true)
    (hd : Replacement.EntryMatches (alphaCode root) factor otherFactor) :
    BranchesSupport.appendCheck otherFactor returnedHeads =
      NativeContext.SourceAdditiveTracking.BranchesSupport.appendCheck (alphaCode root) factor heads := by
  have htrack := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input heads ho
  have hs := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ heads).mp htrack
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input heads ho).2.1.2.1
  have hbounds : ∀ c ∈ heads, NativeContext.interpretation (alphaCode root) c < Enclosure.sourceAlphaPlus root :=
    fun c hc => (hall c hc).trans_lt hown
  have hreturned := ContextAssignmentReturn.raw_tracking_return root ha heads returnedHeads htrack hrel hbounds
  have hl := append_source_relation_last hrel hs.1
  have hv := append_source_returned_values hrel
  have hp : (stripLast returnedHeads).map (interpretation 0) =
      (stripLast heads).map (NativeContext.interpretation (alphaCode root)) := by
    have he := congrArg (fun vs : List Ordinal.{0} => vs.reverse.tail.reverse) hv
    simpa only [stripLast, List.map_reverse, List.map_tail] using he
  have hempty : stripLast returnedHeads = [] ↔ stripLast heads = [] := by
    constructor
    · intro he
      exact List.map_eq_nil_iff.mp (by simpa only [he, List.map_nil] using hp.symm)
    · intro he
      exact List.map_eq_nil_iff.mp (by simpa only [he, List.map_nil] using hp)
  have hfloor : 1 ≤ NativeContext.base (alphaCode root) := by
    rw [OrderSupport.alpha_base root ha]
    exact Order.one_le_iff_pos.mpr (root_pos root ha)
  have hsingleton : stripLast heads = [] →
      NativeContext.base (alphaCode root) < NativeContext.interpretation (alphaCode root) (lastCode heads) := by
    intro he
    obtain ⟨last, hw, hm⟩ := stripLast_split heads hs.1
    have hlast : lastCode heads = last := by rw [hw, lastCode_append_singleton]
    have hword : heads = [lastCode heads] := by simpa only [he, List.nil_append, hlast] using hw
    have hfirst := NativeContext.SourceAdditiveTracking.AssignmentFirst.execute_firstCode_gt_base
      _ input heads ho hstrict
    simpa only [hword, NativeContext.SourceAdditiveTracking.Insertion.firstCode,
      List.head?_cons, Option.getD_some] using hfirst
  have hprevious :
      (if stripLast returnedHeads = [] then 1 < interpretation 0 (lastCode returnedHeads)
       else interpretation 0 (lastCode (stripLast returnedHeads)) < interpretation 0 (lastCode returnedHeads)) ↔
      (if stripLast heads = [] then NativeContext.base (alphaCode root) <
          NativeContext.interpretation (alphaCode root) (lastCode heads)
       else NativeContext.interpretation (alphaCode root) (lastCode (stripLast heads)) <
          NativeContext.interpretation (alphaCode root) (lastCode heads)) := by
    by_cases he : stripLast heads = []
    · have hy := hempty.mpr he
      have hlow := hsingleton he
      simp only [if_pos he, if_pos hy, hl.2]
      exact iff_of_true (hfloor.trans_lt hlow) hlow
    · have hy : stripLast returnedHeads ≠ [] := fun hy => he (hempty.mp hy)
      have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq (interpretation 0)
        (NativeContext.interpretation (alphaCode root)) (stripLast returnedHeads) (stripLast heads) hy hp
      simp only [if_neg he, if_neg hy, hl.2, hlast]
  have hprevious_floor :
      (if stripLast heads = [] then NativeContext.base (alphaCode root) <
          NativeContext.interpretation (alphaCode root) (lastCode heads)
       else NativeContext.interpretation (alphaCode root) (lastCode (stripLast heads)) <
          NativeContext.interpretation (alphaCode root) (lastCode heads)) →
      NativeContext.base (alphaCode root) < NativeContext.interpretation (alphaCode root) (lastCode heads) := by
    intro hc
    by_cases he : stripLast heads = []
    · simpa only [if_pos he] using hc
    · have hroot := hs.2.1.nodes _ (lastCode_mem _ he)
      have hbase := ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ _).mp hroot).2.1
      exact hbase.trans (by simpa only [if_neg he] using hc)
  apply Bool.eq_iff_iff.mpr
  change (BranchesSupport.appendCheck otherFactor returnedHeads = true) ↔
    NativeContext.SourceAdditiveTracking.BranchesSupport.appendCheck (alphaCode root) factor heads = true
  rw [BranchesSupport.appendCheck_exact otherFactor returnedHeads hreturned,
    NativeContext.SourceAdditiveTracking.BranchesSupport.appendCheck_exact (alphaCode root) factor heads htrack]
  constructor
  · rintro ⟨hroot, hprev, hfactor, hcover⟩
    have hprev' := hprevious.mp hprev
    have hepsilon := ((SourceTrackingRaw.Support.inputCheck_exact _).mp hroot).2.2
    have hsource : NativeContext.SourceTrackingRaw.Support.inputCheck (alphaCode root) (lastCode heads) = true :=
      (NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ _).mpr
        ⟨hs.2.2.1, hprevious_floor hprev', by simpa only [hl.2] using hepsilon⟩
    have hmu := ContextAssignmentReturn.contextual_raw_entry root _ _ ha hsource hl
      (hbounds _ (lastCode_mem _ hs.1))
    refine ⟨hsource, hprev', hf, ?_⟩
    simpa only [hd.2, hmu.2] using hcover
  · rintro ⟨hroot, hprev, hfactor, hcover⟩
    have hmu := ContextAssignmentReturn.contextual_raw_entry root _ _ ha hroot hl
      (hbounds _ (lastCode_mem _ hs.1))
    refine ⟨hmu.1, hprevious.mpr hprev, ((Theta.acceptedLowCode_iff 0 _).mp hd.1).1, ?_⟩
    simpa only [hd.2, hmu.2] using hcover

/-- The original real tracker derives the OWN bound and the literal return
relation before comparing the actual two independently defined append flags. -/
theorem returned_assignment_appendCheck_eq (word : List Nat) (head input factor otherFactor : Nat)
    (heads : List Nat) (hw : SourceTrackingRaw.trackingCheck word = true)
    (hh : head ∈ stripLast word)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode word))
    (hf : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) factor = true)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) factor otherFactor) :
    BranchesSupport.appendCheck otherFactor (Replacement.returnWord head heads) =
      NativeContext.SourceAdditiveTracking.BranchesSupport.appendCheck (ReplacementSupport.raisedBaseCode head) factor heads := by
  have ht := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hhead := ht.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hn : stripLast word ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints word hw hn head hh
  have hs := ContextAssignmentReturn.assignment_return word head input heads hw hh ho hb
  have hown : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input <
      Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode head) := hb.trans_lt hend
  simpa only [he] using assignment_appendCheck_eq (SourceTrackingRaw.Support.rootCode head)
    input factor otherFactor heads (Replacement.returnWord head heads) hroot
    (by simpa only [he] using ho) (by simpa only [he] using hstrict)
    (by simpa only [he] using hown) (by simpa only [he] using hs.2.1)
    (by simpa only [he] using hf) (by simpa only [he] using hd)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextAppendCheck
