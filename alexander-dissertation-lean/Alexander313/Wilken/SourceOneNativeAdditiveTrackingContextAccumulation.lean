import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextUninitializedUpdate
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingIntervalFrames

/-!
# Retained-head/reset states along the actual original factor unwind

Every real frame reconstructs the complete original child Assignment.
Its actual last-factor bound supplies the descending initialized caller.
Before any reset the original selected head is literally retained; an
observed default constructs the first genuine lower Assignment. Each later
frame constructs its next complete lower Assignment and actual LF. Thus
the original cut survives the entire actual finite unwind, without an
assigned arbitrary initial suffix, numerical fuel or update equation.
The fixed independently executing greater raised row compares the whole
final suffix, either by its strict FIRST or actual full-P-left/M-right order.
Source-only uncompiled candidates in the literal original source zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextAccumulation

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open Alexander313.Wilken.MultiplicativeNormalForm
open IntervalFrames

/-- The old arbitrary suffix and the genuinely initialized suffix are
kept distinct. The LF column is the actual current source input LF. -/
def State (head greater current : Nat) (suffix : List Nat) : Prop :=
  (∃ after, suffix = head :: after) ∨
    ∃ input heads,
      NativeContext.base (ReplacementSupport.raisedBaseCode head) <
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ∧
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input < interpretation 0 greater ∧
      heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
        (ReplacementSupport.raisedBaseCode head) input ∧
      lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) =
        lf (interpretation 0 current) ∧
      List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix

/-- Real Factor/Unwind memberships derive every state and all current
Assignment memberships. No chronological factor table or child is supplied. -/
theorem unwind_states {target greater current : Nat} {frames : List Frame}
    (hs : Segment target greater current frames)
    (original out before : List Nat) (head : Nat) (ys : List Nat)
    (hbottom : original ∈ Assignment.execute target)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hne : before ≠ [])
    (hfront : interpretation 0 (lastCode before) < interpretation 0 head)
    (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hgreater : interpretation 0 greater ≤ interpretation 0 (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement head greater)
    (hcover : Insertion.coverCheck (lastCode before) (Insertion.firstCode ys) = true)
    (hstart : ∃ after, original = before ++ head :: after)
    (hu : Unwind frames original out) :
    out ∈ Assignment.execute current ∧
      ∃ suffix, out = before ++ suffix ∧ State head greater current suffix := by
  induction hs generalizing out with
  | nil =>
    cases hu
    obtain ⟨after, he⟩ := hstart
    exact ⟨hbottom, head :: after, he, Or.inl ⟨after, rfl⟩⟩
  | cons current child factor frames hf hsmall ht ih =>
    cases hu with
    | cons current child factor frames original middle out htail hbranch =>
      obtain ⟨hchild, suffix, hmiddle, hstate⟩ := ih middle htail
      have hcurrent := Assignment.execute_factor current child factor middle out hf hchild hbranch
      have hfull : SourceTrackingRaw.trackingCheck (before ++ suffix) = true := by
        simpa only [hmiddle] using Assignment.execute_tracking child middle hchild
      obtain ⟨hcaller, hpAccepted, hfAccepted, hpCaller, hpFloor, hpLess, hM, hone,
        hproduct, hlf, hcount⟩ := Factor.execute_spec current (child, factor) hf
      have hcut := Factor.Bounds.execute_last_le_prefix_last current (child, factor) hf
      have hlast := hcut.trans (Assignment.execute_last_bounds child middle hchild).1
      rcases hstate with ⟨after, he⟩ | ⟨input, heads, hstrict, hinput, ho, hlastFactor, hrel⟩
      · obtain ⟨nextSuffix, hout, hnext⟩ := ContextUninitializedUpdate.uninitialized_update
          original head greater factor before after ys out hw hh hne
          (by simpa only [he] using hfull) hfront hfAccepted hM hone
          (by simpa only [hmiddle, he] using hlast) hg hm hhead hsmall hy hcover
          (by simpa only [hmiddle, he] using hbranch)
        refine ⟨hcurrent, nextSuffix, hout, ?_⟩
        rcases hnext with hn | ⟨next, nextHeads, hv, hs, hb, ha, hl, hr⟩
        · exact Or.inl hn
        · exact Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩
      · have hcut' : interpretation 0 factor ≤
          lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) := by
          rw [hlastFactor]
          exact hcut
        obtain ⟨next, nextHeads, nextSuffix, hout, hv, hs, hb, ha, hl, hr⟩ :=
          ContextInitializedUpdate.initialized_update original head greater input factor
            before heads suffix ys out hw hh hg hm hhead hgreater hy hcover ho hstrict hinput
            hrel hne hfull hfront.le hfAccepted hM hone hsmall hcut'
            (by simpa only [hmiddle] using hbranch)
        exact ⟨hcurrent, nextSuffix, hout, Or.inr ⟨next, nextHeads, hs, hb, ha, hl.trans hlf, hr⟩⟩

private theorem assignment_lex_raised (head greater input : Nat) (heads suffix ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hlt : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input < interpretation 0 greater)
    (hr : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix)
    (hy : ys ∈ Replacement.raisedReplacement head greater) :
    List.Lex (· < ·) (suffix.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨rightWord, hw, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head greater ys hh hg hm hhead hy
  obtain ⟨right, hs, hword⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative head greater right hh hg hm hhead hs
  have hs' := ReplacementSupport.raisedSearch_spec head greater right hg hs
  have har : rightWord ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) right := by
    rw [← hword]
    exact NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ right hi
  rw [ContextRelatedFirstCut.relation_values hr, hv]
  exact NativeContext.SourceAdditiveTracking.AssignmentCoverPrefix.execute_right_multiplicative_lex
    _ input right heads rightWord hi (by rw [hs'.2.2]; exact hlt) ho har

/-- The entire actual unwind lies before the fixed raised replacement,
with the original literal preceding word retained in every actual state. -/
theorem unwind_lex {target greater current : Nat} {frames : List Frame}
    (hs : Segment target greater current frames)
    (original out before : List Nat) (head : Nat) (ys : List Nat)
    (hbottom : original ∈ Assignment.execute target)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hne : before ≠ [])
    (hfront : interpretation 0 (lastCode before) < interpretation 0 head)
    (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hgreater : interpretation 0 greater ≤ interpretation 0 (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement head greater)
    (hcover : Insertion.coverCheck (lastCode before) (Insertion.firstCode ys) = true)
    (hstart : ∃ after, original = before ++ head :: after)
    (hu : Unwind frames original out) :
    List.Lex (· < ·) (out.map (interpretation 0)) ((before ++ ys).map (interpretation 0)) := by
  obtain ⟨ha, suffix, he, hsuffix⟩ := unwind_states hs original out before head ys
    hbottom hw hh hne hfront hg hm hhead hgreater hy hcover hstart hu
  have hraw := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hlex : List.Lex (· < ·) (suffix.map (interpretation 0)) (ys.map (interpretation 0)) := by
    rcases hsuffix with ⟨after, hafter⟩ | ⟨input, heads, hstrict, hinput, ho, hl, hrel⟩
    · have hfirst := FrameOrderSupport.raised_first_strict head greater ys hraw hg hm hhead hy
      have hneYs : ys ≠ [] := by
        obtain ⟨rightWord, hr, he, ht, hv, hlen, hchecked⟩ :=
          Replacement.raisedReplacement_spec head greater ys hraw hg hm hhead hy
        intro hn
        have hl := hlen
        rw [hn, List.length_nil] at hl
        exact ((NativeContext.SourceTrackingSequences.trackingCheck_exact _ rightWord).mp ht).1
          (List.length_eq_zero_iff.mp hl.symm)
      obtain ⟨first, rest, hys⟩ := List.exists_cons_of_ne_nil hneYs
      have hl : interpretation 0 head < interpretation 0 first := by
        simpa only [hys, Insertion.firstCode, List.head?_cons, Option.getD_some] using hfirst
      simpa only [hafter, hys, List.map_cons] using
        (List.Lex.rel hl : List.Lex (· < ·)
          (interpretation 0 head :: after.map (interpretation 0)) (interpretation 0 first :: rest.map (interpretation 0)))
    · exact assignment_lex_raised head greater input heads suffix ys hraw hg hm hhead ho hinput hrel hy
  simpa only [he, List.map_append] using List.Lex.append_left (· < ·) hlex (before.map (interpretation 0))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextAccumulation
