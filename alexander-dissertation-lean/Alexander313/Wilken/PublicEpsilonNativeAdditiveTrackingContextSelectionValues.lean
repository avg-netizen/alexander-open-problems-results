import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextRowValues

/-!
# Actual greatest-selector value covariance under genuine source returns

Concrete chronological replacement rows are paired by their actual returned
heads and complete replacement values. At every proper predecessor the real
RAW caller and its OWN interval derive the contextual mu equality, hence the
actual adjacent cover flag. The right-priority recursive selector therefore
returns the same numerical position and replacement values. Its computed
whole insertion word retains the same prefix values. No flag column, selected
position or assignment composition is assumed. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextSelectionValues

open PublicEpsilonUnboundedIota SourceTrackingSequences
open ReplacementFidelity (SameEntry)
open InsertionSupport (Row)
open AssignmentValueSupport (rowValues candidateValues)
open Hereditary.FinePredecessor (stripLast)

private theorem row_stripLast_append_singleton (rows : List Row) (row : Row) :
    stripLast (rows ++ [row]) = rows := by
  simp only [stripLast, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.tail_cons, List.reverse_reverse]

private theorem row_stripLast_cons_nonempty (a : Row) (rows : List Row) (hne : rows ≠ []) :
    stripLast (a :: rows) = a :: stripLast rows := by
  obtain ⟨last, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split rows hne
  calc
    stripLast (a :: rows) = stripLast ((a :: stripLast rows) ++ [last]) := by
      rw [← List.cons_append, ← he]
    _ = a :: stripLast rows := row_stripLast_append_singleton _ _

def RowReturn (q r : Nat) (source target : Row) : Prop :=
  SameEntry q r source.1 target.1 ∧ source.2 ≠ [] ∧
    (∀ c ∈ source.2, lowCheckCode r c = true) ∧
    (∀ d ∈ target.2, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) ∧
    target.2.map (interpretation q) = source.2.map (interpretation r)

theorem RowReturn.first {q r : Nat} {source target : Row} (hr : RowReturn q r source target) :
    SameEntry q r (Insertion.firstCode source.2) (Insertion.firstCode target.2) := by
  rcases source with ⟨a, word⟩
  rcases target with ⟨b, otherWord⟩
  cases word with
  | nil => exact False.elim (hr.2.1 rfl)
  | cons first rest =>
    cases otherWord with
    | nil =>
      have hv := hr.2.2.2.2
      simp only [List.map_nil, List.map_cons, List.nil_ne_cons] at hv
    | cons other otherRest =>
      have hd := hr.2.2.2.1 other List.mem_cons_self
      have hv := (List.cons.inj hr.2.2.2.2).1
      simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using
        And.intro hd.1 (And.intro hd.2 hv)

theorem RowReturn.first_low {q r : Nat} {source target : Row} (hr : RowReturn q r source target) :
    lowCheckCode r (Insertion.firstCode source.2) = true :=
  AssignmentValueSupport.firstCode_low r source.2 hr.2.1 hr.2.2.1

theorem row_returns_values {q r : Nat} {rows targets : List Row}
    (hr : List.Forall₂ (RowReturn q r) rows targets) :
    targets.map (rowValues q) = rows.map (rowValues r) := by
  induction hr with
  | nil => rfl
  | cons hd ht ih =>
    simp only [List.map_cons, rowValues, hd.1.2.2, hd.2.2.2.2, ih]

/-- Every true chronological relation comes from an independently executing
replacement. Both actual complete tracker and factor-to-LAST callers remain. -/
theorem relations_row_return (q r factor otherFactor : Nat) (full returnedFull : List Nat)
    (hh : SourceTrackingRaw.trackingCheck r full = true)
    (ht : SourceTrackingRaw.trackingCheck q returnedFull = true)
    (hf : lowCheckCode r factor = true) (hd : SameEntry q r factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation r factor))
    (hb : interpretation r factor ≤ interpretation r (lastCode full))
    (hc : interpretation q otherFactor ≤ interpretation q (lastCode returnedFull))
    (heads returnedHeads : List Nat) (rows returnedRows : List Row)
    (hs : ∀ c ∈ heads, c ∈ full) (hu : ∀ d ∈ returnedHeads, d ∈ returnedFull)
    (hrel : List.Forall₂ (SameEntry q r) heads returnedHeads)
    (hr : List.Forall₂ (InsertionSupport.Matches r factor) heads rows)
    (ho : List.Forall₂ (InsertionSupport.Matches q otherFactor) returnedHeads returnedRows) :
    List.Forall₂ (RowReturn q r) rows returnedRows := by
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q otherFactor) := by
    rw [hd.2.2]; exact hm
  induction heads generalizing returnedHeads rows returnedRows with
  | nil =>
    cases hrel
    cases hr
    cases ho
    exact .nil
  | cons a heads ih =>
    cases hrel with
    | cons hhead htail =>
      cases hr with
      | cons hrow hrest =>
        cases ho with
        | cons hother hotherRest =>
          have ha := ConditionalReplacement.execute_spec r full hh a factor
            (hs a List.mem_cons_self) hf hm hb _ (by simpa only [hrow.1] using hrow.2)
          have ht' := ConditionalReplacement.execute_spec q returnedFull ht _ otherFactor
            (hu _ List.mem_cons_self) hd.1 hm' hc _ (by simpa only [hother.1] using hother.2)
          have hv := ContextConditionalValues.conditional_values_eq r q full returnedFull hh ht
            a _ factor otherFactor (hs a List.mem_cons_self) (hu _ List.mem_cons_self)
            hf hd.1 hm hb hc hhead.2.2.symm hd.2.2.symm _ _
            (by simpa only [hrow.1] using hrow.2)
            (by simpa only [hother.1] using hother.2)
          refine .cons ?_ (ih _ _ _
            (fun c h => hs c (List.mem_cons_of_mem _ h))
            (fun d h => hu d (List.mem_cons_of_mem _ h)) htail hrest hotherRest)
          exact ⟨by simpa only [hrow.1, hother.1] using hhead, ha.1,
            fun c h => (ha.2.1 c h).1, ht'.2.1, hv.symm⟩

/-- Proper predecessors alone need RAW admission; the final row is never
used as a predecessor by the real selector. Every cover equality is derived
from its genuine contextual mu and the actual next replacement FIRST. -/
theorem choose_values_eq (q alpha : Nat) (rows targets : List Row)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hr : List.Forall₂ (RowReturn q (betaCode q alpha)) rows targets)
    (hp : ∀ row ∈ stripLast rows,
      SourceTrackingRaw.Support.inputCheck (betaCode q alpha) row.1 = true ∧
        interpretation (betaCode q alpha) row.1 < Enclosure.sourceAlphaPlus q alpha) :
    (Insertion.choose q targets).map (candidateValues q) =
      (Insertion.choose (betaCode q alpha) rows).map (candidateValues (betaCode q alpha)) := by
  revert hp
  induction hr with
  | nil => intro hp; rfl
  | @cons a otherA rest otherRest hhead htail ih =>
    intro hp
    cases rest with
    | nil => cases htail; rfl
    | cons b later =>
      cases otherRest with
      | nil => cases htail
      | cons otherB otherLater =>
        cases htail with
        | cons hnext hlater =>
          have hproper : a ∈ stripLast (a :: b :: later) := by
            rw [row_stripLast_cons_nonempty a (b :: later) (List.cons_ne_nil _ _)]
            exact List.mem_cons_self
          have hrec := ih (fun row hm => hp row (by
            rw [row_stripLast_cons_nonempty a (b :: later) (List.cons_ne_nil _ _)]
            exact List.mem_cons_of_mem _ hm))
          have hc := ContextRowValues.returned_cover_eq q alpha a.1 otherA.1
            (Insertion.firstCode b.2) (Insertion.firstCode otherB.2)
            ha (hp a hproper).1 hhead.1 (hp a hproper).2 hnext.first_low hnext.first
          cases hs : Insertion.choose (betaCode q alpha) (b :: later) with
          | none =>
            cases ht : Insertion.choose q (otherB :: otherLater) with
            | some c =>
              simp only [hs, ht, Option.map_none, Option.map_some, Option.some_ne_none] at hrec
            | none =>
              cases hb : Insertion.coverCheck (betaCode q alpha) a.1 (Insertion.firstCode b.2) <;>
                simp only [Insertion.choose_pair, hs, ht, hc, hb, Bool.cond_false,
                  Bool.cond_true, Option.map_none, Option.map_some, candidateValues, hnext.2.2.2.2]
          | some c =>
            cases ht : Insertion.choose q (otherB :: otherLater) with
            | none =>
              simp only [hs, ht, Option.map_none, Option.map_some, Option.none_ne_some] at hrec
            | some d =>
              have he : candidateValues q d = candidateValues (betaCode q alpha) c := by
                simpa only [hs, ht, Option.map_some, Option.some.injEq] using hrec
              have hn := congrArg Prod.fst he
              have hw := congrArg Prod.snd he
              simp only [Insertion.choose_pair, hs, ht, Option.map_some, candidateValues, hn, hw]

theorem default_values_eq (q r : Nat) (rows targets : List Row)
    (hv : targets.map (rowValues q) = rows.map (rowValues r)) :
    ((targets.head?.getD (0, [])).2).map (interpretation q) =
      ((rows.head?.getD (0, [])).2).map (interpretation r) := by
  cases targets with
  | nil =>
    have hn : rows = [] := List.map_eq_nil_iff.mp hv.symm
    subst rows
    rfl
  | cons a targets =>
    cases rows with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b rows =>
      simpa only [List.head?_cons, Option.getD_some] using congrArg Prod.snd (List.cons.inj hv).1

theorem take_heads_values_eq (q r n : Nat) (rows targets : List Row)
    (hv : targets.map (rowValues q) = rows.map (rowValues r)) :
    ((targets.take n).map Prod.fst).map (interpretation q) =
      ((rows.take n).map Prod.fst).map (interpretation r) := by
  have he := congrArg (fun rs : List (Ordinal.{0} × List Ordinal.{0}) => (rs.take n).map Prod.fst) hv
  simpa only [← List.map_take, List.map_map, rowValues] using he

theorem insertion_word_values_eq (q alpha : Nat) (rows targets : List Row)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hr : List.Forall₂ (RowReturn q (betaCode q alpha)) rows targets)
    (hp : ∀ row ∈ stripLast rows,
      SourceTrackingRaw.Support.inputCheck (betaCode q alpha) row.1 = true ∧
        interpretation (betaCode q alpha) row.1 < Enclosure.sourceAlphaPlus q alpha) :
    (Insertion.word q targets).map (interpretation q) =
      (Insertion.word (betaCode q alpha) rows).map (interpretation (betaCode q alpha)) := by
  have hv := row_returns_values hr
  have hc := choose_values_eq q alpha rows targets ha hr hp
  cases ht : Insertion.choose q targets with
  | none =>
    cases hs : Insertion.choose (betaCode q alpha) rows with
    | some c => simp only [ht, hs, Option.map_none, Option.map_some, Option.none_ne_some] at hc
    | none => simpa only [Insertion.word, ht, hs] using default_values_eq q _ rows targets hv
  | some d =>
    cases hs : Insertion.choose (betaCode q alpha) rows with
    | none => simp only [ht, hs, Option.map_none, Option.map_some, Option.some_ne_none] at hc
    | some c =>
      have he : candidateValues q d = candidateValues (betaCode q alpha) c := by
        simpa only [ht, hs, Option.map_some, Option.some.injEq] using hc
      have hn := congrArg Prod.fst he
      have hw := congrArg Prod.snd he
      simpa only [Insertion.word, ht, hs, List.map_append, hn, hw] using
        congrArg (fun prefix => prefix ++ c.2.map (interpretation (betaCode q alpha)))
          (take_heads_values_eq q _ c.1 rows targets hv)

/-- Both independent partial insertions use genuinely executing replacement
rows. The actual lower assignment and finite original return derive every
proper predecessor's RAW and OWN caller before the selector is compared. -/
theorem insertion_values_eq (q alpha input factor otherFactor : Nat)
    (heads returnedHeads word returnedWord : List Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (ho : heads ∈ Assignment.execute (betaCode q alpha) input)
    (hown : interpretation (betaCode q alpha) input < Enclosure.sourceAlphaPlus q alpha)
    (hrel : List.Forall₂ (SameEntry q (betaCode q alpha)) heads returnedHeads)
    (hf : lowCheckCode (betaCode q alpha) factor = true)
    (hd : SameEntry q (betaCode q alpha) factor otherFactor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (betaCode q alpha) factor))
    (hb : interpretation (betaCode q alpha) factor ≤ interpretation (betaCode q alpha) (lastCode heads))
    (hs : word ∈ Insertion.execute (((betaCode q alpha), factor), heads))
    (ht : returnedWord ∈ Insertion.execute ((q, otherFactor), returnedHeads)) :
    returnedWord.map (interpretation q) = word.map (interpretation (betaCode q alpha)) := by
  have htrack := Assignment.execute_tracking _ input heads ho
  have hconditions := (SourceTrackingRaw.trackingCheck_conditions _ heads).mp htrack
  have hall := (Assignment.execute_spec _ input heads ho).2.1.2.1
  have hbounds : ∀ c ∈ heads, interpretation (betaCode q alpha) c < Enclosure.sourceAlphaPlus q alpha :=
    fun c hc => (hall c hc).trans_lt hown
  have htarget := ContextAssignmentReturn.raw_tracking_return q alpha ha heads returnedHeads
    htrack hrel hbounds
  have hv := ContextRowValues.returned_values hrel
  have hlast := SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation q) (interpretation (betaCode q alpha)) returnedHeads heads
    ((SourceTrackingRaw.trackingCheck_conditions q returnedHeads).mp htarget).1 hv
  have hbound : interpretation q otherFactor ≤ interpretation q (lastCode returnedHeads) := by
    rw [hd.2.2, hlast]; exact hb
  obtain ⟨rows, hr, rfl⟩ := (Part.mem_map_iff _).mp hs
  obtain ⟨targets, hout, rfl⟩ := (Part.mem_map_iff _).mp ht
  have hr' := InsertionSupport.executeRows_relation (betaCode q alpha) factor heads rows hr
  have ht' := InsertionSupport.executeRows_relation q otherFactor returnedHeads targets hout
  have hreturn := relations_row_return q (betaCode q alpha) factor otherFactor heads returnedHeads
    htrack htarget hf hd hm hb hbound heads returnedHeads rows targets
    (fun _ h => h) (fun _ h => h) hrel hr' ht'
  apply insertion_word_values_eq q alpha rows targets ha hreturn
  intro row hrow
  have hheads := InsertionSupport.relation_heads (betaCode q alpha) factor hr'
  have hmember : row.1 ∈ stripLast heads := by
    rw [← hheads]
    have hm : row.1 ∈ (stripLast rows).map Prod.fst := List.mem_map.mpr ⟨row, hrow, rfl⟩
    simpa only [stripLast, List.map_reverse, List.map_tail] using hm
  exact ⟨hconditions.2.1.nodes row.1 hmember,
    hbounds row.1 (Hereditary.FinePredecessor.stripLast_mem _ _ hmember)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextSelectionValues
