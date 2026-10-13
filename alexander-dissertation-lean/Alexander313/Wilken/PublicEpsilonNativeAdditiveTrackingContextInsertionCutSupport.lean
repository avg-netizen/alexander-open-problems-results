import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextSelectionValues
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingSmallInsertionIntervalOrderSupport

/-!
# Actual retained cuts expose independently executing insertion suffixes

The genuine chronological row relation has an exact converse: every row
already contains its actual partial conditional execution, so finite fix
induction reconstructs the real sequential table. At a computed passing
adjacency, right-priority selection retains the literal earlier heads and
executes the same insertion procedure on the remaining head suffix. The
suffix membership and whole-word equality are conclusions, not contextual
assignment-composition premises. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextInsertionCutSupport

open InsertionSupport (Row Matches)
open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_split)

/-- Concrete chronological conditional memberships reconstruct the actual
finite table execution with its literal already-written accumulator. -/
theorem loop_of_relation (q factor : Nat) {heads : List Nat} {rows : List Row}
    (hr : List.Forall₂ (Matches q factor) heads rows) (prefix : List Row) :
    prefix ++ rows ∈ InsertionSupport.loop ((q, factor), (heads, prefix)) := by
  induction hr generalizing prefix with
  | nil =>
    simp only [List.append_nil]
    exact PFun.mem_fix_iff.mpr (Or.inl (by
      rw [InsertionSupport.step_nil]
      exact Part.mem_some _))
  | @cons head row heads rows hrow hrest ih =>
    have he : (head, row.2) = row := Prod.ext hrow.1.symm rfl
    have hs : Sum.inr ((q, factor), (heads, prefix ++ [row])) ∈
        InsertionSupport.step ((q, factor), (head :: heads, prefix)) := by
      rw [InsertionSupport.step_cons]
      simpa only [he] using Part.mem_map
        (fun word => Sum.inr ((q, factor), (heads, prefix ++ [(head, word)]))) hrow.2
    have ht := ih (prefix ++ [row])
    have hf := PFun.mem_fix_iff.mpr (Or.inr
      ⟨((q, factor), (heads, prefix ++ [row])), hs, ht⟩)
    simpa only [List.append_assoc, List.singleton_append] using hf

theorem executeRows_of_relation (q factor : Nat) {heads : List Nat} {rows : List Row}
    (hr : List.Forall₂ (Matches q factor) heads rows) :
    rows ∈ InsertionSupport.executeRows q factor heads := by
  simpa only [InsertionSupport.executeRows, List.nil_append] using
    loop_of_relation q factor hr []

theorem relation_split (q factor : Nat) (before after : List Nat) (rows : List Row)
    (hr : List.Forall₂ (Matches q factor) (before ++ after) rows) :
    ∃ prefix rest, rows = prefix ++ rest ∧
      List.Forall₂ (Matches q factor) before prefix ∧
        List.Forall₂ (Matches q factor) after rest := by
  induction before generalizing rows with
  | nil => exact ⟨[], rows, rfl, .nil, hr⟩
  | cons head before ih =>
    obtain ⟨row, tail, hrow, htail, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨prefix, rest, he, hp, ht⟩ := ih tail htail
    refine ⟨row :: prefix, rest, ?_, .cons hrow hp, ht⟩
    simpa only [List.cons_append] using congrArg (List.cons row) he

/-- The boundary cover is the actual computed test. Every later passing
transition takes priority in both the whole table and its own suffix. -/
theorem word_passing_cut (q : Nat) (before : List Row) (previous current : Row)
    (after : List Row)
    (hc : Insertion.coverCheck q previous.1 (Insertion.firstCode current.2) = true) :
    Insertion.word q (before ++ previous :: current :: after) =
      (before.map Prod.fst ++ [previous.1]) ++ Insertion.word q (current :: after) := by
  induction before with
  | nil =>
    cases hs : Insertion.choose q (current :: after) with
    | some selected =>
      simpa only [List.map_nil, List.nil_append, List.singleton_append] using
        SmallInsertionIntervalOrderSupport.word_cons_some q previous _ selected hs
    | none =>
      have hp : Insertion.choose q (previous :: current :: after) = some (1, current.2) := by
        simp only [Insertion.choose_pair, hs, hc, Bool.cond_true]
      simp only [List.map_nil, List.nil_append, Insertion.word, hp, hs,
        List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.head?_cons, Option.getD_some, List.singleton_append]
  | cons row before ih =>
    obtain ⟨n, word, hs, hn⟩ :=
      AssignmentCoverPrefixSupport.choose_after_passing q before previous current after hc
    simpa only [List.cons_append, List.map_cons,
      SmallInsertionIntervalOrderSupport.word_cons_some q row _ (n, word) hs] using
        congrArg (List.cons row.1) ih

/-- Actual full-table execution derives a concrete independently executing
suffix table at every literal chronological cut. -/
theorem executeRows_split (q factor : Nat) (before after : List Nat) (rows : List Row)
    (ho : rows ∈ InsertionSupport.executeRows q factor (before ++ after)) :
    ∃ prefix rest, rows = prefix ++ rest ∧ prefix.map Prod.fst = before ∧
      rest ∈ InsertionSupport.executeRows q factor after := by
  obtain ⟨prefix, rest, he, hp, ht⟩ := relation_split q factor before after rows
    (InsertionSupport.executeRows_relation q factor _ rows ho)
  exact ⟨prefix, rest, he, InsertionSupport.relation_heads q factor hp,
    executeRows_of_relation q factor ht⟩

/-- A genuine passing cut in an actually executed table derives the exact
literal retained prefix followed by the independently executing insertion
of the remaining heads. No suffix output or procedure equality is given. -/
theorem insertion_at_passing_cut (q factor : Nat) (before : List Nat)
    (previous current : Row) (after : List Row) (prefix : List Row)
    (rows : List Row) (out : List Nat)
    (hr : rows ∈ InsertionSupport.executeRows q factor
      (before ++ previous.1 :: current.1 :: after.map Prod.fst))
    (hp : prefix.map Prod.fst = before)
    (he : rows = prefix ++ previous :: current :: after)
    (hc : Insertion.coverCheck q previous.1 (Insertion.firstCode current.2) = true)
    (ho : out ∈ Insertion.execute ((q, factor),
      before ++ previous.1 :: current.1 :: after.map Prod.fst)) :
    ∃ suffix, suffix ∈ Insertion.execute ((q, factor), current.1 :: after.map Prod.fst) ∧
      out = (before ++ [previous.1]) ++ suffix := by
  have hrelation := InsertionSupport.executeRows_relation q factor _ rows hr
  have hheads : before ++ previous.1 :: current.1 :: after.map Prod.fst =
      (before ++ [previous.1]) ++ (current.1 :: after.map Prod.fst) := by
    simp only [List.append_assoc, List.singleton_append]
  have htail : List.Forall₂ (Matches q factor)
      (current.1 :: after.map Prod.fst) (current :: after) := by
    have hlen : (prefix ++ [previous]).length = (before ++ [previous.1]).length := by
      simpa only [List.length_append, List.length_singleton, List.length_map] using
        congrArg (fun xs : List Nat => xs.length + 1) hp
    have hrows : rows = (prefix ++ [previous]) ++ (current :: after) := by
      simpa only [List.append_assoc, List.singleton_append] using he
    have hrel : List.Forall₂ (Matches q factor)
        ((before ++ [previous.1]) ++ (current.1 :: after.map Prod.fst))
        ((prefix ++ [previous]) ++ (current :: after)) := by
      simpa only [hheads, hrows] using hrelation
    have hd := List.forall₂_drop_append _ (prefix ++ [previous]) (current :: after) hrel
    simpa only [hlen, List.drop_left] using hd
  have hs := executeRows_of_relation q factor htail
  have houtput : out = Insertion.word q rows := by
    obtain ⟨otherRows, hm, hword⟩ := (Part.mem_map_iff _).mp ho
    have heq := Part.mem_unique hr hm
    simpa only [heq] using hword.symm
  refine ⟨Insertion.word q (current :: after), Part.mem_map _ hs, ?_⟩
  rw [houtput, he, word_passing_cut q prefix previous current after hc, hp]

/-- Genuine executed replacement bounds construct the passing boundary
internally, then derive the independently executing suffix and exact cut. -/
theorem insertion_covered_cut (q factor : Nat) (before : List Nat) (current : Nat)
    (after out : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck q (before ++ current :: after) = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode (before ++ current :: after)))
    (eta : Ordinal.{0}) (heta : 0 < eta)
    (hbound : ∀ c ∈ before ++ current :: after, interpretation q c ≤ eta)
    (hraw : SourceTrackingRaw.Support.inputCheck q (lastCode before) = true)
    (hcover : eta * interpretation q factor ≤ SourceTrackingRaw.Support.muValue q (lastCode before))
    (ho : out ∈ Insertion.execute ((q, factor), before ++ current :: after)) :
    ∃ suffix, suffix ∈ Insertion.execute ((q, factor), current :: after) ∧
      out = before ++ suffix := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  have hrelation := InsertionSupport.executeRows_relation q factor _ rows hr
  obtain ⟨last, he, hhmem⟩ := stripLast_split before hne
  have hlast : lastCode before = last := by rw [he, lastCode_append_singleton]
  have hrelation' : List.Forall₂ (Matches q factor)
      (stripLast before ++ last :: current :: after) rows := by
    rw [he, List.append_assoc, List.singleton_append] at hrelation
    exact hrelation
  obtain ⟨prefix, a, b, rest, hrows, hp, ha, hbrow, hcall⟩ :=
    SmallInsertionIntervalOrderSupport.rows_at_cut q factor (stripLast before)
      last current after rows hrelation'
  have hmember : current ∈ before ++ current :: after :=
    List.mem_append_right _ List.mem_cons_self
  have hs := ConditionalReplacement.execute_spec q _ hh current factor hmember hf hm hb b.2 hcall
  have hl := AssignmentValueSupport.firstCode_low q b.2 hs.1 (fun c hc => (hs.2.1 c hc).1)
  have hupper := (Bounds.conditional_bounds q _ hh current factor hmember hf hm hb eta heta
    (hbound current hmember) b.2 hcall).2.2
  have hfirstmem : Insertion.firstCode b.2 ∈ b.2 := by
    cases hw : b.2 with
    | nil => exact False.elim (hs.1 hw)
    | cons d ds =>
      simp only [Insertion.firstCode, hw, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  have hfirst := hupper (Insertion.firstCode b.2) hfirstmem
  have hc : Insertion.coverCheck q a.1 (Insertion.firstCode b.2) = true := by
    apply (Insertion.coverCheck_exact q _ _).mpr
    simpa only [ha, ← hlast] using And.intro hraw (And.intro hl (hfirst.trans hcover))
  have hactual : stripLast before ++ a.1 :: b.1 :: rest.map Prod.fst =
      before ++ current :: after := by
    calc
      _ = (prefix ++ a :: b :: rest).map Prod.fst := by
        simp only [List.map_append, List.map_cons, hp]
      _ = rows.map Prod.fst := congrArg (List.map Prod.fst) hrows.symm
      _ = before ++ current :: after := InsertionSupport.relation_heads q factor hrelation
  have htail : b.1 :: rest.map Prod.fst = current :: after := by
    apply List.append_cancel_left (as := stripLast before ++ [last])
    calc
      (stripLast before ++ [last]) ++ (b.1 :: rest.map Prod.fst) =
          stripLast before ++ a.1 :: b.1 :: rest.map Prod.fst := by
        simp only [List.append_assoc, List.singleton_append, ha]
      _ = before ++ current :: after := hactual
      _ = (stripLast before ++ [last]) ++ (current :: after) := by rw [← he]
  obtain ⟨suffix, hsuffix, heq⟩ := insertion_at_passing_cut q factor
    (stripLast before) a b rest prefix rows out (by simpa only [hactual] using hr)
      hp hrows hc (by simpa only [hactual] using ho)
  refine ⟨suffix, by simpa only [htail] using hsuffix, ?_⟩
  simpa only [ha, ← he] using heq

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextInsertionCutSupport
