import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentCoverPrefix

/-!
# Genuine lexical increase of an original source-one factor frame

Every actually raised replacement starts strictly above its unchanged
written head. An actual singleton product also increases that head when
the real factor is greater than one. The executing greatest insertion
therefore increases the whole child word at its genuine replaced row,
including the default row. Actual factor and joint final bounds supply
all callers. This compares a frame with its child; comparisons between
two nonmultiplicative inputs remain separate. No Native base-one parser,
replacement FIRST, selection index or assigned word is supplied. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FrameOrderSupport

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton)

/-- The real raised M tracker supplies a strict first-value bound, before
its actual source-zero return preserves that value. -/
theorem raised_first_strict (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (ho : out ∈ Replacement.raisedReplacement head factor) :
    interpretation 0 head < interpretation 0 (Insertion.firstCode out) := by
  obtain ⟨raised, hr, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := ReplacementSupport.raisedWord_spec head factor raised hh hf hm hlt hr
  have ht := (NativeContext.SourceTrackingSequences.trackingCheck_exact _ raised).mp hs.1
  cases raised with
  | nil => exact False.elim (ht.1 rfl)
  | cons c cs =>
    have hc := hs.2.2 c List.mem_cons_self
    have hd := SkSourcePathSupport.entryCode_spec _ c hc.1 hc.2.2
    have hfirst : interpretation 0 head <
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c := by
      cases cs with
      | nil =>
        have hv : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c =
            interpretation 0 factor := by simpa only [lastCode_singleton] using hs.2.1
        rw [hv]; exact hlt
      | cons b bs =>
        have hp := ht.2.1
        rw [NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support.stripLast_cons_nonempty
          c (b :: bs) (List.cons_ne_nil _ _)] at hp
        have hv := NativeContext.PublicEpsilonUnboundedIota.Mu.root_base_lt _ c hp.first
        simpa only [(ReplacementSupport.raisedBaseCode_spec head hh).2.1] using hv
    simpa only [Replacement.returnWord, List.map_cons, Insertion.firstCode,
      List.head?_cons, Option.getD_some, hd.2] using hfirst

/-- Both genuine conditional alternatives strictly increase the written
head when the independently supplied source factor is greater than one. -/
theorem conditional_first_strict (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute head factor) :
    out ≠ [] ∧ interpretation 0 head < interpretation 0 (Insertion.firstCode out) := by
  have hs := ConditionalReplacement.execute_spec heads hh head factor hhead hf hm hb out ho
  refine ⟨hs.1, ?_⟩
  rcases hs.2.2.2.2 with hraised | hsmall
  · exact raised_first_strict head factor out
      (ConditionalReplacement.raised_member_caller heads hh head factor hhead hraised.1 hb).2
      hf hm hraised.1 hraised.2
  · obtain ⟨d, he, hv⟩ := hsmall.2
    have hp := (ConditionalReplacement.tracking_member_principal heads hh head hhead).2.1
    have hlt : interpretation 0 head < interpretation 0 head * interpretation 0 factor := by
      simpa only [Ordinal.mul_one] using mul_lt_mul_of_pos_left hone hp
    simpa only [he, Insertion.firstCode, List.head?_cons, Option.getD_some, hv] using hlt

/-- The actual selector changes its first replaced row to a strictly
larger first value. The literal heads before that row remain unchanged. -/
theorem rows_word_lex (rows : List Row) (hne : rows ≠ [])
    (hfirst : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation 0 row.1 < interpretation 0 (Insertion.firstCode row.2)) :
    List.Lex (· < ·) (rows.map (fun row => interpretation 0 row.1))
      ((Insertion.word rows).map (interpretation 0)) := by
  cases hs : Insertion.choose rows with
  | none =>
    cases rows with
    | nil => exact False.elim (hne rfl)
    | cons row rest =>
      have hr := hfirst row List.mem_cons_self
      rw [(Insertion.word_default row rest hs).1]
      cases he : row.2 with
      | nil => exact False.elim (hr.1 he)
      | cons c cs =>
        have hlt : interpretation 0 row.1 < interpretation 0 c := by
          simpa only [he, Insertion.firstCode, List.head?_cons, Option.getD_some] using hr.2
        simp only [List.map_cons]
        exact List.Lex.rel hlt
  | some selected =>
    obtain ⟨before, current, after, hn, he, hw, hc, hnone⟩ :=
      Insertion.word_selected rows selected.1 selected.2 hs
    have hmem : current ∈ rows := by
      rw [he]
      exact List.mem_append_right _ List.mem_cons_self
    have hr := hfirst current hmem
    cases ht : current.2 with
    | nil => exact False.elim (hr.1 ht)
    | cons c cs =>
      have hlt : interpretation 0 current.1 < interpretation 0 c := by
        simpa only [ht, Insertion.firstCode, List.head?_cons, Option.getD_some] using hr.2
      have hlex : List.Lex (· < ·)
          (interpretation 0 current.1 :: after.map (fun row => interpretation 0 row.1))
          (interpretation 0 c :: cs.map (interpretation 0)) := List.Lex.rel hlt
      have hleft : rows.map (fun row => interpretation 0 row.1) =
          before.map (fun row => interpretation 0 row.1) ++
            interpretation 0 current.1 :: after.map (fun row => interpretation 0 row.1) := by
        rw [he, List.map_append, List.map_cons]
      have hright : (Insertion.word rows).map (interpretation 0) =
          before.map (fun row => interpretation 0 row.1) ++
            interpretation 0 c :: cs.map (interpretation 0) := by
        simp only [hw, List.map_append, List.map_map, ht, List.map_cons]
      rw [hleft, hright]
      exact List.Lex.append_left (· < ·) hlex (before.map (fun row => interpretation 0 row.1))

/-- All replacement-row first values come from real sequential
executions, so every actual insertion strictly increases the child word. -/
theorem insertion_word_lex (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (factor : Nat)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (out : List Nat) (ho : out ∈ Insertion.execute (factor, heads)) :
    List.Lex (· < ·) (heads.map (interpretation 0)) (out.map (interpretation 0)) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hne : rows ≠ [] := by
    intro hn
    have hz : heads = [] := hheads.symm.trans (by rw [hn]; rfl)
    exact ((SourceTrackingRaw.trackingCheck_exact heads).mp hh).1 hz
  have hrows := rows_word_lex rows hne (fun row hrow => by
    have hs := InsertionSupport.relation_members factor hrel row hrow
    exact conditional_first_strict heads hh row.1 factor hs.1 hf hm hone hb row.2 hs.2)
  rw [← hheads, ← hout]
  simpa only [List.map_map] using hrows

/-- The printed append is a proper extension; the genuine fallback
insertion is strict at its computed replaced row, including default. -/
theorem branches_word_lex (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (factor : Nat)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (out : List Nat) (ho : out ∈ Branches.execute (factor, heads)) :
    List.Lex (· < ·) (heads.map (interpretation 0)) (out.map (interpretation 0)) := by
  rcases Branches.execute_branch factor heads out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · rw [he, List.map_append, List.map_singleton]
    simpa only [List.append_nil] using List.Lex.append_left (· < ·)
      (List.Lex.nil : List.Lex (· < ·) ([] : List Ordinal.{0}) [interpretation 0 factor])
      (heads.map (interpretation 0))
  · exact insertion_word_lex heads hh factor hf hm hone hb out hi

/-- Actual factor removal and the independently executed child derive
the honest joint caller; the whole frame genuinely increases that child. -/
theorem execute_factor_frame_lex (input prefix factor : Nat) (heads out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute input)
    (hh : heads ∈ Assignment.execute prefix)
    (ho : out ∈ Branches.execute (factor, heads)) :
    List.Lex (· < ·) (heads.map (interpretation 0)) (out.map (interpretation 0)) := by
  obtain ⟨_, _, hfactor, _, _, _, hm, hone, _, _, _⟩ := Factor.execute_spec input _ hf
  have hlow := ((Theta.acceptedLowCode_iff 0 factor).mp hfactor).1
  have hlast : interpretation 0 factor ≤ interpretation 0 (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last input _ hf).trans
      (Assignment.execute_last_bounds prefix heads hh).1
  exact branches_word_lex heads (Assignment.execute_tracking prefix heads hh)
    factor hlow hm hone hlast out ho

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FrameOrderSupport
