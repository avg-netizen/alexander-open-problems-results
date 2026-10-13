import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Every actual non-M factor frame increases its child word

The real raised multiplicative word consists of genuine HIGH proper-prefix
roots and its actual final factor, all strictly above the raised base. Its
original-source return preserves those values. The other replacement is
the actual head times a factor greater than one, also strictly above that
head. Therefore the concrete right-priority insertion first differs at a
strictly larger value, while append is a proper extension. The full
inter-input non-M lexical comparison remains separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FrameOrderSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open InsertionSupport (Row)

/-- All actual raised M-word entries are strictly above the original head.
The written proper prefix supplies genuine HIGH callers; its final entry
has the independently searched original factor value. -/
theorem raised_word_member_gt_head (q head factor : Nat) (word : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (hw : word ∈ ReplacementSupport.raisedWord q head factor) :
    ∀ d ∈ word, interpretation q head <
      interpretation (ReplacementSupport.raisedBaseCode q head) d := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative q head factor c hh hf hm hlt hc
  have hs := ReplacementSupport.raisedSearch_spec q head factor c hh hf hc
  have hr := SourceMultiplicativePrincipal.rootInput _ c hi
  have hb := (ReplacementSupport.raisedBaseCode_spec q head hh).2.1
  intro d hd
  rcases ReplacementSupport.rawWord_member _ c d hd with rfl | hprefix
  · rw [hs.2.2]
    exact hlt
  · have hhigh := SourceMultiplicativeTracking.properPrefix_roots _ _ hr d hprefix
    simpa only [hb] using Mu.root_base_lt _ d hhigh

/-- Whole returned VALUES, rather than source spelling, preserve the
strict lower bound at every raised replacement entry. -/
theorem raised_replacement_member_gt_head (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (ho : out ∈ Replacement.raisedReplacement q head factor) :
    ∀ d ∈ out, interpretation q head < interpretation q d := by
  obtain ⟨word, hw, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec q head factor out hh hf hm hlt ho
  intro d hd
  have hmem : interpretation q d ∈ word.map
      (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
    rw [← hv]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
  rw [← he]
  exact raised_word_member_gt_head q head factor word hh hf hm hlt hw a ha

/-- On the actual joint headword/factor domain, every conditional result
begins strictly above the head it replaces. The small case uses the
genuine positive head and factor>1, not an independent tracker premise. -/
theorem replacement_first_gt_head (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute q head factor) :
    out ≠ [] ∧ interpretation q head < interpretation q (Insertion.firstCode out) := by
  have hs := ConditionalReplacement.execute_spec q heads hh head factor hhead hf hm hb out ho
  refine ⟨hs.1, ?_⟩
  rcases hs.2.2 with hr | ⟨hle, d, he, hv⟩
  · have hraw := (ConditionalReplacement.raised_member_caller q heads hh head factor
      hhead hr.1 hb).2
    have hmem : Insertion.firstCode out ∈ out := by
      cases he : out with
      | nil => exact False.elim (hs.1 he)
      | cons d ds =>
        simp only [Insertion.firstCode, he, List.head?_cons, Option.getD_some]
        exact List.mem_cons_self
    exact raised_replacement_member_gt_head q head factor out hraw hf hm hr.1 hr.2.1 _ hmem
  · rw [he]
    change interpretation q head < interpretation q d
    rw [hv]
    have hp := (ConditionalReplacement.tracking_member_principal q heads hh head hhead).2.1
    simpa only [Ordinal.mul_one] using mul_lt_mul_of_pos_left hone hp

/-- The independently computed selector retains a common literal prefix
and replaces its next head by a strictly larger FIRST; the default uses
the first replacement. Thus every such actual row table increases VALUES. -/
theorem word_rows_lex (q : Nat) (rows : List Row) (hne : rows ≠ [])
    (hrows : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation q row.1 < interpretation q (Insertion.firstCode row.2)) :
    List.Lex (· < ·) (rows.map (fun row => interpretation q row.1))
      ((Insertion.word q rows).map (interpretation q)) := by
  cases hs : Insertion.choose q rows with
  | none =>
    cases rows with
    | nil => exact False.elim (hne rfl)
    | cons row rest =>
      have hr := hrows row List.mem_cons_self
      rw [(Insertion.word_default q row rest hs).1, List.map_cons]
      cases he : row.2 with
      | nil => exact False.elim (hr.1 he)
      | cons d ds =>
        simp only [he, List.map_cons]
        exact List.Lex.rel (by simpa only [Insertion.firstCode, he,
          List.head?_cons, Option.getD_some] using hr.2)
  | some e =>
    obtain ⟨before, current, after, hbefore, he, hw, hc, hn⟩ :=
      Insertion.word_selected q rows e.1 e.2 hs
    have hmem : current ∈ rows := by
      rw [he]
      exact List.mem_append_right _ List.mem_cons_self
    have hr := hrows current hmem
    rw [hw, he, List.map_append, List.map_cons, List.map_append, List.map_map]
    cases ho : current.2 with
    | nil => exact False.elim (hr.1 ho)
    | cons d ds =>
      simp only [ho, List.map_cons]
      exact List.Lex.append_left (· < ·)
        (List.Lex.rel (by simpa only [Insertion.firstCode, ho,
          List.head?_cons, Option.getD_some] using hr.2)) _

/-- Actual row executions derive every strict replacement caller before
the concrete insertion word is compared with its unchanged child heads. -/
theorem insertion_lex (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : out ∈ Insertion.execute ((q, factor), heads)) :
    List.Lex (· < ·) (heads.map (interpretation q)) (out.map (interpretation q)) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  have hheads := InsertionSupport.relation_heads q factor hrel
  have hne : rows ≠ [] := by
    intro he
    have hhne := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hh).1
    exact hhne (hheads.symm.trans (by rw [he]; rfl))
  have hstrict : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation q row.1 < interpretation q (Insertion.firstCode row.2) := by
    intro row hrow
    have hs := InsertionSupport.relation_members q factor hrel row hrow
    exact replacement_first_gt_head q heads hh row.1 factor hs.1 hf hm hone hb row.2 hs.2
  have ht := word_rows_lex q rows hne hstrict
  rw [← hout, ← hheads, List.map_map]
  exact ht

/-- Append is a proper extension; otherwise the independently executing
insertion first replaces an actual head by a strictly larger value. -/
theorem branches_lex (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    List.Lex (· < ·) (heads.map (interpretation q)) (out.map (interpretation q)) := by
  rcases Branches.execute_branch q factor heads out ho with ⟨ha, rfl⟩ | ⟨ha, hi⟩
  · rw [List.map_append, List.map_singleton]
    simpa only [List.append_nil] using List.Lex.append_left (· < ·)
      (List.Lex.nil : List.Lex (· < ·) ([] : List Ordinal.{0}) [interpretation q factor])
      (heads.map (interpretation q))
  · exact insertion_lex q factor heads out hh hf hm hone hb hi

/-- Every actually executed factor frame strictly increases the complete
independently computed child word. Its joint LF bound derives factor<=FINAL;
there is no supplied headword, factor bound or lexical comparison. -/
theorem execute_frame_lex (q input prefix factor : Nat) (heads out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute q input)
    (hh : heads ∈ Assignment.execute q prefix)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    List.Lex (· < ·) (heads.map (interpretation q)) (out.map (interpretation q)) := by
  obtain ⟨_, _, _, hlf, _, _, _, _, hm, hone, _, _, _⟩ :=
    Factor.execute_spec q input (prefix, factor) hf
  have hs := (Assignment.execute_spec q prefix heads hh).2.1
  have hb : interpretation q factor ≤ interpretation q (lastCode heads) :=
    (Factor.Bounds.execute_last_le_prefix_last q input (prefix, factor) hf).trans hs.2.2.1
  exact branches_lex q factor heads out hs.1 hlf hm hone hb ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FrameOrderSupport
