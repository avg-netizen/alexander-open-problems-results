import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertionOrderSupport

/-!
# Actual factor frames at the same child preserve strict input order

The final-epsilon append test is monotone toward smaller factors. When
both append, their final factors compare; when both insert, the genuine
paired-table comparison applies. Smaller append versus larger insertion
compares at the strictly raised old head, regardless of the smaller
appended suffix. Real Factor outputs and the same independently executed
complete child derive every joint caller. Different-child non-M input
order remains separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FrameFactorOrder

open PublicEpsilonUnboundedIota SourceTrackingSequences
open InsertionSupport (Row)

theorem appendCheck_smaller (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (left right : Nat)
    (hl : lowCheckCode q left = true)
    (hlt : interpretation q left < interpretation q right)
    (hr : BranchesSupport.appendCheck q right heads = true) :
    BranchesSupport.appendCheck q left heads = true := by
  have hs := (BranchesSupport.appendCheck_exact q right heads hh).mp hr
  exact (BranchesSupport.appendCheck_exact q left heads hh).mpr
    ⟨hs.1, hs.2.1, hl, hlt.le.trans hs.2.2.2⟩

/-- Insertion changes an original head strictly upward, so every suffix
on the entire unchanged original head list still lies strictly below the
actual insertion word. No prefix length is assumed. -/
theorem heads_suffix_lex (q : Nat) (rows : List Row) (suffix : List Nat)
    (hne : rows ≠ [])
    (hrows : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation q row.1 < interpretation q (Insertion.firstCode row.2)) :
    List.Lex (· < ·) ((rows.map Prod.fst ++ suffix).map (interpretation q))
      ((Insertion.word q rows).map (interpretation q)) := by
  cases hs : Insertion.choose q rows with
  | none =>
    cases rows with
    | nil => exact False.elim (hne rfl)
    | cons row rest =>
      have hr := hrows row List.mem_cons_self
      rw [(Insertion.word_default q row rest hs).1]
      simp only [List.map_append, List.map_cons, List.map_map, List.cons_append]
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
    rw [hw, he]
    simp only [List.map_append, List.map_cons, List.map_map,
      List.append_assoc, List.cons_append]
    cases ho : current.2 with
    | nil => exact False.elim (hr.1 ho)
    | cons d ds =>
      simp only [ho, List.map_cons]
      exact List.Lex.append_left (· < ·)
        (List.Lex.rel (by simpa only [Insertion.firstCode, ho,
          List.head?_cons, Option.getD_some] using hr.2)) _

theorem insertion_heads_suffix_lex (q factor : Nat) (heads suffix out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hone : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : out ∈ Insertion.execute ((q, factor), heads)) :
    List.Lex (· < ·) ((heads ++ suffix).map (interpretation q))
      (out.map (interpretation q)) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  have hheads := InsertionSupport.relation_heads q factor hrel
  have hne : rows ≠ [] := by
    intro he
    have hn := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hh).1
    exact hn (by simpa only [he, List.map_nil] using hheads.symm)
  have hstrict : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation q row.1 < interpretation q (Insertion.firstCode row.2) := by
    intro row hrow
    have hs := InsertionSupport.relation_members q factor hrel row hrow
    exact FrameOrderSupport.replacement_first_gt_head q heads hh row.1 factor hs.1
      hf hm hone hb row.2 hs.2
  simpa only [hheads, hout] using heads_suffix_lex q rows suffix hne hstrict

/-- Both printed procedures at the same literal independently checked
headword preserve strict factor order. All selector and append conditions
are inspected from their actual executions. -/
theorem branches_factors_lex (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (left right : Nat)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q right))
    (hone : 1 < interpretation q right)
    (hbl : interpretation q left ≤ interpretation q (lastCode heads))
    (hbr : interpretation q right ≤ interpretation q (lastCode heads))
    (hlt : interpretation q left < interpretation q right) (xs ys : List Nat)
    (hx : xs ∈ Branches.execute ((q, left), heads))
    (hy : ys ∈ Branches.execute ((q, right), heads)) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  rcases Branches.execute_branch q left heads xs hx with ⟨hax, rfl⟩ | ⟨hax, hix⟩
  · rcases Branches.execute_branch q right heads ys hy with ⟨hay, rfl⟩ | ⟨hay, hiy⟩
    · simp only [List.map_append, List.map_singleton]
      exact List.Lex.append_left (· < ·) (List.Lex.rel hlt) _
    · exact insertion_heads_suffix_lex q right heads [left] ys hh hr hmr hone hbr hiy
  · rcases Branches.execute_branch q right heads ys hy with ⟨hay, rfl⟩ | ⟨hay, hiy⟩
    · have hm := appendCheck_smaller q heads hh left right hl hlt hay
      rw [hax] at hm
      cases hm
    · exact InsertionOrderSupport.execute_lex q heads hh left right hl hr hml hmr
        hone hbl hbr hlt xs ys hix hiy

/-- Two real factor outputs with the same written recursive prefix and
strict original input order derive strict factors. The independent SAME
child execution supplies its full tracker and both honest FINAL callers,
so the complete actual factor frames strictly compare in VALUES. -/
theorem execute_same_prefix_lex (q leftInput rightInput prefix left right : Nat)
    (heads xs ys : List Nat)
    (hl : (prefix, left) ∈ Factor.execute q leftInput)
    (hr : (prefix, right) ∈ Factor.execute q rightInput)
    (hh : heads ∈ Assignment.execute q prefix)
    (hlt : interpretation q leftInput < interpretation q rightInput)
    (hx : xs ∈ Branches.execute ((q, left), heads))
    (hy : ys ∈ Branches.execute ((q, right), heads)) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨_, _, _, hll, _, _, _, _, hml, honel, hprodleft, _, _⟩ :=
    Factor.execute_spec q leftInput (prefix, left) hl
  obtain ⟨_, _, _, hlr, _, _, _, _, hmr, honer, hprodright, _, _⟩ :=
    Factor.execute_spec q rightInput (prefix, right) hr
  have hs := (Assignment.execute_spec q prefix heads hh).2.1
  have hbl := (Factor.Bounds.execute_last_le_prefix_last q leftInput (prefix, left) hl).trans hs.2.2.1
  have hbr := (Factor.Bounds.execute_last_le_prefix_last q rightInput (prefix, right) hr).trans hs.2.2.1
  have hf : interpretation q left < interpretation q right := by
    apply lt_of_not_ge
    intro hle
    have hmul := mul_le_mul_right hle (interpretation q prefix)
    exact hlt.not_ge (by rw [hprodleft, hprodright]; exact hmul)
  exact branches_factors_lex q heads hs.1 left right hll hlr hml hmr honer hbl hbr hf xs ys hx hy

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FrameFactorOrder
