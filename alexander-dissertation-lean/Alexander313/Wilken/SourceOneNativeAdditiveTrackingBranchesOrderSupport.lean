import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertionOrderSupport

/-!
# Actual printed branch order at one original source-one child word

The real append cover is monotone downwards in its factor. Hence a larger
append derives a smaller append. Two actual appends compare their final
factors; two actual insertions use the proved paired-row scan. If only the
smaller appends, the greater insertion changes an actual row strictly,
before any appended smaller-factor suffix can matter. Every guard derives
from actual original check-zero headword/factor admission and honest joint
final bounds. No branch, selection index or output comparison is supplied.
Different-child and general non-M input order remain separate. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.BranchesOrderSupport

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode)

/-- A genuine greatest insertion strictly changes an actual written row,
so its VALUE order also exceeds the child followed by any finite suffix. -/
theorem rows_word_lex_suffix (rows : List Row) (suffix : List Nat)
    (hne : rows ≠ [])
    (hfirst : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation 0 row.1 < interpretation 0 (Insertion.firstCode row.2)) :
    List.Lex (· < ·) ((rows.map Prod.fst ++ suffix).map (interpretation 0))
      ((Insertion.word rows).map (interpretation 0)) := by
  cases hs : Insertion.choose rows with
  | none =>
    cases rows with
    | nil => exact False.elim (hne rfl)
    | cons row rest =>
      have hr := hfirst row List.mem_cons_self
      rw [(Insertion.word_default row rest hs).1]
      simpa only [List.map_cons, List.cons_append] using
        InsertionOrderSupport.retained_first_lex row.1 (rest.map Prod.fst ++ suffix)
          row.2 hr.1 hr.2
  | some selected =>
    obtain ⟨before, current, after, hn, he, hw, hc, hnone⟩ :=
      Insertion.word_selected rows selected.1 selected.2 hs
    have hmem : current ∈ rows := by
      rw [he]
      exact List.mem_append_right _ List.mem_cons_self
    have hr := hfirst current hmem
    have hleft : ((rows.map Prod.fst ++ suffix).map (interpretation 0)) =
        before.map (fun row => interpretation 0 row.1) ++
          interpretation 0 current.1 :: ((after.map Prod.fst ++ suffix).map (interpretation 0)) := by
      simp only [he, List.map_append, List.map_cons, List.map_map,
        List.append_assoc, List.cons_append]
    have hright : (Insertion.word rows).map (interpretation 0) =
        before.map (fun row => interpretation 0 row.1) ++ current.2.map (interpretation 0) := by
      simp only [hw, List.map_append, List.map_map]
    rw [hleft, hright]
    exact List.Lex.append_left (· < ·)
      (by simpa only [List.map_cons] using
        InsertionOrderSupport.retained_first_lex current.1 (after.map Prod.fst ++ suffix)
          current.2 hr.1 hr.2) (before.map (fun row => interpretation 0 row.1))

/-- Real independently executed conditional rows derive every strict
FIRST caller, so actual insertion exceeds the whole child plus any suffix. -/
theorem execute_insertion_lex_suffix (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (factor : Nat)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (suffix out : List Nat) (ho : out ∈ Insertion.execute (factor, heads)) :
    List.Lex (· < ·) ((heads ++ suffix).map (interpretation 0))
      (out.map (interpretation 0)) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hne : rows ≠ [] := by
    intro he
    have hn : heads = [] := hheads.symm.trans (by simp only [he, List.map_nil])
    exact ((SourceTrackingRaw.trackingCheck_exact heads).mp hh).1 hn
  have hs := rows_word_lex_suffix rows suffix hne (fun row hrow => by
    have hr := InsertionSupport.relation_members factor hrel row hrow
    exact FrameOrderSupport.conditional_first_strict heads hh row.1 factor hr.1 hf hm
      hone hb row.2 hr.2)
  simpa only [hheads, hout] using hs

/-- The unchanged actual final-eligibility flag and real original mu
cover derive append for every smaller admitted factor. -/
theorem appendCheck_smaller (heads : List Nat) (left right : Nat)
    (hl : lowCheckCode 0 left = true)
    (hlt : interpretation 0 left ≤ interpretation 0 right)
    (hr : BranchesSupport.appendCheck right heads = true) :
    BranchesSupport.appendCheck left heads = true := by
  have hc := Bool.and_eq_true.mp hr
  have hp := (Insertion.coverCheck_exact (lastCode heads) right).mp hc.2
  have hlcover : Insertion.coverCheck (lastCode heads) left = true :=
    (Insertion.coverCheck_exact _ _).mpr ⟨hp.1, hl, hlt.trans hp.2.2⟩
  exact Bool.and_eq_true.mpr ⟨hc.1, hlcover⟩

/-- Both actual printed branch programs at one unchanged original child
are strictly ordered by increasing multiplicative factors. No branch or
selected location is a premise: the real tests derive all four cases. -/
theorem execute_branches_lex (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (left right : Nat)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hbl : interpretation 0 left ≤ interpretation 0 (lastCode heads))
    (hbr : interpretation 0 right ≤ interpretation 0 (lastCode heads))
    (hlt : interpretation 0 left < interpretation 0 right) (xs ys : List Nat)
    (hx : xs ∈ Branches.execute (left, heads))
    (hy : ys ∈ Branches.execute (right, heads)) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have hone : 1 < interpretation 0 right := (Order.one_le_iff_pos.mpr hml.1).trans_lt hlt
  rcases Branches.execute_branch left heads xs hx with ⟨hax, hex⟩ | ⟨hax, hix⟩
  · rcases Branches.execute_branch right heads ys hy with ⟨hay, hey⟩ | ⟨hay, hiy⟩
    · rw [hex, hey, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
      exact List.Lex.append_left (· < ·) (List.Lex.rel hlt) (heads.map (interpretation 0))
    · rw [hex]
      exact execute_insertion_lex_suffix heads hh right hr hmr hone hbr [left] ys hiy
  · rcases Branches.execute_branch right heads ys hy with ⟨hay, hey⟩ | ⟨hay, hiy⟩
    · have he := appendCheck_smaller heads left right hl hlt.le hay
      rw [hax] at he
      cases he
    · exact InsertionOrderSupport.execute_insertion_lex heads hh left right hl hr hml hmr
        hbl hbr hlt xs ys hix hiy

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.BranchesOrderSupport
