import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextAppendCheck

/-!
# Actual right-priority insertion scan under contextual original-zero return

Each paired row retains the genuine admitted original return of its head,
nonempty LOW replacements and their equal VALUES. Only proper lower rows
enter the real OWN contextual mu theorem. The concrete right-priority scan
then preserves the chosen position and complete replacement VALUES. The
actual chronological row executions derive these pairs, rather than taking
a selected index or assigned replacement as an oracle. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextSelectorSupport

open NativeContext.SourceTrackingSequences (lastCode)
open Hereditary.FinePredecessor (stripLast)

private theorem source_row_stripLast_append_singleton (rows : List InsertionSupport.Row)
    (row : InsertionSupport.Row) : stripLast (rows ++ [row]) = rows := by
  simp only [stripLast, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.tail_cons, List.reverse_reverse]

private theorem source_row_stripLast_cons_nonempty (a : InsertionSupport.Row)
    (rows : List InsertionSupport.Row) (hne : rows ≠ []) :
    stripLast (a :: rows) = a :: stripLast rows := by
  obtain ⟨last, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split rows hne
  calc
    stripLast (a :: rows) = stripLast ((a :: stripLast rows) ++ [last]) := by
      rw [← List.cons_append, ← he]
    _ = a :: stripLast rows := source_row_stripLast_append_singleton _ _

def RowMatches (q : Nat) (row other : InsertionSupport.Row) : Prop :=
  Replacement.EntryMatches q other.1 row.1 ∧ row.2 ≠ [] ∧
    (∀ d ∈ row.2, lowCheckCode 0 d = true) ∧ other.2 ≠ [] ∧
      (∀ c ∈ other.2, NativeContext.lowCheckCode q c = true) ∧
        row.2.map (interpretation 0) = other.2.map (NativeContext.interpretation q)

noncomputable def candidateValues (c : Insertion.Candidate) : Nat × List Ordinal.{0} :=
  (c.1, c.2.map (interpretation 0))

private theorem first_values_eq (q : Nat) (xs ys : List Nat) (hne : xs ≠ [])
    (hv : xs.map (interpretation 0) = ys.map (NativeContext.interpretation q)) :
    interpretation 0 (Insertion.firstCode xs) =
      NativeContext.interpretation q (NativeContext.SourceAdditiveTracking.Insertion.firstCode ys) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a xs =>
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b ys =>
      simpa only [Insertion.firstCode, NativeContext.SourceAdditiveTracking.Insertion.firstCode,
        List.head?_cons, Option.getD_some] using (List.cons.inj hv).1

private theorem source_first_low (xs : List Nat) (hne : xs ≠ [])
    (hl : ∀ c ∈ xs, lowCheckCode 0 c = true) : lowCheckCode 0 (Insertion.firstCode xs) = true := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a xs => simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using hl a List.mem_cons_self

/-- Actual proper lower predecessors derive every cover flag used by the
two independent scans. No final-row RAW caller is inferred. -/
theorem choose_values_eq (root : Nat) (rows otherRows : List InsertionSupport.Row)
    (ha : Mu.inputCheck root = true)
    (hrel : List.Forall₂ (RowMatches (alphaCode root)) rows otherRows)
    (hp : ∀ row ∈ stripLast otherRows,
      NativeContext.SourceTrackingRaw.Support.inputCheck (alphaCode root) row.1 = true ∧
        NativeContext.interpretation (alphaCode root) row.1 < Enclosure.sourceAlphaPlus root) :
    (Insertion.choose rows).map candidateValues =
      (NativeContext.SourceAdditiveTracking.Insertion.choose (alphaCode root) otherRows).map
        (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.candidateValues (alphaCode root)) := by
  revert hp
  induction hrel with
  | nil => intro hp; rfl
  | @cons a otherA rest otherRest hrow htail ih =>
    intro hp
    cases rest with
    | nil => cases htail; rfl
    | cons b later =>
      cases otherRest with
      | nil => cases htail
      | cons otherB otherLater =>
        cases htail with
        | cons hnext hrest =>
          have hrec := ih (fun row hr => hp row (by
            rw [source_row_stripLast_cons_nonempty otherA (otherB :: otherLater)
              (List.cons_ne_nil _ _)]
            exact List.mem_cons_of_mem _ hr))
          have hprevious := hp otherA (by
            rw [source_row_stripLast_cons_nonempty otherA (otherB :: otherLater)
              (List.cons_ne_nil _ _)]
            exact List.mem_cons_self)
          have hcov := ContextRowValues.coverCheck_eq root otherA.1 a.1
            (Insertion.firstCode b.2)
            (NativeContext.SourceAdditiveTracking.Insertion.firstCode otherB.2)
            ha hprevious.1 hrow.1 hprevious.2
            (source_first_low b.2 hnext.2.1 hnext.2.2.1)
            (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.firstCode_low
              (alphaCode root) otherB.2 hnext.2.2.2.1 hnext.2.2.2.2.1)
            (first_values_eq (alphaCode root) b.2 otherB.2 hnext.2.1 hnext.2.2.2.2.2)
          cases hl : Insertion.choose (b :: later) with
          | none =>
            cases ht : NativeContext.SourceAdditiveTracking.Insertion.choose (alphaCode root) (otherB :: otherLater) with
            | some c =>
              simp only [hl, ht, Option.map_none, Option.map_some, Option.none_ne_some] at hrec
            | none =>
              cases hc : Insertion.coverCheck a.1 (Insertion.firstCode b.2) <;>
                simp only [Insertion.choose_pair,
                  NativeContext.SourceAdditiveTracking.Insertion.choose_pair,
                  hl, ht, ← hcov, hc, Bool.cond_false, Bool.cond_true, Option.map_none, Option.map_some,
                  candidateValues, NativeContext.SourceAdditiveTracking.AssignmentValueSupport.candidateValues,
                  hnext.2.2.2.2.2]
          | some c =>
            cases ht : NativeContext.SourceAdditiveTracking.Insertion.choose (alphaCode root) (otherB :: otherLater) with
            | none =>
              simp only [hl, ht, Option.map_none, Option.map_some, Option.some_ne_none] at hrec
            | some d =>
              have he : candidateValues c =
                  NativeContext.SourceAdditiveTracking.AssignmentValueSupport.candidateValues (alphaCode root) d := by
                simpa only [hl, ht, Option.map_some, Option.some.injEq] using hrec
              have hn : c.1 = d.1 := congrArg Prod.fst he
              have hw : c.2.map (interpretation 0) = d.2.map (NativeContext.interpretation (alphaCode root)) :=
                congrArg Prod.snd he
              simp only [Insertion.choose_pair,
                NativeContext.SourceAdditiveTracking.Insertion.choose_pair, hl, ht, Option.map_some,
                candidateValues, NativeContext.SourceAdditiveTracking.AssignmentValueSupport.candidateValues, hn, hw]

theorem rows_values_eq {q : Nat} {rows otherRows : List InsertionSupport.Row}
    (hr : List.Forall₂ (RowMatches q) rows otherRows) :
    rows.map ContextRowValues.rowValues = otherRows.map
      (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues q) := by
  induction hr with
  | nil => rfl
  | cons hd ht ih =>
    simp only [List.map_cons, ContextRowValues.rowValues,
      NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues,
      hd.1.2, hd.2.2.2.2.2, ih]

theorem source_default_values_eq (q : Nat) (rows otherRows : List InsertionSupport.Row)
    (hv : rows.map ContextRowValues.rowValues = otherRows.map
      (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues q)) :
    ((rows.head?.getD (0, [])).2).map (interpretation 0) =
      ((otherRows.head?.getD (0, [])).2).map (NativeContext.interpretation q) := by
  cases rows with
  | nil =>
    have hn : otherRows = [] := List.map_eq_nil_iff.mp hv.symm
    subst otherRows
    rfl
  | cons a rows =>
    cases otherRows with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b otherRows =>
      simpa only [List.head?_cons, Option.getD_some] using congrArg Prod.snd (List.cons.inj hv).1

theorem source_take_heads_values_eq (q n : Nat) (rows otherRows : List InsertionSupport.Row)
    (hv : rows.map ContextRowValues.rowValues = otherRows.map
      (NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues q)) :
    ((rows.take n).map Prod.fst).map (interpretation 0) =
      ((otherRows.take n).map Prod.fst).map (NativeContext.interpretation q) := by
  have he := congrArg (fun rs : List (Ordinal.{0} × List Ordinal.{0}) => (rs.take n).map Prod.fst) hv
  simpa only [← List.map_take, List.map_map, ContextRowValues.rowValues,
    NativeContext.SourceAdditiveTracking.AssignmentValueSupport.rowValues] using he

theorem insertion_word_values_eq (root : Nat) (rows otherRows : List InsertionSupport.Row)
    (ha : Mu.inputCheck root = true)
    (hrel : List.Forall₂ (RowMatches (alphaCode root)) rows otherRows)
    (hp : ∀ row ∈ stripLast otherRows,
      NativeContext.SourceTrackingRaw.Support.inputCheck (alphaCode root) row.1 = true ∧
        NativeContext.interpretation (alphaCode root) row.1 < Enclosure.sourceAlphaPlus root) :
    (Insertion.word rows).map (interpretation 0) =
      (NativeContext.SourceAdditiveTracking.Insertion.word (alphaCode root) otherRows).map
        (NativeContext.interpretation (alphaCode root)) := by
  have hv := rows_values_eq hrel
  have hc := choose_values_eq root rows otherRows ha hrel hp
  cases hl : Insertion.choose rows with
  | none =>
    cases ht : NativeContext.SourceAdditiveTracking.Insertion.choose (alphaCode root) otherRows with
    | some c => simp only [hl, ht, Option.map_none, Option.map_some, Option.none_ne_some] at hc
    | none => simpa only [Insertion.word,
        NativeContext.SourceAdditiveTracking.Insertion.word, hl, ht] using
        source_default_values_eq (alphaCode root) rows otherRows hv
  | some c =>
    cases ht : NativeContext.SourceAdditiveTracking.Insertion.choose (alphaCode root) otherRows with
    | none => simp only [hl, ht, Option.map_none, Option.map_some, Option.some_ne_none] at hc
    | some d =>
      have he : candidateValues c =
          NativeContext.SourceAdditiveTracking.AssignmentValueSupport.candidateValues (alphaCode root) d := by
        simpa only [hl, ht, Option.map_some, Option.some.injEq] using hc
      have hn := congrArg Prod.fst he
      have hw := congrArg Prod.snd he
      simpa only [Insertion.word, NativeContext.SourceAdditiveTracking.Insertion.word,
        hl, ht, List.map_append, hn, hw] using
        congrArg (fun prefix => prefix ++ d.2.map (NativeContext.interpretation (alphaCode root)))
          (source_take_heads_values_eq (alphaCode root) d.1 rows otherRows hv)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextSelectorSupport
