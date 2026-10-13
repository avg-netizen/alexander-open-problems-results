import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertionSupport

/-!
# Actual greatest insertion position of Definition 3.20.2.2 in original source-one syntax

The concrete replacement table is scanned from the right. A transition
passes exactly when the first value of its actual replacement is covered
by the real original check-zero mu of the preceding written head. Later passing
transitions take priority; if none passes, the first replacement is used.
The output literally retains the original heads before the selected row.
No insertion index, covering relation or replacement word is supplied.
The joint full tracking splice and recursive assignment are separate.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Insertion

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode)

abbrev Candidate := Nat × List Nat

def firstCode (word : List Nat) : Nat := word.head?.getD 0

theorem firstCode_primrec : Primrec firstCode :=
  Primrec.option_getD.comp Primrec.list_head? (Primrec.const 0)

def coverCheck (previous current : Nat) : Bool :=
  SourceTrackingRaw.Support.coverCheck previous current

theorem coverCheck_primrec : Primrec₂ coverCheck := SourceTrackingRaw.Support.coverCheck_primrec

theorem coverCheck_exact (previous current : Nat) : coverCheck previous current = true ↔
    SourceTrackingRaw.Support.inputCheck previous = true ∧ lowCheckCode 0 current = true ∧
      interpretation 0 current ≤ SourceTrackingRaw.Support.muValue previous :=
  SourceTrackingRaw.Support.coverCheck_exact previous current

/-- The returned number counts the original heads before the replacement.
It is positive for every selected transition; zero is only the default. -/
def choose : List Row → Option Candidate
  | [] => none
  | previous :: rest => match rest.head? with
    | none => none
    | some current => match choose rest with
      | some later => some (later.1 + 1, later.2)
      | none => cond (coverCheck previous.1 (firstCode current.2))
          (some (1, current.2)) none

theorem choose_nil : choose [] = none := rfl

theorem choose_singleton (row : Row) : choose [row] = none := rfl

theorem choose_pair (a b : Row) (rest : List Row) :
    choose (a :: b :: rest) = match choose (b :: rest) with
      | some later => some (later.1 + 1, later.2)
      | none => cond (coverCheck a.1 (firstCode b.2)) (some (1, b.2)) none := rfl

theorem choose_primrec : Primrec choose := by
  let A := List Row × (Row × (List Row × Option Candidate))
  have hp : Primrec (fun p : A => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec (fun p : A × Row => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc := coverCheck_primrec.comp (hp.comp Primrec.fst) (firstCode_primrec.comp hw)
  have hd := hc.cond (Primrec.option_some.comp ((Primrec.const 1).pair hw)) (Primrec.const none)
  have hs : Primrec₂ (fun (_ : A × Row) (later : Candidate) =>
      some (later.1 + 1, later.2)) :=
    (Primrec.option_some.comp ((Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))).to₂
  have hcurrent := Primrec.option_casesOn (hr.comp Primrec.fst) hd hs
  have hstep : Primrec₂ (fun (_ : List Row) (s : Row × (List Row × Option Candidate)) =>
      match s.2.1.head? with
      | none => none
      | some current => match s.2.2 with
        | some later => some (later.1 + 1, later.2)
        | none => cond (coverCheck s.1.1 (firstCode current.2)) (some (1, current.2)) none) := by
    exact (Primrec.option_casesOn (Primrec.list_head?.comp ht) (Primrec.const none) hcurrent.to₂).to₂
  have h := Primrec.list_rec Primrec.id (Primrec.const none) hstep
  exact h.of_eq (fun p => by induction p <;> simp [choose, *])

def NoCover : List Row → Prop
  | [] => True
  | previous :: rest => match rest with
    | [] => True
    | current :: later => coverCheck previous.1 (firstCode current.2) = false ∧
        NoCover (current :: later)

theorem choose_none (rows : List Row) : choose rows = none ↔ NoCover rows := by
  induction rows with
  | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
    | cons b later =>
      change choose (a :: b :: later) = none ↔
        coverCheck a.1 (firstCode b.2) = false ∧ NoCover (b :: later)
      cases hs : choose (b :: later) with
      | none =>
        have hn := ih.mp hs
        cases hc : coverCheck a.1 (firstCode b.2) <;>
          simp only [choose_pair, hs, hc, Bool.cond_false, Bool.cond_true,
            Option.some_ne_none, Bool.true_eq_false, true_and, false_and, hn]
      | some c =>
        constructor
        · intro he
          have hf : False := by simpa only [choose_pair, hs, Option.some_ne_none] using he
          exact False.elim hf
        · intro he
          have hn := ih.mpr he.2
          rw [hs] at hn
          cases hn

/-- The chosen original prefix and selected replacement are literal.
Every later transition fails the real checker, proving greatest position. -/
theorem choose_spec (rows : List Row) (n : Nat) (word : List Nat)
    (hs : choose rows = some (n, word)) :
    ∃ before current after, before ≠ [] ∧ rows = before ++ current :: after ∧
      n = before.length ∧ word = current.2 ∧
      coverCheck (lastCode (before.map Prod.fst)) (firstCode word) = true ∧
      NoCover (current :: after) := by
  induction rows generalizing n word with
  | nil => simp only [choose_nil, Option.none_ne_some] at hs
  | cons a rest ih =>
    cases rest with
    | nil => simp only [choose_singleton, Option.none_ne_some] at hs
    | cons b later =>
      cases ht : choose (b :: later) with
      | none =>
        have hc : coverCheck a.1 (firstCode b.2) = true := by
          cases hc : coverCheck a.1 (firstCode b.2) with
          | true => rfl
          | false => simp only [choose_pair, ht, hc, Bool.cond_false, Option.none_ne_some] at hs
        have he : (1, b.2) = (n, word) := by
          simpa only [choose_pair, ht, hc, Bool.cond_true, Option.some.injEq] using hs
        have hn := (Prod.mk.inj he).1
        have hw := (Prod.mk.inj he).2
        refine ⟨[a], b, later, List.cons_ne_nil _ _, rfl, hn.symm, hw.symm, ?_, (choose_none _).mp ht⟩
        simpa only [List.map_cons, List.map_nil, NativeContext.SourceTrackingSequences.lastCode_singleton, hw] using hc
      | some c =>
        have he : (c.1 + 1, c.2) = (n, word) := by
          simpa only [choose_pair, ht, Option.some.injEq] using hs
        obtain ⟨before, current, after, hne, hrows, hlen, hword, hcover, hnone⟩ :=
          ih c.1 c.2 ht
        have hm : before.map Prod.fst ≠ [] := by
          intro he
          exact hne (List.map_eq_nil_iff.mp he)
        refine ⟨a :: before, current, after, List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, hnone⟩
        · rw [hrows]; rfl
        · rw [← (Prod.mk.inj he).1, hlen]; rfl
        · exact (Prod.mk.inj he).2.symm.trans hword
        · rw [List.map_cons, SkTracking.Support.lastCode_cons_nonempty _ _ hm,
            ← (Prod.mk.inj he).2]
          exact hcover

def word (rows : List Row) : List Nat := match choose rows with
  | none => (rows.head?.getD (0, [])).2
  | some c => (rows.take c.1).map Prod.fst ++ c.2

theorem word_primrec : Primrec word := by
  have hd := Primrec.snd.comp (Primrec.option_getD.comp
    Primrec.list_head? (Primrec.const (0, [])))
  have ht := Primrec.list_take.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hm := Primrec.list_map ht (Primrec.fst.comp Primrec.snd).to₂
  have hs := Primrec.list_append.comp hm (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_casesOn choose_primrec hd hs.to₂

theorem word_default (row : Row) (rest : List Row)
    (hs : choose (row :: rest) = none) : word (row :: rest) = row.2 ∧ NoCover (row :: rest) :=
  ⟨by simp only [word, hs, List.head?_cons, Option.getD_some], (choose_none _).mp hs⟩

theorem word_selected (rows : List Row) (n : Nat) (replacement : List Nat)
    (hs : choose rows = some (n, replacement)) :
    ∃ before current after, before ≠ [] ∧ rows = before ++ current :: after ∧
      word rows = before.map Prod.fst ++ current.2 ∧
      coverCheck (lastCode (before.map Prod.fst)) (firstCode current.2) = true ∧
      NoCover (current :: after) := by
  obtain ⟨before, current, after, hne, hrows, hlen, hword, hcover, hnone⟩ :=
    choose_spec rows n replacement hs
  refine ⟨before, current, after, hne, hrows, ?_, ?_, hnone⟩
  · rw [word, hs, hlen, hrows, List.take_left, hword]
  · simpa only [hword] using hcover

abbrev Query := Nat × List Nat

def execute (p : Query) : Part (List Nat) :=
  (InsertionSupport.executeRows p.1 p.2).map word

theorem execute_partrec : Partrec execute :=
  Partrec.map InsertionSupport.executeRows_partrec
    (word_primrec.comp Primrec.snd).to_comp.to₂

theorem execute_returns (factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads)) :
    ∃ out, out ∈ execute (factor, heads) := by
  obtain ⟨rows, hr⟩ := InsertionSupport.executeRows_returns factor heads hh hf hm hb
  exact ⟨word rows, Part.mem_map _ hr⟩

/-- Genuine replacement executions supply every concrete row. The result
is exactly the default first replacement when no later transition passes,
or the literal original prefix and greatest covered replacement otherwise.
The original prefix codes, including raw spellings, are retained. -/
theorem execute_spec (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (ho : out ∈ execute (factor, heads)) :
    ∃ rows, rows ∈ InsertionSupport.executeRows factor heads ∧
      rows.map Prod.fst = heads ∧ out = word rows ∧
      (∀ row ∈ rows, row.2 ≠ [] ∧ ∀ d ∈ row.2,
        Theta.acceptedLowCode 0 d = true) ∧
      ((∃ first rest, rows = first :: rest ∧ out = first.2 ∧ NoCover rows) ∨
        ∃ before current after, before ≠ [] ∧ rows = before ++ current :: after ∧
          out = before.map Prod.fst ++ current.2 ∧
          interpretation 0 (firstCode current.2) ≤
            SourceTrackingRaw.Support.muValue (lastCode (before.map Prod.fst)) ∧
          NoCover (current :: after)) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hrows : ∀ row ∈ rows, row.2 ≠ [] ∧ ∀ d ∈ row.2,
      Theta.acceptedLowCode 0 d = true := by
    intro row hrow
    have hs := InsertionSupport.relation_members factor hrel row hrow
    have ht := ConditionalReplacement.execute_spec heads hh row.1 factor hs.1 hf hm hb row.2 hs.2
    exact ⟨ht.1, ht.2.1⟩
  refine ⟨rows, hr, hheads, hout.symm, hrows, ?_⟩
  cases hs : choose rows with
  | none =>
    cases rows with
    | nil =>
      have hn : heads ≠ [] := ((SourceTrackingRaw.trackingCheck_exact heads).mp hh).1
      exact False.elim (hn (by simpa only [List.map_nil] using hheads.symm))
    | cons first rest =>
      have hd := word_default first rest hs
      exact Or.inl ⟨first, rest, rfl, hout.symm.trans hd.1, hd.2⟩
  | some c =>
    obtain ⟨before, current, after, hne, hrows, hword, hcover, hnone⟩ :=
      word_selected rows c.1 c.2 hs
    exact Or.inr ⟨before, current, after, hne, hrows, hout.symm.trans hword,
      ((coverCheck_exact _ _).mp hcover).2.2, hnone⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Insertion
