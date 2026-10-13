import Alexander313.Wilken.HereditaryPublicTrackingSequences

/-!
# Concrete least-cover recursion over a chronological localization table

Each new row chooses the FIRST genuine independently computed public-mu
cover among the earlier chronological rows, and appends its target to
that row's already computed word. With no eligible predecessor it returns
the original root singleton. This is the finite executing recursion of
Definition3.28. The supplied-list mathematics is deliberately separate:
this module does not assert that an arbitrary list is a localization, or
that the resulting word is a covering. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Support

open PublicTrackingSequences (adjacencyCheck adjacencyCheck_primrec coverCheck_exact)

abbrev Entry := Nat × List Nat

/-- Chronological order makes this the least passing predecessor. -/
def select (target : Nat) : List Entry → Option Entry
  | [] => none
  | e :: es => cond (adjacencyCheck e.1 target) (some e) (select target es)

theorem select_primrec : Primrec₂ select := by
  have hstep : Primrec₂ (fun p : Nat × List Entry => fun s : Entry × Option Entry =>
      cond (adjacencyCheck s.1.1 p.1) (some s.1) s.2) := by
    have ht := Primrec.fst.comp Primrec.fst
    have he := Primrec.fst.comp Primrec.snd
    have htest := adjacencyCheck_primrec.comp (Primrec.fst.comp he) ht
    exact (htest.cond (Primrec.option_some.comp he) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const none) hstep
  have he : (fun p : Nat × List Entry => p.2.foldr
      (fun e tail => cond (adjacencyCheck e.1 p.1) (some e) tail) none) =
      fun p => select p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, select, ih]
  rw [he] at h
  exact h.to₂

theorem select_mem (target : Nat) (es : List Entry) (e : Entry)
    (hs : select target es = some e) : e ∈ es := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : adjacencyCheck a.1 target with
    | false => exact List.mem_cons_of_mem _
        (ih (by simpa only [select, hc, Bool.cond_false] using hs))
    | true =>
      have he : a = e := by simpa only
        [select, hc, Bool.cond_true, Option.some.injEq] using hs
      rw [← he]
      exact List.mem_cons_self

theorem select_first (target : Nat) (es : List Entry) (e : Entry)
    (hs : select target es = some e) :
    ∃ before after : List Entry, es = before ++ e :: after ∧
      (∀ a ∈ before, adjacencyCheck a.1 target = false) ∧
        adjacencyCheck e.1 target = true := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : adjacencyCheck a.1 target with
    | true =>
      have he : a = e := by simpa only
        [select, hc, Bool.cond_true, Option.some.injEq] using hs
      subst e
      exact ⟨[], es, rfl, fun d hd => False.elim (List.not_mem_nil hd), hc⟩
    | false =>
      obtain ⟨before, after, he, hn, hp⟩ := ih
        (by simpa only [select, hc, Bool.cond_false] using hs)
      refine ⟨a :: before, after, ?_, ?_, hp⟩
      · simp only [he, List.cons_append]
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hc
        · exact hn d hd

theorem select_none (target : Nat) (es : List Entry) :
    select target es = none ↔ ∀ e ∈ es, adjacencyCheck e.1 target = false := by
  induction es with
  | nil => simp only [select, List.not_mem_nil, false_implies, implies_true]
  | cons e es ih =>
    cases hc : adjacencyCheck e.1 target <;>
      simp only [select, hc, Bool.cond_true, Bool.cond_false, Option.some_ne_none,
        List.forall_mem_cons, ih, Bool.true_eq_false, false_and, and_true, true_and]

/-- Passing is a true strict comparison and the independent proper-mu
cover; the stored word is not an admission premise for this test. -/
theorem eligible_exact (a target : Nat) : adjacencyCheck a target = true ↔
    MuPublicDictionary.Support.inputCheck a = true ∧ Canonical.check target = true ∧
      unionInterpretation a < unionInterpretation target ∧
        unionInterpretation target ≤ SkPublicRecurrence.muValue a := by
  rw [PublicTrackingSequences.adjacencyCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hlt, hc⟩
    have hs := (coverCheck_exact a target).mp hc
    exact ⟨hs.1, hs.2.1, ((Canonical.less_exact a target).mp hlt).2.2, hs.2.2⟩
  · rintro ⟨ha, ht, hlt, hc⟩
    exact ⟨(Canonical.less_exact a target).mpr
      ⟨((MuPublicDictionary.Support.inputCheck_image a).mp ha).1, ht, hlt⟩,
      (coverCheck_exact a target).mpr ⟨ha, ht, hc⟩⟩

def extend (root target : Nat) (es : List Entry) : List Nat :=
  match select target es with
  | none => [root]
  | some e => e.2 ++ [target]

theorem extend_primrec : Primrec₂ (fun p : Nat × Nat => extend p.1 p.2) := by
  have hr := Primrec.fst.comp Primrec.fst
  have ht := Primrec.snd.comp Primrec.fst
  have hs := select_primrec.comp ht Primrec.snd
  have hsome : Primrec₂ (fun p : (Nat × Nat) × List Entry => fun e : Entry =>
      e.2 ++ [p.1.2]) :=
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (ht.comp Primrec.fst) (Primrec.const []))).to₂
  exact (Primrec.option_casesOn hs
    (Primrec.list_cons.comp hr (Primrec.const [])) hsome).to₂

theorem extend_none (root target : Nat) (es : List Entry)
    (hs : select target es = none) : extend root target es = [root] := by
  simp only [extend, hs]

theorem extend_some (root target : Nat) (es : List Entry) (e : Entry)
    (hs : select target es = some e) : extend root target es = e.2 ++ [target] := by
  simp only [extend, hs]

theorem extend_least (root target : Nat) (es : List Entry) (e : Entry)
    (hs : select target es = some e) :
    ∃ before after : List Entry, es = before ++ e :: after ∧
      (∀ a ∈ before, adjacencyCheck a.1 target = false) ∧
      adjacencyCheck e.1 target = true ∧ extend root target es = e.2 ++ [target] := by
  obtain ⟨before, after, he, hn, hp⟩ := select_first target es e hs
  exact ⟨before, after, he, hn, hp, extend_some root target es e hs⟩

def update (root current : Nat) (es : List Entry) : List Entry :=
  es ++ [(current, extend root current es)]

theorem update_primrec : Primrec₂ (fun p : Nat × Nat => update p.1 p.2) := by
  have hw := extend_primrec.comp Primrec.fst Primrec.snd
  exact (Primrec.list_append.comp Primrec.snd
    (Primrec.list_cons.comp ((Primrec.snd.comp Primrec.fst).pair hw)
      (Primrec.const []))).to₂

def table (root : Nat) (xs : List Nat) : List Entry :=
  xs.foldl (fun es current => update root current es) [(root, [root])]

theorem table_primrec : Primrec₂ table := by
  have hroot := Primrec.fst
  have hinitial := Primrec.list_cons.comp
    (hroot.pair (Primrec.list_cons.comp hroot (Primrec.const []))) (Primrec.const [])
  have hstep : Primrec₂ (fun p : Nat × List Nat => fun s : List Entry × Nat =>
      update p.1 s.2 s.1) :=
    (update_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)).to₂
  exact (Primrec.list_foldl Primrec.snd hinitial hstep).to₂

theorem table_nil (root : Nat) : table root [] = [(root, [root])] := rfl

theorem table_append (root : Nat) (xs ys : List Nat) :
    table root (xs ++ ys) = ys.foldl (fun es current => update root current es) (table root xs) := by
  simp only [table, List.foldl_append]

theorem table_append_singleton (root current : Nat) (xs : List Nat) :
    table root (xs ++ [current]) =
      table root xs ++ [(current, extend root current (table root xs))] := by
  simp only [table_append, List.foldl_cons, List.foldl_nil, update]

private theorem fold_codes (root : Nat) (xs : List Nat) (es : List Entry) :
    (xs.foldl (fun rows current => update root current rows) es).map Prod.fst =
      es.map Prod.fst ++ xs := by
  induction xs generalizing es with
  | nil => simp only [List.foldl_nil, List.append_nil]
  | cons current xs ih =>
    rw [List.foldl_cons, ih]
    simp only [update, List.map_append, List.map_singleton, List.append_assoc,
      List.singleton_append]

theorem table_codes (root : Nat) (xs : List Nat) :
    (table root xs).map Prod.fst = root :: xs := by
  simpa only [table, List.map_singleton, List.singleton_append] using
    fold_codes root xs [(root, [root])]

/-- The literal chronological table contains precisely the root row and
one row for every actual written localization entry, with no hidden search. -/
theorem table_length (root : Nat) (xs : List Nat) : (table root xs).length = xs.length + 1 := by
  have he := congrArg List.length (table_codes root xs)
  simp only [List.length_map, List.length_cons] at he
  omega

/-- Every stored row is generated from the literal earlier chronological
table. This independent relation specifies the actual finite recursion. -/
inductive Rows (root : Nat) : List Nat → List Entry → Prop
  | initial : Rows root [] [(root, [root])]
  | append (inputs : List Nat) (es : List Entry) (current : Nat)
      (hr : Rows root inputs es) :
      Rows root (inputs ++ [current])
        (es ++ [(current, extend root current es)])

private theorem fold_rows (root : Nat) (xs : List Nat) (inputs : List Nat)
    (es : List Entry) (hr : Rows root inputs es) :
    Rows root (inputs ++ xs)
      (xs.foldl (fun rows current => update root current rows) es) := by
  induction xs generalizing inputs es with
  | nil => simpa only [List.append_nil, List.foldl_nil] using hr
  | cons current xs ih =>
    have hn : Rows root (inputs ++ [current]) (update root current es) :=
      Rows.append inputs es current hr
    simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using
      ih (inputs ++ [current]) (update root current es) hn

theorem table_rows (root : Nat) (xs : List Nat) : Rows root xs (table root xs) := by
  simpa only [table, List.nil_append] using
    fold_rows root xs [] [(root, [root])] Rows.initial

theorem Rows.table_eq {root : Nat} {inputs : List Nat} {es : List Entry}
    (hr : Rows root inputs es) : es = table root inputs := by
  induction hr with
  | initial => rfl
  | append inputs es current hr ih =>
    rw [table_append_singleton, ← ih]

def word (root : Nat) (xs : List Nat) : List Nat :=
  (((table root xs).reverse.head?).getD (root, [root])).2

theorem word_primrec : Primrec₂ word := by
  have hr := Primrec.fst
  have hdefault := hr.pair (Primrec.list_cons.comp hr (Primrec.const []))
  have htable := table_primrec.comp Primrec.fst Primrec.snd
  have hhead := Primrec.list_head?.comp (Primrec.list_reverse.comp htable)
  exact (Primrec.snd.comp (Primrec.option_getD.comp hhead hdefault)).to₂

theorem word_nil (root : Nat) : word root [] = [root] := rfl

/-- The final stored row is exactly the executing least-predecessor
recursion at that input's literal earlier table. -/
theorem word_append (root current : Nat) (xs : List Nat) :
    word root (xs ++ [current]) = extend root current (table root xs) := by
  rw [word, table_append_singleton]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.head?_cons, Option.getD_some]

theorem word_least (root current : Nat) (xs : List Nat) (e : Entry)
    (hs : select current (table root xs) = some e) :
    ∃ before after : List Entry, table root xs = before ++ e :: after ∧
      (∀ a ∈ before, adjacencyCheck a.1 current = false) ∧
      adjacencyCheck e.1 current = true ∧ word root (xs ++ [current]) = e.2 ++ [current] := by
  rw [word_append]
  exact extend_least root current (table root xs) e hs

theorem word_no_predecessor (root current : Nat) (xs : List Nat)
    (hn : ∀ e ∈ table root xs, adjacencyCheck e.1 current = false) :
    word root (xs ++ [current]) = [root] := by
  rw [word_append]
  exact extend_none root current _ ((select_none current _).mpr hn)

/-- Each actual stored word is the independent execution on its literal
earlier input prefix, including the original root row. -/
theorem Rows.entry_word {root : Nat} {xs : List Nat} {es : List Entry}
    (hr : Rows root xs es) (e : Entry) (hm : e ∈ es) :
    e = (root, [root]) ∨ ∃ before after : List Nat,
      xs = before ++ e.1 :: after ∧ e.2 = word root (before ++ [e.1]) := by
  induction hr generalizing e with
  | initial => exact Or.inl (List.mem_singleton.mp hm)
  | append inputs es current hr ih =>
    rcases List.mem_append.mp hm with hm | hm
    · rcases ih e hm with he | ⟨before, after, he, hw⟩
      · exact Or.inl he
      · refine Or.inr ⟨before, after ++ [current], ?_, hw⟩
        simp only [he, List.append_assoc, List.cons_append]
    · have he : e = (current, extend root current es) := List.mem_singleton.mp hm
      subst e
      refine Or.inr ⟨inputs, [], ?_, ?_⟩
      · rfl
      · rw [word_append, ← hr.table_eq]

theorem table_entry_word (root : Nat) (xs : List Nat) (e : Entry)
    (hm : e ∈ table root xs) :
    e = (root, [root]) ∨ ∃ before after : List Nat,
      xs = before ++ e.1 :: after ∧ e.2 = word root (before ++ [e.1]) :=
  (table_rows root xs).entry_word e hm

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.Support
