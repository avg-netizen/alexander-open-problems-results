import Alexander313.Wilken.PublicEpsilonNativeLocalizationProperties
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequences

/-!
# Actual finite greatest-covered selection for multiplicative tracking

The original localization tail is processed in its written order. Each
entry records its already constructed tracking word; the newest records
come first. The actual mu-cover checker selects the first passing record,
therefore the greatest covered localization index. All operations use
the real original code dictionary and actual mu producer. No supplied
tracking assignment, covering relation or evaluation is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Support

open SourceTrackingSequences SourceTrackingSequences.Support

abbrev Entry := Nat × List Nat

def select (q current : Nat) : List Entry → Option Entry
  | [] => none
  | e :: es => cond (coverCheck q e.1 current) (some e) (select q current es)

theorem select_primrec : Primrec
    (fun p : (Nat × Nat) × List Entry => select p.1.1 p.1.2 p.2) := by
  have hstep : Primrec₂ (fun (p : (Nat × Nat) × List Entry) (s : Entry × Option Entry) =>
      cond (coverCheck p.1.1 s.1.1 p.1.2) (some s.1) s.2) := by
    have hq := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hc := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have he := Primrec.fst.comp Primrec.snd
    have hr := Primrec.snd.comp Primrec.snd
    have htest := coverCheck_primrec.comp ((hq.pair (Primrec.fst.comp he)).pair hc)
    exact (Primrec.cond htest (Primrec.option_some.comp he) hr).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const none) hstep
  have hh : (fun p : (Nat × Nat) × List Entry =>
      p.2.foldr (fun e tail => cond (coverCheck p.1.1 e.1 p.1.2) (some e) tail) none) =
      fun p => select p.1.1 p.1.2 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, select, ih]
  rw [hh] at h
  exact h

theorem select_mem (q current : Nat) (es : List Entry) (e : Entry)
    (hs : select q current es = some e) : e ∈ es := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : coverCheck q a.1 current with
    | false =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [select, hc, Bool.cond_false] using hs))
    | true =>
      have he : a = e := by simpa only [select, hc, Bool.cond_true, Option.some.injEq] using hs
      rw [← he]
      exact List.mem_cons_self

theorem select_cover (q current : Nat) (es : List Entry) (e : Entry)
    (hs : select q current es = some e) : coverCheck q e.1 current = true := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : coverCheck q a.1 current with
    | false => exact ih (by simpa only [select, hc, Bool.cond_false] using hs)
    | true =>
      have he : a = e := by simpa only [select, hc, Bool.cond_true, Option.some.injEq] using hs
      simpa only [he] using hc

theorem select_none (q current : Nat) (es : List Entry) :
    select q current es = none ↔ ∀ e ∈ es, coverCheck q e.1 current = false := by
  induction es with
  | nil => simp only [select, List.not_mem_nil, false_implies, implies_true]
  | cons a es ih =>
    cases hc : coverCheck q a.1 current with
    | false => simp only [select, hc, Bool.cond_false, ih, List.forall_mem_cons, and_true, true_and]
    | true => simp only [select, hc, Bool.cond_true, Option.some_ne_none,
        List.forall_mem_cons, Bool.true_eq_false, false_and]

/-- Literal first passing record, with all more recent records excluded. -/
theorem select_first (q current : Nat) (es : List Entry) (e : Entry)
    (hs : select q current es = some e) :
    ∃ before after : List Entry, es = before ++ e :: after ∧
      (∀ a ∈ before, coverCheck q a.1 current = false) ∧ coverCheck q e.1 current = true := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : coverCheck q a.1 current with
    | true =>
      have he : a = e := by simpa only [select, hc, Bool.cond_true, Option.some.injEq] using hs
      subst a
      exact ⟨[], es, rfl, by simp, hc⟩
    | false =>
      obtain ⟨before, after, he, hb, ht⟩ := ih
        (by simpa only [select, hc, Bool.cond_false] using hs)
      refine ⟨a :: before, after, ?_, ?_, ht⟩
      · simp only [List.cons_append, he]
      · intro b hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hc
        · exact hb b hm

def extend (q current : Nat) (es : List Entry) : List Nat :=
  match select q current es with
  | none => [current]
  | some e => e.2 ++ [current]

theorem extend_primrec : Primrec
    (fun p : (Nat × Nat) × List Entry => extend p.1.1 p.1.2 p.2) := by
  have hc := Primrec.snd.comp Primrec.fst
  have hunit := Primrec.list_cons.comp hc (Primrec.const [])
  have hsome := Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
    (hunit.comp Primrec.fst)
  exact Primrec.option_casesOn select_primrec hunit hsome.to₂

def step (q current : Nat) (es : List Entry) : List Entry := (current, extend q current es) :: es

theorem step_primrec : Primrec
    (fun p : (Nat × Nat) × List Entry => step p.1.1 p.1.2 p.2) :=
  Primrec.list_cons.comp ((Primrec.snd.comp Primrec.fst).pair extend_primrec) Primrec.snd

def buildRev (q : Nat) : List Nat → List Entry
  | [] => []
  | current :: rest => step q current (buildRev q rest)

theorem buildRev_primrec : Primrec₂ buildRev := by
  have hs : Primrec₂ (fun (p : Nat × List Nat) (s : Nat × List Entry) => step p.1 s.1 s.2) :=
    (step_primrec.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  have he : (fun p : Nat × List Nat => p.2.foldr (fun c es => step p.1 c es) []) =
      fun p => buildRev p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons c cs ih => simp only [List.foldr_cons, buildRev, ih]
  rw [he] at h
  exact h.to₂

theorem buildRev_codes (q : Nat) (xs : List Nat) : (buildRev q xs).map Prod.fst = xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp only [buildRev, step, List.map_cons, ih]

theorem extend_ne_nil (q current : Nat) (es : List Entry) : extend q current es ≠ [] := by
  cases hs : select q current es <;>
    simp only [extend, hs, List.cons_ne_nil, List.append_eq_nil_iff, and_false, not_false_eq_true]

theorem extend_last (q current : Nat) (es : List Entry) : lastCode (extend q current es) = current := by
  cases hs : select q current es with
  | none => simp only [extend, hs, lastCode_singleton]
  | some e => simp only [extend, hs, lastCode_append_singleton]

theorem buildRev_last (q : Nat) (xs : List Nat) :
    ∀ e ∈ buildRev q xs, e.2 ≠ [] ∧ lastCode e.2 = e.1 := by
  induction xs with
  | nil => intro e hm; exact False.elim (List.not_mem_nil hm)
  | cons c cs ih =>
    intro e hm
    rcases List.mem_cons.mp hm with he | hm
    · subst e
      exact ⟨extend_ne_nil q c _, extend_last q c _⟩
    · exact ih e hm

theorem buildRev_word_mem (q : Nat) (xs : List Nat) :
    ∀ e ∈ buildRev q xs, ∀ c ∈ e.2, c ∈ xs := by
  induction xs with
  | nil => intro e hm; exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    intro e he c hc
    rcases List.mem_cons.mp he with he | he
    · subst e
      change c ∈ extend q current (buildRev q rest) at hc
      cases hs : select q current (buildRev q rest) with
      | none =>
        have hce : c = current := by simpa only [extend, hs, List.mem_singleton] using hc
        rw [hce]
        exact List.mem_cons_self
      | some a =>
        have ha := select_mem q current (buildRev q rest) a hs
        have hm : c ∈ a.2 ++ [current] := by simpa only [extend, hs] using hc
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_cons_of_mem _ (ih a ha c hm)
        · rw [List.mem_singleton.mp hm]
          exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih e he c hc)

theorem buildRev_code_mem (q : Nat) (xs : List Nat) (e : Entry)
    (he : e ∈ buildRev q xs) : e.1 ∈ xs := by
  rw [← buildRev_codes q xs]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

def table (q : Nat) (xs : List Nat) : List Entry := buildRev q xs.reverse

theorem table_primrec : Primrec₂ table :=
  (buildRev_primrec.comp Primrec.fst (Primrec.list_reverse.comp Primrec.snd)).to₂

theorem table_codes (q : Nat) (xs : List Nat) : (table q xs).map Prod.fst = xs.reverse :=
  buildRev_codes q xs.reverse

theorem table_append (q current : Nat) (xs : List Nat) :
    table q (xs ++ [current]) = (current, extend q current (table q xs)) :: table q xs := by
  simp only [table, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, buildRev, step]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Support
