import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingPrefix

/-!
# Actual finite covered table in the original source-one dictionary

Every finite record retains its original source-zero code and already
constructed word. Reverse chronological first-passing selection uses the
genuine raw source-one mu cover checker. All literal finite operations are
primitive recursive. No Native base-one parser, assigned word, cover or
tracking soundness is supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Support

open SourceTrackingRaw.Support (coverCheck coverCheck_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton lastCode_append_singleton)

abbrev Entry := Nat × List Nat

def select (current : Nat) : List Entry → Option Entry
  | [] => none
  | e :: es => cond (coverCheck e.1 current) (some e) (select current es)

theorem select_primrec : Primrec₂ select := by
  have hstep : Primrec₂ (fun (p : Nat × List Entry) (s : Entry × Option Entry) =>
      cond (coverCheck s.1.1 p.1) (some s.1) s.2) := by
    have hc := Primrec.fst.comp Primrec.fst
    have he := Primrec.fst.comp Primrec.snd
    have hr := Primrec.snd.comp Primrec.snd
    have htest := coverCheck_primrec.comp (Primrec.fst.comp he) hc
    exact (Primrec.cond htest (Primrec.option_some.comp he) hr).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const none) hstep
  have hh : (fun p : Nat × List Entry =>
      p.2.foldr (fun e tail => cond (coverCheck e.1 p.1) (some e) tail) none) =
      fun p => select p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, select, ih]
  rw [hh] at h
  exact h.to₂

theorem select_mem (current : Nat) (es : List Entry) (e : Entry)
    (hs : select current es = some e) : e ∈ es := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : coverCheck a.1 current with
    | false =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [select, hc, Bool.cond_false] using hs))
    | true =>
      have he : a = e := by simpa only [select, hc, Bool.cond_true, Option.some.injEq] using hs
      rw [← he]
      exact List.mem_cons_self

theorem select_cover (current : Nat) (es : List Entry) (e : Entry)
    (hs : select current es = some e) : coverCheck e.1 current = true := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : coverCheck a.1 current with
    | false => exact ih (by simpa only [select, hc, Bool.cond_false] using hs)
    | true =>
      have he : a = e := by simpa only [select, hc, Bool.cond_true, Option.some.injEq] using hs
      simpa only [he] using hc

theorem select_none (current : Nat) (es : List Entry) :
    select current es = none ↔ ∀ e ∈ es, coverCheck e.1 current = false := by
  induction es with
  | nil => simp only [select, List.not_mem_nil, false_implies, implies_true]
  | cons a es ih =>
    cases hc : coverCheck a.1 current with
    | false => simp only [select, hc, Bool.cond_false, ih, List.forall_mem_cons, and_true, true_and]
    | true => simp only [select, hc, Bool.cond_true, Option.some_ne_none,
        List.forall_mem_cons, Bool.true_eq_false, false_and]

theorem select_first (current : Nat) (es : List Entry) (e : Entry)
    (hs : select current es = some e) :
    ∃ before after : List Entry, es = before ++ e :: after ∧
      (∀ a ∈ before, coverCheck a.1 current = false) ∧ coverCheck e.1 current = true := by
  induction es with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons a es ih =>
    cases hc : coverCheck a.1 current with
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

def extend (current : Nat) (es : List Entry) : List Nat :=
  match select current es with
  | none => [current]
  | some e => e.2 ++ [current]

theorem extend_primrec : Primrec₂ extend := by
  have hunit := Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  have hsome := Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
    (hunit.comp Primrec.fst)
  exact (Primrec.option_casesOn select_primrec hunit hsome.to₂).to₂

def step (current : Nat) (es : List Entry) : List Entry := (current, extend current es) :: es

theorem step_primrec : Primrec₂ step :=
  (Primrec.list_cons.comp (Primrec.fst.pair extend_primrec) Primrec.snd).to₂

def buildRev : List Nat → List Entry
  | [] => []
  | current :: rest => step current (buildRev rest)

theorem buildRev_primrec : Primrec buildRev := by
  have hs : Primrec₂ (fun (_xs : List Nat) (s : Nat × List Entry) => step s.1 s.2) :=
    (Primrec.comp step_primrec Primrec.snd).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const []) hs
  have he : (fun xs : List Nat => xs.foldr (fun c es => step c es) []) = buildRev := by
    funext xs
    induction xs with
    | nil => rfl
    | cons c cs ih => simp only [List.foldr_cons, buildRev, ih]
  rw [he] at h
  exact h

theorem buildRev_codes (xs : List Nat) : (buildRev xs).map Prod.fst = xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp only [buildRev, step, List.map_cons, ih]

theorem extend_ne_nil (current : Nat) (es : List Entry) : extend current es ≠ [] := by
  cases hs : select current es <;>
    simp only [extend, hs, List.cons_ne_nil, List.append_eq_nil_iff, and_false, not_false_eq_true]

theorem extend_last (current : Nat) (es : List Entry) : lastCode (extend current es) = current := by
  cases hs : select current es with
  | none => simp only [extend, hs, lastCode_singleton]
  | some e => simp only [extend, hs, lastCode_append_singleton]

theorem buildRev_last (xs : List Nat) :
    ∀ e ∈ buildRev xs, e.2 ≠ [] ∧ lastCode e.2 = e.1 := by
  induction xs with
  | nil => intro e hm; exact False.elim (List.not_mem_nil hm)
  | cons c cs ih =>
    intro e hm
    rcases List.mem_cons.mp hm with he | hm
    · subst e
      exact ⟨extend_ne_nil c _, extend_last c _⟩
    · exact ih e hm

theorem buildRev_word_mem (xs : List Nat) :
    ∀ e ∈ buildRev xs, ∀ c ∈ e.2, c ∈ xs := by
  induction xs with
  | nil => intro e hm; exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    intro e he c hc
    rcases List.mem_cons.mp he with he | he
    · subst e
      change c ∈ extend current (buildRev rest) at hc
      cases hs : select current (buildRev rest) with
      | none =>
        have hce : c = current := by simpa only [extend, hs, List.mem_singleton] using hc
        rw [hce]
        exact List.mem_cons_self
      | some a =>
        have ha := select_mem current (buildRev rest) a hs
        have hm : c ∈ a.2 ++ [current] := by simpa only [extend, hs] using hc
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_cons_of_mem _ (ih a ha c hm)
        · rw [List.mem_singleton.mp hm]
          exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih e he c hc)

theorem buildRev_code_mem (xs : List Nat) (e : Entry) (he : e ∈ buildRev xs) : e.1 ∈ xs := by
  rw [← buildRev_codes xs]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

def table (xs : List Nat) : List Entry := buildRev xs.reverse

theorem table_primrec : Primrec table := buildRev_primrec.comp Primrec.list_reverse

theorem table_codes (xs : List Nat) : (table xs).map Prod.fst = xs.reverse := buildRev_codes xs.reverse

theorem table_append (current : Nat) (xs : List Nat) :
    table (xs ++ [current]) = (current, extend current (table xs)) :: table xs := by
  simp only [table, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, buildRev, step]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Support
