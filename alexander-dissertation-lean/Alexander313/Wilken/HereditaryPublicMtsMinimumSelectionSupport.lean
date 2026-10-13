import Alexander313.Wilken.HereditaryPublicMtsMinimum
import Mathlib.Data.List.Sublists

/-!
# Finite independent covering selection in genuine localization

Every subsequence is enumerated by a literal finite fold. The primitive
recursive predicate checks the independently defined covering and a real
numerical length. At fixed length this enumeration runs from greatest to
least lexical value word, because the actual localization is strictly
increasing. Selecting its first passing candidate therefore derives lexical
maximality among coverings of that length. No lexical or covering oracle is
an input. Equality of this independent selector with mts is separate.
Source-only uncompiled draft.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.MinimumSelectionSupport

open CoveringSupport (Covering)

abbrev Query := (Nat × Nat) × Nat

def enumerate : List Nat → List (List Nat)
  | [] => [[]]
  | a :: xs => enumerate xs ++ (enumerate xs).map (List.cons a)

theorem enumerate_primrec : Primrec enumerate := by
  have hmap : Primrec₂ (fun a : Nat => fun xs : List (List Nat) => xs.map (List.cons a)) := by
    have hs : Primrec₂ (fun p : Nat × List (List Nat) => fun xs : List Nat => p.1 :: xs) :=
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    exact (Primrec.list_map Primrec.snd hs).to₂
  have hstep : Primrec₂ (fun p : List Nat => fun s : Nat × List (List Nat) =>
      s.2 ++ s.2.map (List.cons s.1)) :=
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (hmap.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂
  have hf := Primrec.list_foldr Primrec.id (Primrec.const [[]]) hstep
  have he : (fun xs : List Nat => xs.foldr
      (fun a tail => tail ++ tail.map (List.cons a)) [[]]) = enumerate := by
    funext xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.foldr_cons, enumerate, ih]
  rw [he] at hf
  exact hf

theorem enumerate_eq (xs : List Nat) : enumerate xs = xs.sublists' := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [enumerate, ih, List.sublists'_cons]

theorem enumerate_mem (xs candidate : List Nat) : candidate ∈ enumerate xs ↔ candidate.Sublist xs := by
  rw [enumerate_eq, List.mem_sublists']

def passes (p : Query) (candidate : List Nat) : Bool :=
  CoveringRecognition.coveringCheck p.1.1 p.1.2 candidate && (candidate.length == p.2)

theorem passes_primrec : Primrec₂ passes := by
  have hg := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hb := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk := Primrec.snd.comp Primrec.fst
  have hc := CoveringRecognition.coveringCheck_primrec.comp (hg.pair (hb.pair Primrec.snd))
  exact (Primrec.and.comp hc
    (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd) hk)).to₂

theorem passes_exact (p : Query) (candidate : List Nat) : passes p candidate = true ↔
    Covering p.1.1 p.1.2 candidate ∧ candidate.length = p.2 := by
  rw [passes, Bool.and_eq_true, CoveringRecognition.coveringCheck_exact, beq_iff_eq]

def select (p : Query) : List (List Nat) → Option (List Nat)
  | [] => none
  | candidate :: candidates => cond (passes p candidate) (some candidate) (select p candidates)

theorem select_primrec : Primrec₂ select := by
  have hstep : Primrec₂ (fun p : Query × List (List Nat) =>
      fun s : List Nat × Option (List Nat) =>
      cond (passes p.1 s.1) (some s.1) s.2) := by
    have ht := passes_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    exact (ht.cond (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hf := Primrec.list_foldr Primrec.snd (Primrec.const none) hstep
  have he : (fun p : Query × List (List Nat) => p.2.foldr
      (fun candidate tail => cond (passes p.1 candidate) (some candidate) tail) none) =
      fun p => select p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons candidate candidates ih => simp only [List.foldr_cons, select, ih]
  rw [he] at hf
  exact hf.to₂

theorem select_first (p : Query) (candidates : List (List Nat)) (selected : List Nat)
    (hs : select p candidates = some selected) :
    passes p selected = true ∧ ∃ before after,
      candidates = before ++ selected :: after ∧ ∀ c ∈ before, passes p c = false := by
  induction candidates with
  | nil => simp only [select, Option.none_ne_some] at hs
  | cons candidate candidates ih =>
    cases hc : passes p candidate with
    | true =>
      have he : candidate = selected := by
        simpa only [select, hc, Bool.cond_true, Option.some.injEq] using hs
      subst selected
      exact ⟨hc, [], candidates, rfl, fun c hm => False.elim (List.not_mem_nil hm)⟩
    | false =>
      obtain ⟨hp, before, after, he, hn⟩ := ih
        (by simpa only [select, hc, Bool.cond_false] using hs)
      refine ⟨hp, candidate :: before, after, by simp only [he, List.cons_append], ?_⟩
      intro c hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hc
      · exact hn c hm

theorem select_none (p : Query) (candidates : List (List Nat)) :
    select p candidates = none ↔ ∀ c ∈ candidates, passes p c = false := by
  induction candidates with
  | nil => simp only [select, List.not_mem_nil, false_implies, implies_true]
  | cons c cs ih =>
    cases hc : passes p c <;>
      simp only [select, hc, Bool.cond_true, Bool.cond_false, Option.some_ne_none,
        List.forall_mem_cons, ih, Bool.true_eq_false, false_and, and_true, true_and]

theorem select_exists (p : Query) (candidates : List (List Nat))
    (hw : ∃ c ∈ candidates, passes p c = true) : ∃ selected, select p candidates = some selected := by
  cases hs : select p candidates with
  | some selected => exact ⟨selected, hs⟩
  | none =>
    obtain ⟨c, hm, hp⟩ := hw
    have hf := (select_none p candidates).mp hs c hm
    exact False.elim (Bool.true_ne_false (hp.symm.trans hf))

/-- On equal-length words, reversing every strict constituent comparison
reverses the genuine lexicographic comparison; prefix cases are impossible. -/
theorem reverse_lex_of_equal_length {xs ys : List Ordinal.{0}}
    (hl : xs.length = ys.length) (hx : List.Lex (fun a b => b < a) xs ys) :
    List.Lex (· < ·) ys xs := by
  revert hl
  induction hx with
  | nil => intro hl; simp only [List.length_nil, List.length_cons] at hl; omega
  | rel hr => intro hl; exact List.Lex.rel hr
  | cons hx ih =>
    intro hl
    exact List.Lex.cons (ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hl))

/-- All enumerated equal-length subwords occur in descending genuine
lexical value order. Strictness comes from the actual localization. -/
theorem enumerate_order (xs : List Nat)
    (ht : (xs.map unionInterpretation).Pairwise (· < ·)) :
    (enumerate xs).Pairwise (fun as bs =>
      List.Lex (fun a b => b < a) (as.map unionInterpretation) (bs.map unionInterpretation)) := by
  have hs := ht.sublists'
  rw [List.sublists'_map, ← enumerate_eq xs] at hs
  exact List.pairwise_map.mp hs

theorem select_lex_maximal (p : Query) (xs selected candidate : List Nat)
    (ht : (xs.map unionInterpretation).Pairwise (· < ·))
    (hs : select p (enumerate xs) = some selected)
    (hc : candidate.Sublist xs) (hp : passes p candidate = true) :
    candidate.map unionInterpretation = selected.map unionInterpretation ∨
      List.Lex (· < ·) (candidate.map unionInterpretation) (selected.map unionInterpretation) := by
  obtain ⟨hselected, before, after, he, hfailed⟩ := select_first p _ _ hs
  have hm := (enumerate_mem xs candidate).mpr hc
  rw [he] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact False.elim (Bool.true_ne_false (hp.symm.trans (hfailed candidate hm)))
  · rcases List.mem_cons.mp hm with hsame | hm
    · exact Or.inl (congrArg (List.map unionInterpretation) hsame)
    · have horder := enumerate_order xs ht
      rw [he] at horder
      have htail := (List.pairwise_append.mp horder).2.1
      have hlex := (List.pairwise_cons.mp htail).1 candidate hm
      have hslen := ((passes_exact p selected).mp hselected).2
      have hclen := ((passes_exact p candidate).mp hp).2
      have hl : (selected.map unionInterpretation).length = (candidate.map unionInterpretation).length := by
        simp only [List.length_map, hslen, hclen]
      exact Or.inr (reverse_lex_of_equal_length hl hlex)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.MinimumSelectionSupport
