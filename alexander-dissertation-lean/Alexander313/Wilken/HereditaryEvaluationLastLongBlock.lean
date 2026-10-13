import Alexander313.Wilken.HereditaryEvaluationPrefixLengthDescent

/-!
# The actual last nonsingleton component of Definition 3.35

A literal primitive recursive fold computes the last one-based component
index whose length exceeds one. Its complete graph derives the selected
block, its literal before/after decomposition and the fact that every later
block has length at most one. Actual component execution and its nonempty
blocks therefore derive the real n0 and its bound; no selected index,
component or phase oracle is supplied. The h/sk call at the selected
penultimate endpoint and its strict length descent remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationLastLongBlock

open EvaluationBlocks (Block)

/-- The printed one-based last-long index, with zero for no long block. -/
def lastLong : List Block → Nat
  | [] => 0
  | word :: words => if lastLong words = 0 then
      if 1 < word.length then 1 else 0
    else lastLong words + 1

theorem lastLong_primrec : Primrec lastLong := by
  have hnext : Primrec (fun p : List Block × (Block × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlength : Primrec (fun p : List Block × (Block × Nat) => p.2.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  have hzero := Primrec.eq.comp hnext (Primrec.const 0)
  have hlong := Primrec.nat_lt.comp (Primrec.const 1) hlength
  have hstep : Primrec₂ (fun p : List Block => fun s : Block × Nat =>
      if s.2 = 0 then if 1 < s.1.length then 1 else 0 else s.2 + 1) :=
    (Primrec.ite hzero (Primrec.ite hlong (Primrec.const 1) (Primrec.const 0))
      (Primrec.succ.comp hnext)).to₂
  have hf := Primrec.list_foldr Primrec.id (Primrec.const 0) hstep
  have he : (fun words : List Block => words.foldr
      (fun word n => if n = 0 then if 1 < word.length then 1 else 0 else n + 1) 0) =
      lastLong := by
    funext words
    induction words with
    | nil => rfl
    | cons word words ih => simp only [List.foldr_cons, lastLong, ih]
  rw [he] at hf
  exact hf

theorem lastLong_eq_zero (words : List Block) :
    lastLong words = 0 ↔ ∀ word ∈ words, word.length ≤ 1 := by
  induction words with
  | nil => simp only [lastLong, List.not_mem_nil, false_implies, implies_true]
  | cons word words ih =>
    by_cases hn : lastLong words = 0
    · have hrest := ih.mp hn
      rw [lastLong, if_pos hn]
      by_cases hw : 1 < word.length
      · rw [if_pos hw]
        constructor
        · intro h; omega
        · intro h; exact False.elim (hw.not_ge (h word List.mem_cons_self))
      · rw [if_neg hw]
        constructor
        · intro h w hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact le_of_not_gt hw
          · exact hrest w hm
        · intro h; rfl
    · rw [lastLong, if_neg hn]
      constructor
      · intro h; omega
      · intro h
        exact False.elim (hn (ih.mpr (fun w hm => h w (List.mem_cons_of_mem word hm))))

/-- The actual positive index constructs its selected block and certifies
that the entire later chronological suffix contains no longer block. -/
theorem lastLong_spec (words : List Block) (hn : 0 < lastLong words) :
    ∃ before word after,
      words = before ++ word :: after ∧ lastLong words = before.length + 1 ∧
      1 < word.length ∧ ∀ w ∈ after, w.length ≤ 1 := by
  induction words with
  | nil => simp only [lastLong] at hn; omega
  | cons word words ih =>
    by_cases hr : lastLong words = 0
    · by_cases hw : 1 < word.length
      · exact ⟨[], word, words, rfl, by simp only [lastLong, if_pos hr, if_pos hw, List.length_nil],
          hw, (lastLong_eq_zero words).mp hr⟩
      · simp only [lastLong, if_pos hr, if_neg hw] at hn; omega
    · obtain ⟨before, selected, after, he, hi, hlong, hafter⟩ :=
        ih (Nat.pos_of_ne_zero hr)
      refine ⟨word :: before, selected, after, ?_, ?_, hlong, hafter⟩
      · simpa only [List.cons_append] using congrArg (List.cons word) he
      · rw [lastLong, if_neg hr, hi, List.length_cons]

theorem lastLong_le_length (words : List Block) : lastLong words ≤ words.length := by
  by_cases hn : lastLong words = 0
  · rw [hn]; exact Nat.zero_le _
  · obtain ⟨before, word, after, he, hi, hw, hafter⟩ :=
      lastLong_spec words (Nat.pos_of_ne_zero hn)
    rw [hi, he, List.length_append, List.length_cons]
    omega

/-- Actual component execution derives either all singleton blocks or
the genuine final long block and the literal chronological cut. -/
theorem execute_lastLong (codes : List Nat) (words : List Block)
    (ho : words ∈ EvaluationComponents.execute codes) :
    (lastLong words = 0 ∧ ∀ word ∈ words, word.length = 1) ∨
      ∃ before word after,
        words = before ++ word :: after ∧ lastLong words = before.length + 1 ∧
        1 < word.length ∧ ∀ w ∈ after, w.length = 1 := by
  have hnonempty := EvaluationComponents.execute_nonempty_components codes words ho
  by_cases hn : lastLong words = 0
  · refine Or.inl ⟨hn, ?_⟩
    intro word hm
    have hle := (lastLong_eq_zero words).mp hn word hm
    have hpos : 0 < word.length := List.length_pos_iff.mpr (hnonempty word hm)
    omega
  · obtain ⟨before, word, after, he, hi, hw, hafter⟩ :=
      lastLong_spec words (Nat.pos_of_ne_zero hn)
    refine Or.inr ⟨before, word, after, he, hi, hw, ?_⟩
    intro w hm
    have hle := hafter w hm
    have hmem : w ∈ words := by
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem word hm)
    have hpos : 0 < w.length := List.length_pos_iff.mpr (hnonempty w hmem)
    omega

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationLastLongBlock
