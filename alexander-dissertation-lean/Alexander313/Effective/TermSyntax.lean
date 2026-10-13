import Alexander313.Computability

/-!
# A primitive-recursive recognizer for the actual arithmetic-term codes

The recognizer follows the concrete tagged pairing serialization in
`Encoding`, rejects malformed tags and the noncanonical zero payload, and
recurses only to smaller codes. Primitive recursiveness is proved using a
finite table of earlier answers, rather than inferred from Lean termination.
-/

namespace Alexander313
namespace Term

def isCode : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) true
      (cond (tag == 1) (p == 0)
        (cond (tag == 2) (isCode p)
          (cond ((tag == 3) || (tag == 4))
            (isCode p.unpair.1 && isCode p.unpair.2) false)))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def recognitionStep (history : List Bool) : Bool :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) false
    (cond (tag == 0) true
      (cond (tag == 1) (p == 0)
        (cond (tag == 2) (history[p]?.getD false)
          (cond ((tag == 3) || (tag == 4))
            (history[p.unpair.1]?.getD false && history[p.unpair.2]?.getD false)
            false))))

private theorem recognitionStep_primrec : Primrec recognitionStep := by
  have hk : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hget (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond
    (Primrec.const false)
    ((Primrec.beq.comp ht (Primrec.const 0)).cond (Primrec.const true)
      ((Primrec.beq.comp ht (Primrec.const 1)).cond
        (Primrec.beq.comp hp (Primrec.const 0))
        ((Primrec.beq.comp ht (Primrec.const 2)).cond (hget _ hp)
          ((Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 3))
            (Primrec.beq.comp ht (Primrec.const 4))).cond
            (Primrec.and.comp (hget _ hl) (hget _ hr)) (Primrec.const false)))))

theorem isCode_primrec : Primrec isCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Bool) => some (recognitionStep h)) :=
    ((Primrec.option_some.comp recognitionStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => isCode n) hg
    (by
      intro a n
      cases n with
      | zero => simp [recognitionStep, isCode]
      | succ k =>
        have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hl : k.unpair.2.unpair.1 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_left_le _) hp
        have hr : k.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hp
        simp [recognitionStep, isCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem isCode_code (t : Term) : isCode t.code = true := by
  induction t <;> simp_all [code, isCode, Nat.unpair_pair]

theorem isCode_sound (n : Nat) : isCode n = true → ∃ t : Term, t.code = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [isCode]
    | succ k =>
      intro hn
      let tag := k.unpair.1
      let p := k.unpair.2
      have hp : p < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : p.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le p) hp
      have hr : p.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le p) hp
      have hk : k = Nat.pair tag p := (Nat.pair_unpair k).symm
      by_cases h0 : tag = 0
      · refine ⟨.var p, ?_⟩
        rw [hk, h0]
        rfl
      by_cases h1 : tag = 1
      · have hp0 : p = 0 := by simpa [isCode, tag, p, h0, h1] using hn
        refine ⟨.zero, ?_⟩
        rw [hk, h1, hp0]
        rfl
      by_cases h2 : tag = 2
      · have hchild : isCode p = true := by simpa [isCode, tag, p, h0, h1, h2] using hn
        obtain ⟨t, ht⟩ := ih p hp hchild
        refine ⟨.succ t, ?_⟩
        rw [hk, h2]
        simp only [code, ht]
      by_cases h3 : tag = 3
      · have hchildren : isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3] using hn
        obtain ⟨t, ht⟩ := ih _ hl hchildren.1
        obtain ⟨u, hu⟩ := ih _ hr hchildren.2
        refine ⟨.add t u, ?_⟩
        rw [hk, h3]
        simp only [code, ht, hu, Nat.pair_unpair]
      by_cases h4 : tag = 4
      · have hchildren : isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4] using hn
        obtain ⟨t, ht⟩ := ih _ hl hchildren.1
        obtain ⟨u, hu⟩ := ih _ hr hchildren.2
        refine ⟨.mul t u, ?_⟩
        rw [hk, h4]
        simp only [code, ht, hu, Nat.pair_unpair]
      simp [isCode, tag, p, h0, h1, h2, h3, h4] at hn

theorem isCode_iff (n : Nat) : isCode n = true ↔ ∃ t : Term, t.code = n :=
  ⟨isCode_sound n, fun ⟨t, ht⟩ => ht ▸ isCode_code t⟩

end Term
end Alexander313
