import Alexander313.Effective.TermSyntax

/-!
# A primitive-recursive recognizer for the original-language formula codes

Owners and variables are natural numbers. The recognizer uses exactly
`Formula.code id`, with canonical falsum/term payloads; an accepted natural
number really decodes to a formula in this language.
-/

namespace Alexander313
namespace Formula

def isCode : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (p == 0)
      (cond (tag == 1) (Term.isCode p.unpair.1 && Term.isCode p.unpair.2)
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (isCode p.unpair.1 && isCode p.unpair.2)
          (cond (tag == 5) (isCode p)
            (cond ((tag == 6) || (tag == 7) || (tag == 8)) (isCode p.unpair.2) false))))
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
    (cond (tag == 0) (p == 0)
      (cond (tag == 1) (Term.isCode p.unpair.1 && Term.isCode p.unpair.2)
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (history[p.unpair.1]?.getD false && history[p.unpair.2]?.getD false)
          (cond (tag == 5) (history[p]?.getD false)
            (cond ((tag == 6) || (tag == 7) || (tag == 8))
              (history[p.unpair.2]?.getD false) false)))))

private theorem recognitionStep_primrec : Primrec recognitionStep := by
  have hk : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have hget (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond
    (Primrec.const false)
    ((test 0).cond (Primrec.beq.comp hp (Primrec.const 0))
      ((test 1).cond
        (Primrec.and.comp (Term.isCode_primrec.comp hl) (Term.isCode_primrec.comp hr))
        ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
          (Primrec.and.comp (hget _ hl) (hget _ hr))
          ((test 5).cond (hget _ hp)
            ((Primrec.or.comp (Primrec.or.comp (test 6) (test 7)) (test 8)).cond
              (hget _ hr) (Primrec.const false))))))

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

@[simp] theorem isCode_code (φ : Formula Nat) : isCode (φ.code id) = true := by
  induction φ <;> simp_all [code, isCode, Nat.unpair_pair, Term.isCode_code]

theorem isCode_sound (n : Nat) : isCode n = true → ∃ φ : Formula Nat, φ.code id = n := by
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
      · have hp0 : p = 0 := by simpa [isCode, tag, p, h0] using hn
        refine ⟨.falsum, ?_⟩
        rw [hk, h0, hp0]
        rfl
      by_cases h1 : tag = 1
      · have hchildren : Term.isCode p.unpair.1 = true ∧ Term.isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1] using hn
        obtain ⟨t, ht⟩ := Term.isCode_sound _ hchildren.1
        obtain ⟨u, hu⟩ := Term.isCode_sound _ hchildren.2
        refine ⟨.equal t u, ?_⟩
        rw [hk, h1]
        simp only [code, ht, hu, Nat.pair_unpair]
      by_cases h2 : tag = 2
      · have hchildren : isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2] using hn
        obtain ⟨φ, hφ⟩ := ih _ hl hchildren.1
        obtain ⟨ψ, hψ⟩ := ih _ hr hchildren.2
        refine ⟨.imp φ ψ, ?_⟩
        rw [hk, h2]
        simp only [code, hφ, hψ, Nat.pair_unpair]
      by_cases h3 : tag = 3
      · have hchildren : isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3] using hn
        obtain ⟨φ, hφ⟩ := ih _ hl hchildren.1
        obtain ⟨ψ, hψ⟩ := ih _ hr hchildren.2
        refine ⟨.conj φ ψ, ?_⟩
        rw [hk, h3]
        simp only [code, hφ, hψ, Nat.pair_unpair]
      by_cases h4 : tag = 4
      · have hchildren : isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4] using hn
        obtain ⟨φ, hφ⟩ := ih _ hl hchildren.1
        obtain ⟨ψ, hψ⟩ := ih _ hr hchildren.2
        refine ⟨.disj φ ψ, ?_⟩
        rw [hk, h4]
        simp only [code, hφ, hψ, Nat.pair_unpair]
      by_cases h5 : tag = 5
      · have hchild : isCode p = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4, h5] using hn
        obtain ⟨φ, hφ⟩ := ih _ hp hchild
        refine ⟨.neg φ, ?_⟩
        rw [hk, h5]
        simp only [code, hφ]
      by_cases h6 : tag = 6
      · have hchild : isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4, h5, h6] using hn
        obtain ⟨φ, hφ⟩ := ih _ hr hchild
        refine ⟨.all p.unpair.1 φ, ?_⟩
        rw [hk, h6]
        simp only [code, hφ, Nat.pair_unpair]
      by_cases h7 : tag = 7
      · have hchild : isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4, h5, h6, h7] using hn
        obtain ⟨φ, hφ⟩ := ih _ hr hchild
        refine ⟨.ex p.unpair.1 φ, ?_⟩
        rw [hk, h7]
        simp only [code, hφ, Nat.pair_unpair]
      by_cases h8 : tag = 8
      · have hchild : isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4, h5, h6, h7, h8] using hn
        obtain ⟨φ, hφ⟩ := ih _ hr hchild
        refine ⟨.know p.unpair.1 φ, ?_⟩
        rw [hk, h8]
        simp only [code, hφ, Nat.pair_unpair, id_eq]
      simp [isCode, tag, p, h0, h1, h2, h3, h4, h5, h6, h7, h8] at hn

theorem isCode_iff (n : Nat) : isCode n = true ↔ ∃ φ : Formula Nat, φ.code id = n :=
  ⟨isCode_sound n, fun ⟨φ, hφ⟩ => hφ ▸ isCode_code φ⟩

end Formula
end Alexander313
