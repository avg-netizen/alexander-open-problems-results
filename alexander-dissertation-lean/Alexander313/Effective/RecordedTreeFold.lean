import Alexander313.Effective.RecordedAdmissibility

/-!
# Primitive-recursive value folds on literal recorded trees

An explicit course table keeps the parameter fixed throughout recursion.
Unary constructors have their own operation; in particular rank counts
negations and quantifiers. The head operation receives the original literal
argument code, so a nested inspection can use its exact rank and support.
-/

noncomputable section

namespace Alexander313.RecordedFormula.ValueFold

variable {α β : Type} [Primcodable α] [Primcodable β]

def code (combine : β → β → β) (unary : β → β) (base : β)
    (head : α → Nat → Nat → β → β) (a : α) : Nat → β
  | 0 => base
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond ((tag == 2) || (tag == 3) || (tag == 4))
      (combine (code combine unary base head a p.unpair.1)
        (code combine unary base head a p.unpair.2))
      (cond (tag == 5) (unary (code combine unary base head a p))
        (cond ((tag == 6) || (tag == 7)) (unary (code combine unary base head a p.unpair.2))
          (cond (tag == 8)
            (head a p.unpair.1 p.unpair.2 (code combine unary base head a p.unpair.2)) base)))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def step (combine : β → β → β) (unary : β → β) (base : β)
    (head : α → Nat → Nat → β → β) (a : α) (h : List β) : β :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) base
    (cond ((tag == 2) || (tag == 3) || (tag == 4))
      (combine (h[p.unpair.1]?.getD base) (h[p.unpair.2]?.getD base))
      (cond (tag == 5) (unary (h[p]?.getD base))
        (cond ((tag == 6) || (tag == 7)) (unary (h[p.unpair.2]?.getD base))
          (cond (tag == 8)
            (head a p.unpair.1 p.unpair.2 (h[p.unpair.2]?.getD base)) base))))

private theorem step_primrec (combine : β → β → β) (unary : β → β) (base : β)
    (head : α → Nat → Nat → β → β) (hc : Primrec₂ combine) (hu : Primrec unary)
    (hh : Primrec (fun p : α × (Nat × (Nat × β)) => head p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec₂ (step combine unary base head) := by
  have hn : Primrec (fun p : α × List β => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : α × List β → Nat) (hf : Primrec f) :
      Primrec (fun p : α × List β => p.2[f p]?.getD base) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const base)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const base)
    ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
      (hc.comp (get _ hl) (get _ hr))
      ((test 5).cond (hu.comp (get _ hp))
        ((Primrec.or.comp (test 6) (test 7)).cond (hu.comp (get _ hr))
          ((test 8).cond
            (hh.comp (Primrec.pair Primrec.fst (Primrec.pair hl (Primrec.pair hr (get _ hr)))))
            (Primrec.const base)))))).to₂

theorem code_primrec (combine : β → β → β) (unary : β → β) (base : β)
    (head : α → Nat → Nat → β → β) (hc : Primrec₂ combine) (hu : Primrec unary)
    (hh : Primrec (fun p : α × (Nat × (Nat × β)) => head p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec₂ (code combine unary base head) := by
  have hg := Primrec.option_some.comp₂ (step_primrec combine unary base head hc hu hh)
  exact Primrec.nat_strong_rec (code combine unary base head) hg (by
    intro a n
    cases n with
    | zero => simp [step, code]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [step, code, hp, hl, hr])

def formula (combine : β → β → β) (unary : β → β) (base : β)
    (head : α → Nat → Nat → β → β) (a : α) : Syntax → β
  | .falsum => base
  | .equal _ _ => base
  | .imp φ ψ => combine (formula combine unary base head a φ) (formula combine unary base head a ψ)
  | .conj φ ψ => combine (formula combine unary base head a φ) (formula combine unary base head a ψ)
  | .disj φ ψ => combine (formula combine unary base head a φ) (formula combine unary base head a ψ)
  | .neg φ => unary (formula combine unary base head a φ)
  | .all _ φ => unary (formula combine unary base head a φ)
  | .ex _ φ => unary (formula combine unary base head a φ)
  | .know b φ => head a b.code (φ.code RecordedHead.code) (formula combine unary base head a φ)

@[simp] theorem code_formula (combine : β → β → β) (unary : β → β) (base : β)
    (head : α → Nat → Nat → β → β) (a : α) (φ : Syntax) :
    code combine unary base head a (φ.code RecordedHead.code) =
      formula combine unary base head a φ := by
  induction φ <;> simp_all [code, formula, Formula.code, Nat.unpair_pair]

end Alexander313.RecordedFormula.ValueFold
