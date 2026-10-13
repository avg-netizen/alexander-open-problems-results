import Alexander313.Effective.TermSyntax

/-! # Primitive-recursive numeral substitution on the actual term codes -/

namespace Alexander313

def singleNumeralSubstitution (x m : Nat) : NumericalSubstitution :=
  fun y => if y = x then some m else none

@[simp] theorem singleNumeralSubstitution_remove_self (x m : Nat) :
    NumericalSubstitution.remove (singleNumeralSubstitution x m) x = fun _ => none := by
  funext y
  by_cases hy : y = x <;> simp [singleNumeralSubstitution, NumericalSubstitution.remove, hy]

theorem singleNumeralSubstitution_remove_of_ne (x m y : Nat) (hy : y ≠ x) :
    NumericalSubstitution.remove (singleNumeralSubstitution x m) y = singleNumeralSubstitution x m := by
  funext z
  by_cases hz : z = y
  · subst z
    simp [singleNumeralSubstitution, NumericalSubstitution.remove, hy]
  · simp [NumericalSubstitution.remove, hz]

namespace EncodedSyntax

def node (tag payload : Nat) : Nat := Nat.succ (Nat.pair tag payload)

theorem node_primrec : Primrec₂ node := Primrec.succ.comp₂ Primrec₂.natPair

end EncodedSyntax

namespace Term

def numeralCode : Nat → Nat :=
  Nat.rec Term.zero.code (fun _ c => EncodedSyntax.node 2 c)

theorem numeralCode_primrec : Primrec numeralCode :=
  Primrec.nat_rec₁ Term.zero.code
    (EncodedSyntax.node_primrec.comp (Primrec.const 2) Primrec.snd).to₂

@[simp] theorem numeralCode_eq (m : Nat) : numeralCode m = (Term.numeral m).code := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (EncodedSyntax.node 2) ih

def substCode (x m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (cond (p == x) (numeralCode m) (k + 1))
      (cond (tag == 1) (k + 1)
        (cond (tag == 2) (EncodedSyntax.node 2 (substCode x m p))
          (cond ((tag == 3) || (tag == 4))
            (EncodedSyntax.node tag (Nat.pair (substCode x m p.unpair.1)
              (substCode x m p.unpair.2))) 0)))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def substitutionStep (a : Nat × Nat) (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond (tag == 0) (cond (p == a.1) (numeralCode a.2) history.length)
      (cond (tag == 1) history.length
        (cond (tag == 2) (EncodedSyntax.node 2 (history[p]?.getD 0))
          (cond ((tag == 3) || (tag == 4))
            (EncodedSyntax.node tag (Nat.pair (history[p.unpair.1]?.getD 0)
              (history[p.unpair.2]?.getD 0))) 0))))

private theorem substitutionStep_primrec : Primrec₂ substitutionStep := by
  have hn : Primrec (fun p : (Nat × Nat) × List Nat => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have hget (f : (Nat × Nat) × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : (Nat × Nat) × List Nat => p.2[f p]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const 0)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond
      ((Primrec.beq.comp hp (Primrec.fst.comp Primrec.fst)).cond
        (numeralCode_primrec.comp (Primrec.snd.comp Primrec.fst)) hn)
      ((test 1).cond hn
        ((test 2).cond (EncodedSyntax.node_primrec.comp (Primrec.const 2) (hget _ hp))
          ((Primrec.or.comp (test 3) (test 4)).cond
            (EncodedSyntax.node_primrec.comp ht
              (Primrec₂.natPair.comp (hget _ hl) (hget _ hr))) (Primrec.const 0)))))).to₂

theorem substCode_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    substCode p.1.1 p.1.2 p.2) := by
  have hg := Primrec.option_some.comp₂ substitutionStep_primrec
  exact Primrec.nat_strong_rec (fun a n => substCode a.1 a.2 n) hg (by
    intro a n
    cases n with
    | zero => simp [substitutionStep, substCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [substitutionStep, substCode, hp, hl, hr])

@[simp] theorem substCode_code (x m : Nat) (t : Term) :
    substCode x m t.code = (t.subst (singleNumeralSubstitution x m)).code := by
  induction t with
  | var y =>
    by_cases hy : y = x
    · subst y
      simp [code, substCode, subst, singleNumeralSubstitution, Nat.unpair_pair]
    · have hyb : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      simp [code, substCode, subst, singleNumeralSubstitution, Nat.unpair_pair, hy, hyb]
  | zero => simp [code, substCode, subst, Nat.unpair_pair]
  | succ t ih => simp [code, substCode, subst, Nat.unpair_pair, ih, EncodedSyntax.node]
  | add t u iht ihu =>
    simp [code, substCode, subst, Nat.unpair_pair, iht, ihu, EncodedSyntax.node]
  | mul t u iht ihu =>
    simp [code, substCode, subst, Nat.unpair_pair, iht, ihu, EncodedSyntax.node]

end Term
end Alexander313
