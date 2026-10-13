import Alexander313.Effective.TermOperations

/-!
# Primitive-recursive literal variable shifts of modal syntax

Every bound and free variable is shifted together. Knowledge owners stay
unchanged. This is a numerical syntax operation, with no semantic claim
about arbitrary-term substitution beneath a knowledge operator.
-/

namespace Alexander313

namespace EncodedSyntax

def binary (tag left right : Nat) : Nat := node tag (Nat.pair left right)

theorem binary_primrec (tag : Nat) : Primrec₂ (binary tag) :=
  node_primrec.comp (Primrec.const tag) Primrec₂.natPair

def «variable» (x : Nat) : Nat := node 0 x

theorem variable_primrec : Primrec «variable» :=
  node_primrec.comp (Primrec.const 0) Primrec.id

@[simp] theorem variable_code (x : Nat) : «variable» x = (Term.var x).code := rfl

end EncodedSyntax

namespace Formula

def shiftCode (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (k + 1)
      (cond (tag == 1) (EncodedSyntax.binary 1
        (Term.shiftCode a p.unpair.1) (Term.shiftCode a p.unpair.2))
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (EncodedSyntax.binary tag (shiftCode a p.unpair.1) (shiftCode a p.unpair.2))
          (cond (tag == 5) (EncodedSyntax.node 5 (shiftCode a p))
            (cond ((tag == 6) || (tag == 7))
              (EncodedSyntax.binary tag (a + p.unpair.1) (shiftCode a p.unpair.2))
              (cond (tag == 8) (EncodedSyntax.binary 8 p.unpair.1 (shiftCode a p.unpair.2)) 0)))))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def shiftStep (a : Nat) (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond (tag == 0) history.length
      (cond (tag == 1) (EncodedSyntax.binary 1
        (Term.shiftCode a p.unpair.1) (Term.shiftCode a p.unpair.2))
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (EncodedSyntax.binary tag (history[p.unpair.1]?.getD 0) (history[p.unpair.2]?.getD 0))
          (cond (tag == 5) (EncodedSyntax.node 5 (history[p]?.getD 0))
            (cond ((tag == 6) || (tag == 7))
              (EncodedSyntax.binary tag (a + p.unpair.1) (history[p.unpair.2]?.getD 0))
              (cond (tag == 8) (EncodedSyntax.binary 8 p.unpair.1
                (history[p.unpair.2]?.getD 0)) 0))))))

private theorem shiftStep_primrec : Primrec₂ shiftStep := by
  have hn : Primrec (fun p : Nat × List Nat => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have hget (f : Nat × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : Nat × List Nat => p.2[f p]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const 0)
  have hterm (f : Nat × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : Nat × List Nat => Term.shiftCode p.1 (f p)) :=
    Term.shiftCode_primrec.comp Primrec.fst hf
  have hbinary := EncodedSyntax.node_primrec.comp ht
    (Primrec₂.natPair.comp (hget _ hl) (hget _ hr))
  have hbound := EncodedSyntax.node_primrec.comp ht
    (Primrec₂.natPair.comp (Primrec.nat_add.comp Primrec.fst hl) (hget _ hr))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond hn
      ((test 1).cond ((EncodedSyntax.binary_primrec 1).comp (hterm _ hl) (hterm _ hr))
        ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond hbinary
          ((test 5).cond (EncodedSyntax.node_primrec.comp (Primrec.const 5) (hget _ hp))
            ((Primrec.or.comp (test 6) (test 7)).cond hbound
              ((test 8).cond ((EncodedSyntax.binary_primrec 8).comp hl (hget _ hr))
                (Primrec.const 0)))))))).to₂

theorem shiftCode_primrec : Primrec₂ shiftCode := by
  have hg := Primrec.option_some.comp₂ shiftStep_primrec
  exact Primrec.nat_strong_rec shiftCode hg (by
    intro a n
    cases n with
    | zero => simp [shiftStep, shiftCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [shiftStep, shiftCode, hp, hl, hr])

@[simp] theorem shiftCode_code (a : Nat) (φ : Formula Nat) :
    shiftCode a (φ.code id) = (φ.renameVariables (fun v => a + v)).code id := by
  induction φ <;>
    simp_all [code, shiftCode, renameVariables, Nat.unpair_pair,
      Term.shiftCode_code, EncodedSyntax.binary, EncodedSyntax.node]

end Formula
end Alexander313
