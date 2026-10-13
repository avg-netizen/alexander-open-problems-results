import Alexander313.Effective.TermSubstitution
import Alexander313.Arithmetic.Template

/-!
# Primitive-recursive fresh-variable bounds and literal variable shifts

Both algorithms operate on the actual numerical term serialization. Their
primitive recursion is established by a finite table of earlier values;
well-founded Lean recursion alone is not used as an effectivity claim.
-/

namespace Alexander313
namespace Term

def variableBoundCode : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (p + 1)
      (cond (tag == 2) (variableBoundCode p)
        (cond ((tag == 3) || (tag == 4))
          (max (variableBoundCode p.unpair.1) (variableBoundCode p.unpair.2)) 0))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def boundStep (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond (tag == 0) (p + 1)
      (cond (tag == 2) (history[p]?.getD 0)
        (cond ((tag == 3) || (tag == 4))
          (max (history[p.unpair.1]?.getD 0) (history[p.unpair.2]?.getD 0)) 0)))

private theorem boundStep_primrec : Primrec boundStep := by
  have hn : Primrec (fun h : List Nat => h.length) := Primrec.list_length
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have hget (f : List Nat → Nat) (hf : Primrec f) :
      Primrec (fun h : List Nat => h[f h]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const 0)
  exact (Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond (Primrec.succ.comp hp)
      ((test 2).cond (hget _ hp)
        ((Primrec.or.comp (test 3) (test 4)).cond
          (Primrec.nat_max.comp (hget _ hl) (hget _ hr)) (Primrec.const 0))))

theorem variableBoundCode_primrec : Primrec variableBoundCode := by
  have hg : Primrec₂ (fun (_ : Unit) (history : List Nat) => some (boundStep history)) :=
    ((Primrec.option_some.comp boundStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => variableBoundCode n) hg (by
    intro a n
    cases n with
    | zero => simp [boundStep, variableBoundCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [boundStep, variableBoundCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem variableBoundCode_code (t : Term) :
    variableBoundCode t.code = t.variableBound := by
  induction t <;> simp_all [variableBoundCode, code, variableBound, Nat.unpair_pair]

def shiftCode (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (EncodedSyntax.node 0 (a + p))
      (cond (tag == 1) (k + 1)
        (cond (tag == 2) (EncodedSyntax.node 2 (shiftCode a p))
          (cond ((tag == 3) || (tag == 4))
            (EncodedSyntax.node tag (Nat.pair (shiftCode a p.unpair.1)
              (shiftCode a p.unpair.2))) 0)))
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
    (cond (tag == 0) (EncodedSyntax.node 0 (a + p))
      (cond (tag == 1) history.length
        (cond (tag == 2) (EncodedSyntax.node 2 (history[p]?.getD 0))
          (cond ((tag == 3) || (tag == 4))
            (EncodedSyntax.node tag (Nat.pair (history[p.unpair.1]?.getD 0)
              (history[p.unpair.2]?.getD 0))) 0))))

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
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond
      (EncodedSyntax.node_primrec.comp (Primrec.const 0) (Primrec.nat_add.comp Primrec.fst hp))
      ((test 1).cond hn
        ((test 2).cond (EncodedSyntax.node_primrec.comp (Primrec.const 2) (hget _ hp))
          ((Primrec.or.comp (test 3) (test 4)).cond
            (EncodedSyntax.node_primrec.comp ht
              (Primrec₂.natPair.comp (hget _ hl) (hget _ hr))) (Primrec.const 0)))))).to₂

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

@[simp] theorem shiftCode_code (a : Nat) (t : Term) :
    shiftCode a t.code = (t.renameVariables (fun v => a + v)).code := by
  induction t <;>
    simp_all [code, shiftCode, renameVariables, Nat.unpair_pair, EncodedSyntax.node]

end Term
end Alexander313
