import Alexander313.Alexander.BLProofChecker
import Alexander313.Alexander.SourceLabelFormation

/-!
# Effective capture-safe variable substitution tests

The numerical test is the existing source `VarSubstitutable` condition. It
uses the actual free-variable membership algorithm and respects binder
shadowing. It adds no substitution principle to weak modal validity.
-/

namespace Alexander313.Formula

def variableSubstitutableCode (x y : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond ((tag == 0) || (tag == 1)) true
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (variableSubstitutableCode x y p.unpair.1 &&
          variableSubstitutableCode x y p.unpair.2)
        (cond (tag == 5) (variableSubstitutableCode x y p)
          (cond ((tag == 6) || (tag == 7))
            ((p.unpair.1 == x) ||
              ((!(p.unpair.1 == y) || !(freeMemCode x p.unpair.2)) &&
                variableSubstitutableCode x y p.unpair.2))
            (cond (tag == 8) (variableSubstitutableCode x y p.unpair.2) false))))
termination_by c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def variableStep (xy : Nat × Nat) (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) false
    (cond ((tag == 0) || (tag == 1)) true
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (h[p.unpair.1]?.getD false && h[p.unpair.2]?.getD false)
        (cond (tag == 5) (h[p]?.getD false)
          (cond ((tag == 6) || (tag == 7))
            ((p.unpair.1 == xy.1) ||
              ((!(p.unpair.1 == xy.2) || !(freeMemCode xy.1 p.unpair.2)) &&
                h[p.unpair.2]?.getD false))
            (cond (tag == 8) (h[p.unpair.2]?.getD false) false)))))

private theorem variableStep_primrec : Primrec₂ variableStep := by
  have hn : Primrec (fun p : (Nat × Nat) × List Bool => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hx : Primrec (fun p : (Nat × Nat) × List Bool => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hy : Primrec (fun p : (Nat × Nat) × List Bool => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : (Nat × Nat) × List Bool → Nat) (hf : Primrec f) :
      Primrec (fun p : (Nat × Nat) × List Bool => p.2[f p]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf)
      (Primrec.const false)
  have hbound := Primrec.or.comp (Primrec.beq.comp hl hx)
    (Primrec.and.comp
      (Primrec.or.comp (Primrec.not.comp (Primrec.beq.comp hl hy))
        (Primrec.not.comp (freeMemCode_primrec.comp hx hr))) (get _ hr))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const false)
    ((Primrec.or.comp (test 0) (test 1)).cond (Primrec.const true)
      ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
        (Primrec.and.comp (get _ hl) (get _ hr))
        ((test 5).cond (get _ hp)
          ((Primrec.or.comp (test 6) (test 7)).cond hbound
            ((test 8).cond (get _ hr) (Primrec.const false))))))).to₂

theorem variableSubstitutableCode_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => variableSubstitutableCode p.1.1 p.1.2 p.2) := by
  have hg := Primrec.option_some.comp₂ variableStep_primrec
  exact Primrec.nat_strong_rec
    (fun (xy : Nat × Nat) c => variableSubstitutableCode xy.1 xy.2 c) hg (by
      intro xy c
      cases c with
      | zero => simp [variableStep, variableSubstitutableCode]
      | succ k =>
        have hp : k.unpair.2 < k + 1 :=
          Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hl : k.unpair.2.unpair.1 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_left_le _) hp
        have hr : k.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hp
        simp [variableStep, variableSubstitutableCode, hp, hl, hr])

@[simp] theorem variableSubstitutableCode_code (x y : Nat) (φ : Formula Nat) :
    variableSubstitutableCode x y (φ.code id) = variableSubstitutable? x y φ := by
  induction φ <;> simp_all [code, variableSubstitutableCode,
    variableSubstitutable?, Nat.unpair_pair, freeMemCode_code, Bool.beq_eq_decide_eq]

theorem variableSubstitutable?_primrec : Primrec
    (fun p : (Nat × Nat) × Formula Nat => variableSubstitutable? p.1.1 p.1.2 p.2) := by
  simpa only [variableSubstitutableCode_code] using
    variableSubstitutableCode_primrec.comp
      (Primrec.fst.pair (Formula.code_primrec.comp Primrec.snd))

theorem varSubstitutable_primrec : PrimrecPred
    (fun p : (Nat × Nat) × Formula Nat => p.2.VarSubstitutable p.1.1 p.1.2) :=
  (Primrec.eq.comp variableSubstitutable?_primrec (Primrec.const true)).of_eq
    (fun p => variableSubstitutable?_eq_true p.1.1 p.1.2 p.2)

end Alexander313.Formula
