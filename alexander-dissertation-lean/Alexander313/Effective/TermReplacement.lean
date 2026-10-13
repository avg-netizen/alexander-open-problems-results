import Alexander313.Effective.LiteralFormation

/-!
# Primitive-recursive literal replacement by an arithmetic term

These algorithms implement the existing syntactic `substTerm` operations.
They do not assert a modal substitution theorem. In particular, semantic
capture conditions remain the responsibility of the theorem using a term
replacement, as in the separately proved PA successor instance.
-/

namespace Alexander313
namespace Term

def replaceCode (x replacement : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (cond (p == x) replacement (k + 1))
      (cond (tag == 1) (k + 1)
        (cond (tag == 2) (EncodedSyntax.node 2 (replaceCode x replacement p))
          (cond ((tag == 3) || (tag == 4))
            (EncodedSyntax.binary tag (replaceCode x replacement p.unpair.1)
              (replaceCode x replacement p.unpair.2)) 0)))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def replacementStep (a : Nat × Nat) (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond (tag == 0) (cond (p == a.1) a.2 history.length)
      (cond (tag == 1) history.length
        (cond (tag == 2) (EncodedSyntax.node 2 (history[p]?.getD 0))
          (cond ((tag == 3) || (tag == 4))
            (EncodedSyntax.binary tag (history[p.unpair.1]?.getD 0)
              (history[p.unpair.2]?.getD 0)) 0))))

private theorem replacementStep_primrec : Primrec₂ replacementStep := by
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
        (Primrec.snd.comp Primrec.fst) hn)
      ((test 1).cond hn
        ((test 2).cond (EncodedSyntax.node_primrec.comp (Primrec.const 2) (hget _ hp))
          ((Primrec.or.comp (test 3) (test 4)).cond
            (EncodedSyntax.node_primrec.comp ht
              (Primrec₂.natPair.comp (hget _ hl) (hget _ hr))) (Primrec.const 0)))))).to₂

theorem replaceCode_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    replaceCode p.1.1 p.1.2 p.2) := by
  have hg := Primrec.option_some.comp₂ replacementStep_primrec
  exact Primrec.nat_strong_rec (fun a n => replaceCode a.1 a.2 n) hg (by
    intro a n
    cases n with
    | zero => simp [replacementStep, replaceCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [replacementStep, replaceCode, hp, hl, hr])

@[simp] theorem replaceCode_code (x : Nat) (replacement t : Term) :
    replaceCode x replacement.code t.code = (Term.substTerm x replacement t).code := by
  induction t with
  | var y =>
    by_cases hy : y = x
    · simp [replaceCode, code, substTerm, Nat.unpair_pair, hy]
    · have hyb : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      simp [replaceCode, code, substTerm, Nat.unpair_pair, hy, hyb]
  | zero => simp [replaceCode, code, substTerm, Nat.unpair_pair]
  | succ t ih =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, ih, EncodedSyntax.node]
  | add t u iht ihu =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, iht, ihu,
      EncodedSyntax.binary, EncodedSyntax.node]
  | mul t u iht ihu =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, iht, ihu,
      EncodedSyntax.binary, EncodedSyntax.node]

theorem substTerm_primrec : Primrec (fun p : (Nat × Term) × Term =>
    Term.substTerm p.1.1 p.1.2 p.2) := by
  apply Primrec.encode_iff.1
  have h := replaceCode_primrec.comp
    (((Primrec.fst.comp Primrec.fst).pair (code_primrec.comp (Primrec.snd.comp Primrec.fst))).pair
      (code_primrec.comp Primrec.snd))
  simpa only [encode_eq_code, replaceCode_code] using h

end Term

namespace Formula

def replaceCode (x replacement : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (k + 1)
      (cond (tag == 1) (EncodedSyntax.binary 1
        (Term.replaceCode x replacement p.unpair.1) (Term.replaceCode x replacement p.unpair.2))
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (EncodedSyntax.binary tag (replaceCode x replacement p.unpair.1)
            (replaceCode x replacement p.unpair.2))
          (cond (tag == 5) (EncodedSyntax.node 5 (replaceCode x replacement p))
            (cond ((tag == 6) || (tag == 7))
              (cond (p.unpair.1 == x) (k + 1)
                (EncodedSyntax.binary tag p.unpair.1 (replaceCode x replacement p.unpair.2)))
              (cond (tag == 8) (EncodedSyntax.binary 8 p.unpair.1
                (replaceCode x replacement p.unpair.2)) 0)))))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def replacementStep (a : Nat × Nat) (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond (tag == 0) history.length
      (cond (tag == 1) (EncodedSyntax.binary 1
        (Term.replaceCode a.1 a.2 p.unpair.1) (Term.replaceCode a.1 a.2 p.unpair.2))
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (EncodedSyntax.binary tag (history[p.unpair.1]?.getD 0) (history[p.unpair.2]?.getD 0))
          (cond (tag == 5) (EncodedSyntax.node 5 (history[p]?.getD 0))
            (cond ((tag == 6) || (tag == 7))
              (cond (p.unpair.1 == a.1) history.length
                (EncodedSyntax.binary tag p.unpair.1 (history[p.unpair.2]?.getD 0)))
              (cond (tag == 8) (EncodedSyntax.binary 8 p.unpair.1
                (history[p.unpair.2]?.getD 0)) 0))))))

private theorem replacementStep_primrec : Primrec₂ replacementStep := by
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
  have hterm (f : (Nat × Nat) × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : (Nat × Nat) × List Nat => Term.replaceCode p.1.1 p.1.2 (f p)) :=
    Term.replaceCode_primrec.comp (Primrec.fst.pair hf)
  have hbinary := EncodedSyntax.node_primrec.comp ht
    (Primrec₂.natPair.comp (hget _ hl) (hget _ hr))
  have hheaded := EncodedSyntax.node_primrec.comp ht (Primrec₂.natPair.comp hl (hget _ hr))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond hn
      ((test 1).cond ((EncodedSyntax.binary_primrec 1).comp (hterm _ hl) (hterm _ hr))
        ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond hbinary
          ((test 5).cond (EncodedSyntax.node_primrec.comp (Primrec.const 5) (hget _ hp))
            ((Primrec.or.comp (test 6) (test 7)).cond
              ((Primrec.beq.comp hl (Primrec.fst.comp Primrec.fst)).cond hn hheaded)
              ((test 8).cond ((EncodedSyntax.binary_primrec 8).comp hl (hget _ hr))
                (Primrec.const 0)))))))).to₂

theorem replaceCode_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    replaceCode p.1.1 p.1.2 p.2) := by
  have hg := Primrec.option_some.comp₂ replacementStep_primrec
  exact Primrec.nat_strong_rec (fun a n => replaceCode a.1 a.2 n) hg (by
    intro a n
    cases n with
    | zero => simp [replacementStep, replaceCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [replacementStep, replaceCode, hp, hl, hr])

@[simp] theorem replaceCode_code (x : Nat) (replacement : Term) (φ : Formula Nat) :
    replaceCode x replacement.code (φ.code id) = (φ.substTerm x replacement).code id := by
  induction φ with
  | falsum => simp [replaceCode, code, substTerm, Nat.unpair_pair]
  | equal t u =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair,
      Term.replaceCode_code, EncodedSyntax.binary, EncodedSyntax.node]
  | imp φ ψ ihφ ihψ =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, ihφ, ihψ,
      EncodedSyntax.binary, EncodedSyntax.node]
  | conj φ ψ ihφ ihψ =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, ihφ, ihψ,
      EncodedSyntax.binary, EncodedSyntax.node]
  | disj φ ψ ihφ ihψ =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, ihφ, ihψ,
      EncodedSyntax.binary, EncodedSyntax.node]
  | neg φ ih => simp [replaceCode, code, substTerm, Nat.unpair_pair, ih, EncodedSyntax.node]
  | all y φ ih =>
    by_cases hy : y = x
    · simp [replaceCode, code, substTerm, Nat.unpair_pair, hy, ih,
        EncodedSyntax.binary, EncodedSyntax.node]
    · have hyb : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      simp [replaceCode, code, substTerm, Nat.unpair_pair, hy, hyb, ih,
        EncodedSyntax.binary, EncodedSyntax.node]
  | ex y φ ih =>
    by_cases hy : y = x
    · simp [replaceCode, code, substTerm, Nat.unpair_pair, hy, ih,
        EncodedSyntax.binary, EncodedSyntax.node]
    · have hyb : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      simp [replaceCode, code, substTerm, Nat.unpair_pair, hy, hyb, ih,
        EncodedSyntax.binary, EncodedSyntax.node]
  | know j φ ih =>
    simp [replaceCode, code, substTerm, Nat.unpair_pair, ih, EncodedSyntax.binary, EncodedSyntax.node]

theorem substTerm_primrec : Primrec (fun p : (Nat × Term) × Formula Nat =>
    p.2.substTerm p.1.1 p.1.2) := by
  apply Primrec.encode_iff.1
  have h := replaceCode_primrec.comp
    (((Primrec.fst.comp Primrec.fst).pair (Term.code_primrec.comp (Primrec.snd.comp Primrec.fst))).pair
      (code_primrec.comp Primrec.snd))
  simpa only [encode_eq_code, replaceCode_code] using h

end Formula
end Alexander313
