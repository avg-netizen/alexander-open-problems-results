import Alexander313.Effective.TermSubstitution
import Alexander313.FreeVariables

/-! # Primitive-recursive numeral instances in the original modal language -/

namespace Alexander313
namespace Formula

def substCode (x m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (k + 1)
      (cond (tag == 1) (EncodedSyntax.node 1
        (Nat.pair (Term.substCode x m p.unpair.1) (Term.substCode x m p.unpair.2)))
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (EncodedSyntax.node tag (Nat.pair (substCode x m p.unpair.1)
            (substCode x m p.unpair.2)))
          (cond (tag == 5) (EncodedSyntax.node 5 (substCode x m p))
            (cond ((tag == 6) || (tag == 7))
              (cond (p.unpair.1 == x) (k + 1)
                (EncodedSyntax.node tag (Nat.pair p.unpair.1 (substCode x m p.unpair.2))))
              (cond (tag == 8)
                (EncodedSyntax.node 8 (Nat.pair p.unpair.1 (substCode x m p.unpair.2))) 0)))))
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
    (cond (tag == 0) history.length
      (cond (tag == 1) (EncodedSyntax.node 1
        (Nat.pair (Term.substCode a.1 a.2 p.unpair.1) (Term.substCode a.1 a.2 p.unpair.2)))
        (cond ((tag == 2) || (tag == 3) || (tag == 4))
          (EncodedSyntax.node tag (Nat.pair (history[p.unpair.1]?.getD 0)
            (history[p.unpair.2]?.getD 0)))
          (cond (tag == 5) (EncodedSyntax.node 5 (history[p]?.getD 0))
            (cond ((tag == 6) || (tag == 7))
              (cond (p.unpair.1 == a.1) history.length
                (EncodedSyntax.node tag (Nat.pair p.unpair.1 (history[p.unpair.2]?.getD 0))))
              (cond (tag == 8)
                (EncodedSyntax.node 8 (Nat.pair p.unpair.1 (history[p.unpair.2]?.getD 0))) 0))))))

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
  have hterm (f : (Nat × Nat) × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : (Nat × Nat) × List Nat => Term.substCode p.1.1 p.1.2 (f p)) :=
    Term.substCode_primrec.comp (Primrec.fst.pair hf)
  have hbinary := EncodedSyntax.node_primrec.comp ht
    (Primrec₂.natPair.comp (hget _ hl) (hget _ hr))
  have hheaded := EncodedSyntax.node_primrec.comp ht (Primrec₂.natPair.comp hl (hget _ hr))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond hn
      ((test 1).cond
        (EncodedSyntax.node_primrec.comp (Primrec.const 1)
          (Primrec₂.natPair.comp (hterm _ hl) (hterm _ hr)))
        ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond hbinary
          ((test 5).cond (EncodedSyntax.node_primrec.comp (Primrec.const 5) (hget _ hp))
            ((Primrec.or.comp (test 6) (test 7)).cond
              ((Primrec.beq.comp hl (Primrec.fst.comp Primrec.fst)).cond hn hheaded)
              ((test 8).cond
                (EncodedSyntax.node_primrec.comp (Primrec.const 8)
                  (Primrec₂.natPair.comp hl (hget _ hr))) (Primrec.const 0)))))))).to₂

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

@[simp] theorem substCode_code (x m : Nat) (φ : Formula Nat) :
    substCode x m (φ.code id) = (φ.subst (singleNumeralSubstitution x m)).code id := by
  induction φ with
  | falsum => simp [code, substCode, subst, Nat.unpair_pair]
  | equal t u =>
    simp [code, substCode, subst, Nat.unpair_pair, Term.substCode_code, EncodedSyntax.node]
  | imp φ ψ ihφ ihψ =>
    simp [code, substCode, subst, Nat.unpair_pair, ihφ, ihψ, EncodedSyntax.node]
  | conj φ ψ ihφ ihψ =>
    simp [code, substCode, subst, Nat.unpair_pair, ihφ, ihψ, EncodedSyntax.node]
  | disj φ ψ ihφ ihψ =>
    simp [code, substCode, subst, Nat.unpair_pair, ihφ, ihψ, EncodedSyntax.node]
  | neg φ ih => simp [code, substCode, subst, Nat.unpair_pair, ih, EncodedSyntax.node]
  | all y φ ih =>
    by_cases hy : y = x
    · subst y
      simp [code, substCode, subst, Nat.unpair_pair, EncodedSyntax.node]
    · have hyb : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      simp [code, substCode, subst, Nat.unpair_pair, hy, hyb,
        singleNumeralSubstitution_remove_of_ne x m y hy, ih, EncodedSyntax.node]
  | ex y φ ih =>
    by_cases hy : y = x
    · subst y
      simp [code, substCode, subst, Nat.unpair_pair, EncodedSyntax.node]
    · have hyb : (y == x) = false := beq_eq_false_iff_ne.mpr hy
      simp [code, substCode, subst, Nat.unpair_pair, hy, hyb,
        singleNumeralSubstitution_remove_of_ne x m y hy, ih, EncodedSyntax.node]
  | know j φ ih => simp [code, substCode, subst, Nat.unpair_pair, ih, EncodedSyntax.node]

end Formula

theorem UnaryFormula.close_eq_single (φ : UnaryFormula Nat) (s : Assignment) :
    φ.body.close s = φ.body.subst (singleNumeralSubstitution φ.input (s φ.input)) := by
  apply Formula.subst_eq_of_agree
  intro v hv
  have hvx : v = φ.input := by
    simpa only [φ.freeVars_exact, Finset.mem_singleton] using hv
  subst v
  simp [singleNumeralSubstitution]

theorem UnaryFormula.close_code (φ : UnaryFormula Nat) (s : Assignment) :
    (φ.body.close s).code id =
      Formula.substCode φ.input (s φ.input) (φ.body.code id) := by
  rw [φ.close_eq_single, Formula.substCode_code]

end Alexander313
