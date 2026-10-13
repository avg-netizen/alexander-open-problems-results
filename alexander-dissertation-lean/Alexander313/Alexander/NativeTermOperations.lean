import Alexander313.Alexander.NativeClosedLabels

/-!
# Effective native term substitution and binding

`rewriteCode` replaces variable leaves by complete term codes. Its finite
history proof is instantiated below with actual free-variable substitution
and with the variable action of native first-order binding. Modal source
arguments are relation-symbol labels and are not substituted by this code.
-/

namespace Alexander313.Delta.NativeTerm

variable {A : Type} [Primcodable A]

def rewriteCode («variable» : A → Nat → Nat) (a : A) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) («variable» a p)
      (cond (tag == 1) (k + 1)
        (cond (tag == 2) (EncodedSyntax.node 2 (rewriteCode «variable» a p))
          (cond ((tag == 3) || (tag == 4)) (EncodedSyntax.node tag
            (Nat.pair (rewriteCode «variable» a p.unpair.1)
              (rewriteCode «variable» a p.unpair.2))) 0)))
termination_by c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def rewriteStep («variable» : A → Nat → Nat) (a : A) (h : List Nat) : Nat :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) 0
    (cond (tag == 0) («variable» a p)
      (cond (tag == 1) h.length
        (cond (tag == 2) (EncodedSyntax.node 2 (h[p]?.getD 0))
          (cond ((tag == 3) || (tag == 4)) (EncodedSyntax.node tag
            (Nat.pair (h[p.unpair.1]?.getD 0) (h[p.unpair.2]?.getD 0))) 0))))

private theorem rewriteStep_primrec {«variable» : A → Nat → Nat}
    (hv : Primrec₂ «variable») : Primrec₂ (rewriteStep «variable») := by
  have hn : Primrec (fun p : A × List Nat => p.2.length) := Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : A × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : A × List Nat => p.2[f p]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const 0)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((test 0).cond (hv.comp Primrec.fst hp)
      ((test 1).cond hn
        ((test 2).cond (EncodedSyntax.node_primrec.comp (Primrec.const 2) (get _ hp))
          ((Primrec.or.comp (test 3) (test 4)).cond
            (EncodedSyntax.node_primrec.comp ht (Primrec₂.natPair.comp (get _ hl) (get _ hr)))
            (Primrec.const 0)))))).to₂

theorem rewriteCode_primrec {«variable» : A → Nat → Nat} (hv : Primrec₂ «variable») :
    Primrec₂ (rewriteCode «variable») := by
  have hg := Primrec.option_some.comp₂ (rewriteStep_primrec hv)
  exact Primrec.nat_strong_rec (rewriteCode «variable») hg (by
    intro a c
    cases c with
    | zero => simp [rewriteStep, rewriteCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [rewriteStep, rewriteCode, hp, hl, hr])

theorem rewriteCode_subst {«variable» : A → Nat → Nat} (a : A) {n m : Nat}
    (f : Nat ⊕ Fin n → Syntax m)
    (hv : ∀ v, «variable» a (variableCode v) = code (f v)) (t : Syntax n) :
    rewriteCode «variable» a (code t) = code (t.subst f) := by
  induction t with
  | var v => simpa [rewriteCode, code_var, Nat.unpair_pair] using hv v
  | func g ts ih =>
    cases g <;> simp_all [rewriteCode, code, toLiteral, Term.code,
      FirstOrder.Language.Term.subst, Nat.unpair_pair, EncodedSyntax.node]

theorem rewriteCode_relabel {«variable» : A → Nat → Nat} (a : A) {n m : Nat}
    (f : Nat ⊕ Fin n → Nat ⊕ Fin m)
    (hv : ∀ v, «variable» a (variableCode v) = code (.var (f v))) (t : Syntax n) :
    rewriteCode «variable» a (code t) = code (t.relabel f) := by
  have ht : t.subst (fun v => .var (f v)) = t.relabel f := by
    induction t <;> simp_all [FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel]
  rw [← ht]
  exact rewriteCode_subst a (fun v => .var (f v)) hv t

def substVariableCode (a : Nat × Nat) (p : Nat) : Nat :=
  cond ((p.unpair.1 == 0) && (p.unpair.2 == a.1)) a.2 (EncodedSyntax.node 0 p)

theorem substVariableCode_primrec : Primrec₂ substVariableCode := by
  have hp : Primrec (fun q : (Nat × Nat) × Nat => q.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  exact ((Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp hp) (Primrec.const 0))
    (Primrec.beq.comp (Primrec.snd.comp hp) (Primrec.fst.comp Primrec.fst))).cond
      (Primrec.snd.comp Primrec.fst)
      (EncodedSyntax.node_primrec.comp (Primrec.const 0) Primrec.snd)).to₂

def substCode (x replacement c : Nat) : Nat :=
  rewriteCode substVariableCode (x, replacement) c

theorem substCode_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => substCode p.1.1 p.1.2 p.2) :=
  rewriteCode_primrec substVariableCode_primrec

theorem freeCode_relabel {n : Nat} (t : FreeSyntax) :
    code (n := n) (t.relabel Sum.inl) = freeCode t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    cases f <;> simp_all [code, toLiteral, freeCode, freeTermEquiv,
      FirstOrder.Language.Term.relabelEquiv, FirstOrder.Language.Term.relabel, Term.code]

@[simp] theorem substCode_code (x : Nat) (replacement : FreeSyntax)
    {n : Nat} (t : Syntax n) :
    substCode x (freeCode replacement) (code t) = code (t.subst
      (Sum.elim (fun y => if y = x then replacement.relabel Sum.inl else .var (.inl y))
        (fun i => .var (.inr i)))) := by
  apply rewriteCode_subst
  intro v
  cases v with
  | inl y =>
    by_cases h : y = x <;> simp [substVariableCode, variableCode, h, cond_eq_ite, Nat.unpair_pair,
      freeCode_relabel, code_var, EncodedSyntax.node]
  | inr i => simp [substVariableCode, variableCode, Nat.unpair_pair, code_var,
      EncodedSyntax.node]

def bindVariableCode (x p : Nat) : Nat :=
  cond (p.unpair.1 == 0)
    (cond (p.unpair.2 == x) (EncodedSyntax.node 0 (Nat.pair 1 0)) (EncodedSyntax.node 0 p))
    (EncodedSyntax.node 0 (Nat.pair 1 (1 + p.unpair.2)))

theorem bindVariableCode_primrec : Primrec₂ bindVariableCode := by
  have hp : Primrec (fun q : Nat × Nat => q.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have ht := Primrec.fst.comp hp
  have hy := Primrec.snd.comp hp
  have hkeep : Primrec (fun q : Nat × Nat => EncodedSyntax.node 0 q.2) :=
    EncodedSyntax.node_primrec.comp (Primrec.const 0) Primrec.snd
  have hbound := EncodedSyntax.node_primrec.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 1) (Primrec.nat_add.comp (Primrec.const 1) hy))
  exact ((Primrec.beq.comp ht (Primrec.const 0)).cond
    ((Primrec.beq.comp hy Primrec.fst).cond
      (Primrec.const (EncodedSyntax.node 0 (Nat.pair 1 0))) hkeep) hbound).to₂

def bindCode (x c : Nat) : Nat := rewriteCode bindVariableCode x c

theorem bindCode_primrec : Primrec₂ bindCode := rewriteCode_primrec bindVariableCode_primrec

theorem bindCode_code (x : Nat) {n : Nat} (t : Syntax n) :
    bindCode x (code t) = code (t.relabel
      (FirstOrder.Language.BoundedFormula.relabelAux (FirstOrderCalculus.bindVariable x) n)) := by
  apply rewriteCode_relabel
  intro v
  cases v with
  | inl y =>
    by_cases h : y = x <;> simp [bindVariableCode, variableCode,
      FirstOrderCalculus.bindVariable, FirstOrder.Language.BoundedFormula.relabelAux,
      h, cond_eq_ite, Nat.unpair_pair, code_var, EncodedSyntax.node]
  | inr i =>
    simp [bindVariableCode, variableCode, FirstOrder.Language.BoundedFormula.relabelAux,
      Nat.unpair_pair, code_var, EncodedSyntax.node, Nat.add_comm]

def substitute (x : Nat) (replacement : FreeSyntax) {n : Nat} (t : Syntax n) : Syntax n :=
  t.subst (Sum.elim
    (fun y => if y = x then replacement.relabel Sum.inl else .var (.inl y))
    (fun i => .var (.inr i)))

theorem substitute_primrec (n : Nat) :
    Primrec (fun p : (Nat × FreeSyntax) × Syntax n => substitute p.1.1 p.1.2 p.2) := by
  apply Primrec.encode_iff.1
  have hp : Primrec (fun p : (Nat × FreeSyntax) × Syntax n => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : (Nat × FreeSyntax) × Syntax n => freeCode p.1.2) :=
    freeCode_primrec.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun p : (Nat × FreeSyntax) × Syntax n => code p.2) :=
    (code_primrec n).comp Primrec.snd
  exact (substCode_primrec.comp ((hp.pair hr).pair ht)).of_eq
    (fun p => substCode_code p.1.1 p.1.2 p.2)

theorem bind_primrec (n : Nat) : Primrec₂ (fun (x : Nat) (t : Syntax n) =>
    t.relabel (FirstOrder.Language.BoundedFormula.relabelAux
      (FirstOrderCalculus.bindVariable x) n)) := by
  apply Primrec.encode_iff.1
  exact (bindCode_primrec.comp Primrec.fst ((code_primrec n).comp Primrec.snd)).of_eq
    (fun p => bindCode_code p.1 p.2)

end Alexander313.Delta.NativeTerm
