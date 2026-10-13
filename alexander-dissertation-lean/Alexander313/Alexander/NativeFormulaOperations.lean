import Alexander313.Alexander.NativeTermOperations

/-!
# Effective native first-order formula substitution and binding

The numerical rewriter changes native term arguments and bound-context headers.
It preserves relation-symbol labels, including their opaque Alexander formulas.
Thus these are operations of the native first-order Hilbert calculus, rather
than new substitution rules for the modal source logic.
-/

namespace Alexander313.Delta

namespace NativeTuple

variable {A : Type} [Primcodable A]

def rewriteCode (term : A → Nat → Nat) (a : A) (c : Nat) : Nat :=
  Encodable.encode (((Encodable.decode₂ (List Nat) c).getD []).map (term a))

theorem rewriteCode_primrec {term : A → Nat → Nat} (ht : Primrec₂ term) :
    Primrec₂ (rewriteCode term) := by
  have hd : Primrec (fun p : A × Nat =>
      (Encodable.decode₂ (List Nat) p.2).getD []) :=
    Primrec.option_getD.comp (Primrec.decode₂.comp Primrec.snd) (Primrec.const [])
  have hm := Primrec.list_map hd
    (ht.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.encode.comp hm).to₂

theorem rewriteCode_code {term : A → Nat → Nat} (a : A) {n m l : Nat}
    (f : NativeTerm.Syntax n → NativeTerm.Syntax m)
    (ht : ∀ t, term a (NativeTerm.code t) = NativeTerm.code (f t)) (ts : Fin l → NativeTerm.Syntax n) :
    rewriteCode term a (code ts) = code (fun i => f (ts i)) := by
  simp only [rewriteCode, code, Encodable.decode₂_encode, Option.getD_some]
  congr 1
  simp only [List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => ht (ts i)))

end NativeTuple

namespace NativeFormula

variable {A : Type} [Primcodable A]

def rewriteCode (term : A → Nat → Nat) (d : Nat) (a : A) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let n := k.unpair.1
    let b := k.unpair.2
    let tag := (b - 1).unpair.1
    let p := (b - 1).unpair.2
    let payload := cond (tag == 0) 0
      (cond (tag == 1) (Nat.pair (term a p.unpair.1) (term a p.unpair.2))
        (cond (tag == 2) (Nat.pair p.unpair.1 (NativeTuple.rewriteCode term a p.unpair.2))
          (cond (tag == 3) (Nat.pair (rewriteCode term d a p.unpair.1)
            (rewriteCode term d a p.unpair.2)) (rewriteCode term d a p))))
    Nat.pair (d + n) (Nat.pair tag payload + 1) + 1
termination_by c => c
decreasing_by
  all_goals
    have hb := Nat.unpair_right_le k
    have hk := Nat.sub_le k.unpair.2 1
    have hp := Nat.unpair_right_le (k.unpair.2 - 1)
    have hl := Nat.unpair_left_le (k.unpair.2 - 1).unpair.2
    have hr := Nat.unpair_right_le (k.unpair.2 - 1).unpair.2
    omega

private def rewriteStep (term : A → Nat → Nat) (d : Nat) (a : A) (h : List Nat) : Nat :=
  let k := h.length - 1
  let n := k.unpair.1
  let b := k.unpair.2
  let tag := (b - 1).unpair.1
  let p := (b - 1).unpair.2
  let payload := cond (tag == 0) 0
    (cond (tag == 1) (Nat.pair (term a p.unpair.1) (term a p.unpair.2))
      (cond (tag == 2) (Nat.pair p.unpair.1 (NativeTuple.rewriteCode term a p.unpair.2))
        (cond (tag == 3) (Nat.pair (h[p.unpair.1]?.getD 0)
          (h[p.unpair.2]?.getD 0)) (h[p]?.getD 0))))
  cond (h.length == 0) 0 (Nat.pair (d + n) (Nat.pair tag payload + 1) + 1)

private theorem rewriteStep_primrec (d : Nat) {term : A → Nat → Nat}
    (ht : Primrec₂ term) : Primrec₂ (rewriteStep term d) := by
  have hn := Primrec.list_length.comp (Primrec.snd : Primrec (Prod.snd : A × List Nat → _))
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hctx := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hb := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hnode := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have htag := Primrec.fst.comp hnode
  have hp := Primrec.snd.comp hnode
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (t : Nat) := Primrec.beq.comp htag (Primrec.const t)
  have get (f : A × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : A × List Nat => p.2[f p]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const 0)
  have hpl := (test 0).cond (Primrec.const 0)
    ((test 1).cond (Primrec₂.natPair.comp (ht.comp Primrec.fst hl) (ht.comp Primrec.fst hr))
      ((test 2).cond (Primrec₂.natPair.comp hl
        ((NativeTuple.rewriteCode_primrec ht).comp Primrec.fst hr))
        ((test 3).cond (Primrec₂.natPair.comp (get _ hl) (get _ hr)) (get _ hp))))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    (Primrec.succ.comp (Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.const d) hctx)
      (Primrec.succ.comp (Primrec₂.natPair.comp htag hpl))))).to₂

theorem rewriteCode_primrec (d : Nat) {term : A → Nat → Nat} (ht : Primrec₂ term) :
    Primrec₂ (rewriteCode term d) := by
  have hg := Primrec.option_some.comp₂ (rewriteStep_primrec d ht)
  exact Primrec.nat_strong_rec (rewriteCode term d) hg (by
    intro a c
    cases c with
    | zero => simp [rewriteStep, rewriteCode]
    | succ k =>
      have hb := Nat.unpair_right_le k
      have hk := Nat.sub_le k.unpair.2 1
      have hp₀ := Nat.unpair_right_le (k.unpair.2 - 1)
      have hp : (k.unpair.2 - 1).unpair.2 < k + 1 := by omega
      have hl := lt_of_le_of_lt (Nat.unpair_left_le (k.unpair.2 - 1).unpair.2) hp
      have hr := lt_of_le_of_lt (Nat.unpair_right_le (k.unpair.2 - 1).unpair.2) hp
      simp [rewriteStep, rewriteCode, hp, hl, hr])

theorem rewriteCode_subst {term : A → Nat → Nat} (a : A)
    (f : Nat → NativeTerm.FreeSyntax)
    (ht : ∀ {n} (t : NativeTerm.Syntax n), term a (NativeTerm.code t) =
      NativeTerm.code (t.subst (Sum.elim (fun x => (f x).relabel Sum.inl)
        (fun i => .var (.inr i))))) {n : Nat} (φ : Syntax n) :
    rewriteCode term 0 a (code φ) = code (φ.subst f) := by
  induction φ with
  | falsum => simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.mapTermRel]
  | equal t u =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, Function.comp_def, ht]
  | rel r ts =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, Function.comp_def,
      NativeTuple.rewriteCode_code a _ (fun t => ht t)]
  | imp φ ψ ihφ ihψ =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, ihφ, ihψ]
  | all φ ih =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, ih]

theorem rewriteCode_relabel {term : A → Nat → Nat} (d : Nat) (a : A)
    (f : Nat → Nat ⊕ Fin d)
    (ht : ∀ {n} (t : NativeTerm.Syntax n), term a (NativeTerm.code t) = NativeTerm.code
      (t.relabel (FirstOrder.Language.BoundedFormula.relabelAux f n)))
    {n : Nat} (φ : Syntax n) :
    rewriteCode term d a (code φ) = code (φ.relabel f) := by
  induction φ with
  | falsum => simp [rewriteCode, code, Nat.unpair_pair]
  | equal t u =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, ht]
  | rel r ts =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      NativeTuple.rewriteCode_code a _ (fun t => ht t)]
  | imp φ ψ ihφ ihψ =>
    simp [rewriteCode, code, Nat.unpair_pair,
      FirstOrder.Language.BoundedFormula.relabel_imp, ihφ, ihψ]
  | all φ ih =>
    rw [FirstOrder.Language.BoundedFormula.relabel_all]
    simp [rewriteCode, code, Nat.unpair_pair,
      ih, Nat.add_assoc]

def substCode (x replacement c : Nat) : Nat :=
  rewriteCode (NativeTerm.rewriteCode NativeTerm.substVariableCode) 0 (x, replacement) c

theorem substCode_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => substCode p.1.1 p.1.2 p.2) :=
  rewriteCode_primrec 0 (NativeTerm.rewriteCode_primrec NativeTerm.substVariableCode_primrec)

@[simp] theorem substCode_code (x : Nat) (t : NativeTerm.FreeSyntax)
    {n : Nat} (φ : Syntax n) :
    substCode x (NativeTerm.freeCode t) (code φ) =
      code (φ.subst (fun y => if y = x then t else .var y)) := by
  apply rewriteCode_subst
  intro n u
  simpa only [NativeTerm.substCode, FirstOrder.Language.Term.relabel, apply_ite] using
    NativeTerm.substCode_code x t u

theorem substitute_primrec (n : Nat) : Primrec
    (fun p : (Nat × NativeTerm.FreeSyntax) × Syntax n =>
      p.2.subst (fun y => if y = p.1.1 then p.1.2 else .var y)) := by
  apply Primrec.encode_iff.1
  have hx : Primrec (fun p : (Nat × NativeTerm.FreeSyntax) × Syntax n => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : (Nat × NativeTerm.FreeSyntax) × Syntax n => NativeTerm.freeCode p.1.2) :=
    NativeTerm.freeCode_primrec.comp (Primrec.snd.comp Primrec.fst)
  have hφ : Primrec (fun p : (Nat × NativeTerm.FreeSyntax) × Syntax n => code p.2) :=
    (code_primrec n).comp Primrec.snd
  exact (substCode_primrec.comp ((hx.pair ht).pair hφ)).of_eq
    (fun p => substCode_code p.1.1 p.1.2 p.2)

theorem substituteVariable_primrec : Primrec
    (fun p : (Nat × NativeTerm.FreeSyntax) × Syntax 0 =>
      FirstOrderCalculus.substituteVariable p.1.1 p.1.2 p.2) :=
  substitute_primrec 0

def bindCode (x c : Nat) : Nat := rewriteCode NativeTerm.bindCode 1 x c

theorem bindCode_primrec : Primrec₂ bindCode :=
  rewriteCode_primrec 1 NativeTerm.bindCode_primrec

@[simp] theorem bindCode_code (x : Nat) {n : Nat} (φ : Syntax n) :
    bindCode x (code φ) = code (φ.relabel (FirstOrderCalculus.bindVariable x)) :=
  rewriteCode_relabel 1 x (FirstOrderCalculus.bindVariable x)
    (fun t => NativeTerm.bindCode_code x t) φ

theorem bind_primrec (n : Nat) : Primrec₂ (fun (x : Nat) (φ : Syntax n) =>
    φ.relabel (FirstOrderCalculus.bindVariable x)) := by
  apply Primrec.encode_iff.1
  exact (bindCode_primrec.comp Primrec.fst ((code_primrec n).comp Primrec.snd)).of_eq
    (fun p => bindCode_code p.1 p.2)

theorem allVariable_primrec : Primrec₂ (fun (x : Nat) (φ : Syntax 0) =>
    FirstOrderCalculus.allVariable x φ) :=
  (all_primrec 0).comp₂ (bind_primrec 0)

private theorem rewriteStep_uniform_primrec {term : A → Nat → Nat} (ht : Primrec₂ term) :
    Primrec₂ (fun (a : Nat × A) (h : List Nat) => rewriteStep term a.1 a.2 h) := by
  have hn := Primrec.list_length.comp
    (Primrec.snd : Primrec (Prod.snd : (Nat × A) × List Nat → _))
  have hd : Primrec (fun p : (Nat × A) × List Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Nat × A) × List Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hctx := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hb := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hnode := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have htag := Primrec.fst.comp hnode
  have hp := Primrec.snd.comp hnode
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (t : Nat) := Primrec.beq.comp htag (Primrec.const t)
  have get (f : (Nat × A) × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : (Nat × A) × List Nat => p.2[f p]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const 0)
  have hpl := (test 0).cond (Primrec.const 0)
    ((test 1).cond (Primrec₂.natPair.comp (ht.comp ha hl) (ht.comp ha hr))
      ((test 2).cond (Primrec₂.natPair.comp hl
        ((NativeTuple.rewriteCode_primrec ht).comp ha hr))
        ((test 3).cond (Primrec₂.natPair.comp (get _ hl) (get _ hr)) (get _ hp))))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.nat_add.comp hd hctx)
      (Primrec.succ.comp (Primrec₂.natPair.comp htag hpl))))).to₂

theorem rewriteCode_uniform_primrec {term : A → Nat → Nat} (ht : Primrec₂ term) :
    Primrec (fun p : (Nat × A) × Nat => rewriteCode term p.1.1 p.1.2 p.2) := by
  have hg := Primrec.option_some.comp₂ (rewriteStep_uniform_primrec ht)
  exact Primrec.nat_strong_rec
    (fun (a : Nat × A) c => rewriteCode term a.1 a.2 c) hg (by
    intro a c
    cases c with
    | zero => simp [rewriteStep, rewriteCode]
    | succ k =>
      have hb := Nat.unpair_right_le k
      have hk := Nat.sub_le k.unpair.2 1
      have hp₀ := Nat.unpair_right_le (k.unpair.2 - 1)
      have hp : (k.unpair.2 - 1).unpair.2 < k + 1 := by omega
      have hl := lt_of_le_of_lt (Nat.unpair_left_le (k.unpair.2 - 1).unpair.2) hp
      have hr := lt_of_le_of_lt (Nat.unpair_right_le (k.unpair.2 - 1).unpair.2) hp
      simp [rewriteStep, rewriteCode, hp, hl, hr])

end NativeFormula

end Alexander313.Delta
