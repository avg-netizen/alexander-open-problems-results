import Alexander313.Effective.FormulaOperations
import Alexander313.Alexander.LiteralCoding
import Alexander313.Alexander.BaseLogic

/-!
# Primitive-recursive alphabetic equivalence of the literal source syntax

An explicit stack machine visits source terms and formulas with the actual
list of enclosing binders. Join instructions build the existing de Bruijn
alpha tree. A visit/join cost is at most twice the literal source code, so a
primitive-recursive bounded iteration computes its exact alpha code. Binder
contexts may change between instructions; no fixed-context course-recursion
claim is used for this traversal.
-/

namespace Alexander313

namespace AlphaTerm

def code : AlphaTerm → Nat
  | .free x => EncodedSyntax.node 0 x
  | .bound x => EncodedSyntax.node 1 x
  | .zero => EncodedSyntax.node 2 0
  | .succ t => EncodedSyntax.node 3 t.code
  | .add t u => EncodedSyntax.binary 4 t.code u.code
  | .mul t u => EncodedSyntax.binary 5 t.code u.code

theorem code_injective : Function.Injective code := by
  intro t u h
  induction t generalizing u <;> cases u <;>
    simp_all [code, EncodedSyntax.binary, EncodedSyntax.node, Nat.pair_eq_pair] <;>
    aesop

end AlphaTerm

namespace AlphaFormula

def code : AlphaFormula Nat → Nat
  | .falsum => EncodedSyntax.node 0 0
  | .equal t u => EncodedSyntax.binary 1 t.code u.code
  | .imp φ ψ => EncodedSyntax.binary 2 φ.code ψ.code
  | .conj φ ψ => EncodedSyntax.binary 3 φ.code ψ.code
  | .disj φ ψ => EncodedSyntax.binary 4 φ.code ψ.code
  | .neg φ => EncodedSyntax.node 5 φ.code
  | .all φ => EncodedSyntax.node 6 φ.code
  | .ex φ => EncodedSyntax.node 7 φ.code
  | .know a φ => EncodedSyntax.binary 8 a φ.code

theorem code_injective : Function.Injective code := by
  intro φ ψ h
  induction φ generalizing ψ <;> cases ψ <;>
    simp_all [code, EncodedSyntax.binary, EncodedSyntax.node, Nat.pair_eq_pair,
      AlphaTerm.code_injective.eq_iff] <;> aesop

end AlphaFormula

namespace AlphaMachine

/-- Task kinds: term visit, formula visit, unary join, binary join, owner join. -/
abbrev Task := (Nat × Nat) × List Nat
abbrev State := List Task × List Nat

def task (kind data : Nat) (bound : List Nat) : Task := ((kind, data), bound)

def push (kind data : Nat) (bound : List Nat) (s : State) : State :=
  (task kind data bound :: s.1, s.2)

def value (c : Nat) (s : State) : State := (s.1, c :: s.2)

def peek (s : List Nat) : Nat := s[0]?.getD 0

def variableCode (x : Nat) (bound : List Nat) : Nat :=
  if x ∈ bound then EncodedSyntax.node 1 (bound.idxOf x)
  else EncodedSyntax.node 0 x

private theorem variableCode_primrec : Primrec₂ variableCode := by
  have hi : Primrec (fun p : Nat × List Nat => p.2.idxOf p.1) :=
    Primrec.list_idxOf.comp Primrec.fst Primrec.snd
  have hm : PrimrecPred (fun p : Nat × List Nat => p.1 ∈ p.2) :=
    (Primrec.nat_lt.comp hi (Primrec.list_length.comp Primrec.snd)).of_eq
      (fun p => List.idxOf_lt_length_iff)
  exact (Primrec.ite hm
    (EncodedSyntax.node_primrec.comp (Primrec.const 1) hi)
    (EncodedSyntax.node_primrec.comp (Primrec.const 0) Primrec.fst)).to₂

private theorem push_primrec {A : Type} [Primcodable A]
    {kind data : A → Nat} {bound : A → List Nat} {s : A → State}
    (hk : Primrec kind) (hd : Primrec data) (hb : Primrec bound) (hs : Primrec s) :
    Primrec (fun a => push (kind a) (data a) (bound a) (s a)) :=
  (Primrec.list_cons.comp ((hk.pair hd).pair hb) (Primrec.fst.comp hs)).pair
    (Primrec.snd.comp hs)

private theorem value_primrec {A : Type} [Primcodable A]
    {c : A → Nat} {s : A → State} (hc : Primrec c) (hs : Primrec s) :
    Primrec (fun a => value (c a) (s a)) :=
  (Primrec.fst.comp hs).pair (Primrec.list_cons.comp hc (Primrec.snd.comp hs))

def termStep (c : Nat) (bound : List Nat) (s : State) : State :=
  let tag := (c - 1).unpair.1
  let p := (c - 1).unpair.2
  cond (tag == 0) (value (variableCode p bound) s)
    (cond (tag == 1) (value (EncodedSyntax.node 2 0) s)
      (cond (tag == 2) (push 0 p bound (push 2 3 [] s))
        (cond ((tag == 3) || (tag == 4))
          (push 0 p.unpair.1 bound (push 0 p.unpair.2 bound (push 3 (tag + 1) [] s))) s)))

def formulaStep (c : Nat) (bound : List Nat) (s : State) : State :=
  let tag := (c - 1).unpair.1
  let p := (c - 1).unpair.2
  cond (tag == 0) (value (EncodedSyntax.node 0 0) s)
    (cond (tag == 1)
      (push 0 p.unpair.1 bound (push 0 p.unpair.2 bound (push 3 1 [] s)))
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (push 1 p.unpair.1 bound (push 1 p.unpair.2 bound (push 3 tag [] s)))
        (cond (tag == 5) (push 1 p bound (push 2 5 [] s))
          (cond ((tag == 6) || (tag == 7))
            (push 1 p.unpair.2 (p.unpair.1 :: bound) (push 2 tag [] s))
            (cond (tag == 8) (push 1 p.unpair.2 bound (push 4 p.unpair.1 [] s)) s)))))

private theorem termStep_primrec : Primrec
    (fun p : (Nat × List Nat) × State => termStep p.1.1 p.1.2 p.2) := by
  have hc : Primrec (fun p : (Nat × List Nat) × State => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : (Nat × List Nat) × State => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × List Nat) × State => p.2) := Primrec.snd
  have hn := Primrec.unpair.comp (Primrec.nat_sub.comp hc (Primrec.const 1))
  have ht := Primrec.fst.comp hn
  have hp := Primrec.snd.comp hn
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (tag : Nat) := Primrec.beq.comp ht (Primrec.const tag)
  have hv := value_primrec (variableCode_primrec.comp hp hb) hs
  have hz := value_primrec (Primrec.const (EncodedSyntax.node 2 0)) hs
  have hu := push_primrec (Primrec.const 0) hp hb
    (push_primrec (Primrec.const 2) (Primrec.const 3) (Primrec.const []) hs)
  have hbin := push_primrec (Primrec.const 0) hl hb
    (push_primrec (Primrec.const 0) hr hb
      (push_primrec (Primrec.const 3) (Primrec.succ.comp ht) (Primrec.const []) hs))
  exact (test 0).cond hv ((test 1).cond hz
    ((test 2).cond hu ((Primrec.or.comp (test 3) (test 4)).cond hbin hs)))

private theorem formulaStep_primrec : Primrec
    (fun p : (Nat × List Nat) × State => formulaStep p.1.1 p.1.2 p.2) := by
  have hc : Primrec (fun p : (Nat × List Nat) × State => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : (Nat × List Nat) × State => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × List Nat) × State => p.2) := Primrec.snd
  have hn := Primrec.unpair.comp (Primrec.nat_sub.comp hc (Primrec.const 1))
  have ht := Primrec.fst.comp hn
  have hp := Primrec.snd.comp hn
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (tag : Nat) := Primrec.beq.comp ht (Primrec.const tag)
  have hf := value_primrec (Primrec.const (EncodedSyntax.node 0 0)) hs
  have heq := push_primrec (Primrec.const 0) hl hb
    (push_primrec (Primrec.const 0) hr hb
      (push_primrec (Primrec.const 3) (Primrec.const 1) (Primrec.const []) hs))
  have hbin := push_primrec (Primrec.const 1) hl hb
    (push_primrec (Primrec.const 1) hr hb
      (push_primrec (Primrec.const 3) ht (Primrec.const []) hs))
  have hneg := push_primrec (Primrec.const 1) hp hb
    (push_primrec (Primrec.const 2) (Primrec.const 5) (Primrec.const []) hs)
  have hquant := push_primrec (Primrec.const 1) hr (Primrec.list_cons.comp hl hb)
    (push_primrec (Primrec.const 2) ht (Primrec.const []) hs)
  have hknow := push_primrec (Primrec.const 1) hr hb
    (push_primrec (Primrec.const 4) hl (Primrec.const []) hs)
  exact (test 0).cond hf ((test 1).cond heq
    ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond hbin
      ((test 5).cond hneg ((Primrec.or.comp (test 6) (test 7)).cond hquant
        ((test 8).cond hknow hs)))))

def advance (w : Task) (s : State) : State :=
  cond (w.1.1 == 0) (termStep w.1.2 w.2 s)
    (cond (w.1.1 == 1) (formulaStep w.1.2 w.2 s)
      (cond (w.1.1 == 2) (s.1, EncodedSyntax.node w.1.2 (peek s.2) :: s.2.tail)
        (cond (w.1.1 == 3)
          (s.1, EncodedSyntax.binary w.1.2 (peek s.2.tail) (peek s.2) :: s.2.tail.tail)
          (cond (w.1.1 == 4)
            (s.1, EncodedSyntax.binary 8 w.1.2 (peek s.2) :: s.2.tail) s))))

private theorem advance_primrec : Primrec₂ advance := by
  have hw : Primrec (fun p : Task × State => p.1) := Primrec.fst
  have hk := Primrec.fst.comp (Primrec.fst.comp hw)
  have hc := Primrec.snd.comp (Primrec.fst.comp hw)
  have hb := Primrec.snd.comp hw
  have hs : Primrec (fun p : Task × State => p.2) := Primrec.snd
  have ht := Primrec.fst.comp hs
  have hv := Primrec.snd.comp hs
  have htail := Primrec.list_tail.comp hv
  have htail₂ := Primrec.list_tail.comp htail
  have hpeek : Primrec peek :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0))
      (Primrec.const 0)
  have hfirst := hpeek.comp hv
  have hsecond := hpeek.comp htail
  have test (kind : Nat) := Primrec.beq.comp hk (Primrec.const kind)
  have hterm := termStep_primrec.comp ((hc.pair hb).pair hs)
  have hform := formulaStep_primrec.comp ((hc.pair hb).pair hs)
  have hunary := ht.pair (Primrec.list_cons.comp
    (EncodedSyntax.node_primrec.comp hc hfirst) htail)
  have hbinary := ht.pair (Primrec.list_cons.comp
    (EncodedSyntax.node_primrec.comp hc (Primrec₂.natPair.comp hsecond hfirst)) htail₂)
  have howner := ht.pair (Primrec.list_cons.comp
    ((EncodedSyntax.binary_primrec 8).comp hc hfirst) htail)
  exact ((test 0).cond hterm ((test 1).cond hform
    ((test 2).cond hunary ((test 3).cond hbinary ((test 4).cond howner hs))))).to₂

def step (s : State) : State :=
  s.1.casesOn s (fun w rest => advance w (rest, s.2))

theorem step_primrec : Primrec step :=
  Primrec.list_casesOn Primrec.fst Primrec.id
    (advance_primrec.comp (Primrec.fst.comp Primrec.snd)
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst))).to₂

def run (n : Nat) (s : State) : State := step^[n] s

theorem run_primrec : Primrec₂ run :=
  (Primrec.nat_iterate Primrec.fst Primrec.snd
    (step_primrec.comp₂ Primrec₂.right)).to₂

@[simp] theorem run_zero (s : State) : run 0 s = s := rfl
@[simp] theorem run_one (s : State) : run 1 s = step s := rfl

theorem run_add (n m : Nat) (s : State) : run (n + m) s = run m (run n s) := by
  change step^[n + m] s = step^[m] (step^[n] s)
  rw [Nat.add_comm n m, Function.iterate_add_apply]

@[simp] theorem run_empty (n : Nat) (values : List Nat) :
    run n ([], values) = ([], values) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [run, Function.iterate_succ_apply, step] using ih

@[simp] theorem step_term_var (x : Nat) (b : List Nat) (todo : List Task) (v : List Nat) :
    step (task 0 (Term.var x).code b :: todo, v) = value (variableCode x b) (todo, v) := by
  simp [step, advance, task, termStep, Term.code, Nat.unpair_pair, value]

@[simp] theorem step_term_zero (b : List Nat) (todo : List Task) (v : List Nat) :
    step (task 0 Term.zero.code b :: todo, v) = value (EncodedSyntax.node 2 0) (todo, v) := by
  simp [step, advance, task, termStep, Term.code, Nat.unpair_pair, value]

@[simp] theorem step_term_succ (t : Term) (b : List Nat) (todo : List Task) (v : List Nat) :
    step (task 0 (Term.succ t).code b :: todo, v) =
      (task 0 t.code b :: task 2 3 [] :: todo, v) := by
  simp [step, advance, task, termStep, Term.code, Nat.unpair_pair, push]

@[simp] theorem step_term_add (t u : Term) (b : List Nat) (todo : List Task) (v : List Nat) :
    step (task 0 (Term.add t u).code b :: todo, v) =
      (task 0 t.code b :: task 0 u.code b :: task 3 4 [] :: todo, v) := by
  simp [step, advance, task, termStep, Term.code, Nat.unpair_pair, push]

@[simp] theorem step_term_mul (t u : Term) (b : List Nat) (todo : List Task) (v : List Nat) :
    step (task 0 (Term.mul t u).code b :: todo, v) =
      (task 0 t.code b :: task 0 u.code b :: task 3 5 [] :: todo, v) := by
  simp [step, advance, task, termStep, Term.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_falsum (b : List Nat) (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.falsum : Formula Nat).code id) b :: todo, v) =
      value (EncodedSyntax.node 0 0) (todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, value]

@[simp] theorem step_formula_equal (t u : Term) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.equal t u : Formula Nat).code id) b :: todo, v) =
      (task 0 t.code b :: task 0 u.code b :: task 3 1 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_imp (φ ψ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.imp φ ψ).code id) b :: todo, v) =
      (task 1 (φ.code id) b :: task 1 (ψ.code id) b :: task 3 2 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_conj (φ ψ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.conj φ ψ).code id) b :: todo, v) =
      (task 1 (φ.code id) b :: task 1 (ψ.code id) b :: task 3 3 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_disj (φ ψ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.disj φ ψ).code id) b :: todo, v) =
      (task 1 (φ.code id) b :: task 1 (ψ.code id) b :: task 3 4 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_neg (φ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.neg φ).code id) b :: todo, v) =
      (task 1 (φ.code id) b :: task 2 5 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_all (x : Nat) (φ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.all x φ).code id) b :: todo, v) =
      (task 1 (φ.code id) (x :: b) :: task 2 6 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_ex (x : Nat) (φ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.ex x φ).code id) b :: todo, v) =
      (task 1 (φ.code id) (x :: b) :: task 2 7 [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_formula_know (a : Nat) (φ : Formula Nat) (b : List Nat)
    (todo : List Task) (v : List Nat) :
    step (task 1 ((Formula.know a φ).code id) b :: todo, v) =
      (task 1 (φ.code id) b :: task 4 a [] :: todo, v) := by
  simp [step, advance, task, formulaStep, Formula.code, Nat.unpair_pair, push]

@[simp] theorem step_unary (tag c : Nat) (todo : List Task) (v : List Nat) :
    step (task 2 tag [] :: todo, c :: v) = (todo, EncodedSyntax.node tag c :: v) := rfl

@[simp] theorem step_binary (tag c d : Nat) (todo : List Task) (v : List Nat) :
    step (task 3 tag [] :: todo, d :: c :: v) =
      (todo, EncodedSyntax.binary tag c d :: v) := rfl

@[simp] theorem step_owner (a c : Nat) (todo : List Task) (v : List Nat) :
    step (task 4 a [] :: todo, c :: v) =
      (todo, EncodedSyntax.binary 8 a c :: v) := rfl

end AlphaMachine

namespace Term

def alphaCost : Term → Nat
  | .var _ => 1
  | .zero => 1
  | .succ t => t.alphaCost + 2
  | .add t u => t.alphaCost + u.alphaCost + 2
  | .mul t u => t.alphaCost + u.alphaCost + 2

theorem alphaCost_le_twice_code (t : Term) : t.alphaCost ≤ 2 * t.code := by
  induction t with
  | var x =>
    simp only [alphaCost, code]
    omega
  | zero => simp [alphaCost, code, Nat.pair]
  | succ t ih =>
    have h := Nat.right_le_pair 2 t.code
    simp only [alphaCost, code]
    omega
  | add t u iht ihu =>
    have h₁ := Nat.add_le_pair t.code u.code
    have h₂ := Nat.right_le_pair 3 (Nat.pair t.code u.code)
    simp only [alphaCost, code]
    omega
  | mul t u iht ihu =>
    have h₁ := Nat.add_le_pair t.code u.code
    have h₂ := Nat.right_le_pair 4 (Nat.pair t.code u.code)
    simp only [alphaCost, code]
    omega

theorem alpha_run (t : Term) (bound : List Nat)
    (todo : List AlphaMachine.Task) (values : List Nat) :
    AlphaMachine.run t.alphaCost
      (AlphaMachine.task 0 t.code bound :: todo, values) =
      (todo, (t.alpha bound).code :: values) := by
  induction t generalizing bound todo values with
  | var x =>
    by_cases hx : x ∈ bound <;>
      simp [alphaCost, AlphaMachine.run_one, AlphaMachine.step_term_var,
        AlphaMachine.value, alpha, AlphaTerm.code, AlphaMachine.variableCode, hx]
  | zero =>
    simp [alphaCost, AlphaMachine.run_one, AlphaMachine.step_term_zero,
      AlphaMachine.value, alpha, AlphaTerm.code]
  | succ t ih =>
    have hc : t.alphaCost + 2 = 1 + t.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_term_succ]
    rw [ih]
    rfl
  | add t u iht ihu =>
    have hc : t.alphaCost + u.alphaCost + 2 = 1 + t.alphaCost + u.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_term_add]
    rw [iht, ihu]
    rfl
  | mul t u iht ihu =>
    have hc : t.alphaCost + u.alphaCost + 2 = 1 + t.alphaCost + u.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_term_mul]
    rw [iht, ihu]
    rfl

end Term

namespace Formula

def alphaCost : Formula Nat → Nat
  | .falsum => 1
  | .equal t u => t.alphaCost + u.alphaCost + 2
  | .imp φ ψ => φ.alphaCost + ψ.alphaCost + 2
  | .conj φ ψ => φ.alphaCost + ψ.alphaCost + 2
  | .disj φ ψ => φ.alphaCost + ψ.alphaCost + 2
  | .neg φ => φ.alphaCost + 2
  | .all _ φ => φ.alphaCost + 2
  | .ex _ φ => φ.alphaCost + 2
  | .know _ φ => φ.alphaCost + 2

theorem alphaCost_le_twice_code (φ : Formula Nat) : φ.alphaCost ≤ 2 * φ.code id := by
  induction φ with
  | falsum => simp [alphaCost, code, Nat.pair]
  | equal t u =>
    have iht := t.alphaCost_le_twice_code
    have ihu := u.alphaCost_le_twice_code
    have h₁ := Nat.add_le_pair t.code u.code
    have h₂ := Nat.right_le_pair 1 (Nat.pair t.code u.code)
    simp only [alphaCost, code]
    omega
  | imp φ ψ ihφ ihψ =>
    have h₁ := Nat.add_le_pair (φ.code id) (ψ.code id)
    have h₂ := Nat.right_le_pair 2 (Nat.pair (φ.code id) (ψ.code id))
    simp only [alphaCost, code]
    omega
  | conj φ ψ ihφ ihψ =>
    have h₁ := Nat.add_le_pair (φ.code id) (ψ.code id)
    have h₂ := Nat.right_le_pair 3 (Nat.pair (φ.code id) (ψ.code id))
    simp only [alphaCost, code]
    omega
  | disj φ ψ ihφ ihψ =>
    have h₁ := Nat.add_le_pair (φ.code id) (ψ.code id)
    have h₂ := Nat.right_le_pair 4 (Nat.pair (φ.code id) (ψ.code id))
    simp only [alphaCost, code]
    omega
  | neg φ ih =>
    have h := Nat.right_le_pair 5 (φ.code id)
    simp only [alphaCost, code]
    omega
  | all x φ ih =>
    have h₁ := Nat.right_le_pair x (φ.code id)
    have h₂ := Nat.right_le_pair 6 (Nat.pair x (φ.code id))
    simp only [alphaCost, code]
    omega
  | ex x φ ih =>
    have h₁ := Nat.right_le_pair x (φ.code id)
    have h₂ := Nat.right_le_pair 7 (Nat.pair x (φ.code id))
    simp only [alphaCost, code]
    omega
  | know a φ ih =>
    have h₁ := Nat.right_le_pair a (φ.code id)
    have h₂ := Nat.right_le_pair 8 (Nat.pair a (φ.code id))
    simp only [alphaCost, code, id_eq]
    omega

theorem alpha_run (φ : Formula Nat) (bound : List Nat)
    (todo : List AlphaMachine.Task) (values : List Nat) :
    AlphaMachine.run φ.alphaCost
      (AlphaMachine.task 1 (φ.code id) bound :: todo, values) =
      (todo, (φ.alpha bound).code :: values) := by
  induction φ generalizing bound todo values with
  | falsum =>
    simp [alphaCost, AlphaMachine.run_one, AlphaMachine.step_formula_falsum,
      AlphaMachine.value, alpha, AlphaFormula.code]
  | equal t u =>
    have hc : t.alphaCost + u.alphaCost + 2 = 1 + t.alphaCost + u.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_formula_equal]
    rw [t.alpha_run, u.alpha_run]
    rfl
  | imp φ ψ ihφ ihψ | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    have hc : φ.alphaCost + ψ.alphaCost + 2 = 1 + φ.alphaCost + ψ.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_formula_imp, AlphaMachine.step_formula_conj,
      AlphaMachine.step_formula_disj]
    rw [ihφ, ihψ]
    rfl
  | neg φ ih =>
    have hc : φ.alphaCost + 2 = 1 + φ.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_formula_neg]
    rw [ih]
    rfl
  | all x φ ih | ex x φ ih =>
    have hc : φ.alphaCost + 2 = 1 + φ.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_formula_all, AlphaMachine.step_formula_ex]
    rw [ih]
    rfl
  | know a φ ih =>
    have hc : φ.alphaCost + 2 = 1 + φ.alphaCost + 1 := by omega
    simp only [alphaCost, hc, AlphaMachine.run_add, AlphaMachine.run_one,
      AlphaMachine.step_formula_know]
    rw [ih]
    rfl

end Formula

namespace AlphaMachine

def code (kind c : Nat) (bound : List Nat) : Nat :=
  peek (run (2 * c) ([task kind c bound], [])).2

theorem code_primrec (kind : Nat) : Primrec₂ (code kind) := by
  have hc : Primrec (fun p : Nat × List Nat => p.1) := Primrec.fst
  have hb : Primrec (fun p : Nat × List Nat => p.2) := Primrec.snd
  have ht := ((Primrec.const kind).pair hc).pair hb
  have hs : Primrec (fun p : Nat × List Nat => ([task kind p.1 p.2], ([] : List Nat))) :=
    (Primrec.list_cons.comp ht (Primrec.const [])).pair (Primrec.const [])
  exact (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (Primrec.snd.comp (run_primrec.comp (Primrec.nat_mul.comp (Primrec.const 2) hc) hs))
      (Primrec.const 0)) (Primrec.const 0)).to₂

@[simp] theorem term_code (t : Term) (bound : List Nat) :
    code 0 t.code bound = (t.alpha bound).code := by
  have h := t.alphaCost_le_twice_code
  have heq : 2 * t.code = t.alphaCost + (2 * t.code - t.alphaCost) := by omega
  rw [code, heq, run_add, t.alpha_run, run_empty]
  rfl

@[simp] theorem formula_code (φ : Formula Nat) (bound : List Nat) :
    code 1 (φ.code id) bound = (φ.alpha bound).code := by
  have h := φ.alphaCost_le_twice_code
  have heq : 2 * φ.code id = φ.alphaCost + (2 * φ.code id - φ.alphaCost) := by omega
  rw [code, heq, run_add, φ.alpha_run, run_empty]
  rfl

end AlphaMachine

namespace Formula

instance decidableAlphaEquivalent (φ ψ : Formula Nat) : Decidable (φ.AlphaEquivalent ψ) :=
  inferInstanceAs (Decidable (φ.alpha [] = ψ.alpha []))

def alphabeticCode (c d : Nat) : Bool :=
  AlphaMachine.code 1 c [] == AlphaMachine.code 1 d []

theorem alphabeticCode_primrec : Primrec₂ alphabeticCode :=
  (Primrec.beq.comp ((AlphaMachine.code_primrec 1).comp Primrec.fst (Primrec.const []))
    ((AlphaMachine.code_primrec 1).comp Primrec.snd (Primrec.const []))).to₂

@[simp] theorem alphabeticCode_code (φ ψ : Formula Nat) :
    alphabeticCode (φ.code id) (ψ.code id) = decide (φ.AlphaEquivalent ψ) := by
  apply Bool.eq_iff_iff.mpr
  simp only [alphabeticCode, AlphaMachine.formula_code, beq_iff_eq, decide_eq_true_eq,
    AlphaFormula.code_injective.eq_iff, AlphaEquivalent]

theorem alphaEquivalent_primrec : PrimrecRel (AlphaEquivalent (Owner := Nat)) := by
  apply Primrec₂.primrecRel
  simpa only [alphabeticCode_code] using (alphabeticCode_primrec.comp
    (Formula.code_primrec.comp Primrec.fst) (Formula.code_primrec.comp Primrec.snd)).to₂

end Formula
end Alexander313
