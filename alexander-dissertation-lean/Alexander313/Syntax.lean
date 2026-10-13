import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Aesop
import Lean.Elab.Tactic.Omega

/-!
# The arithmetic/modal syntax

Variables are named by natural numbers. Numerals are literal iterated
successors, as in Alexander Definition 1.2.10. There is no primitive
halting predicate in this language. Its arithmetic representation is a
separate obligation in `ArithmeticCoding`.
-/

namespace Alexander313

abbrev Assignment := Nat → Nat
abbrev NumericalSubstitution := Nat → Option Nat

def NumericalSubstitution.remove (σ : NumericalSubstitution) (x : Nat) :
    NumericalSubstitution := fun y => if y = x then none else σ y

def NumericalSubstitution.compose (σ τ : NumericalSubstitution) :
    NumericalSubstitution := fun x => (σ x).orElse (fun _ => τ x)

def NumericalSubstitution.override (σ : NumericalSubstitution) (s : Assignment) :
    Assignment := fun x => (σ x).getD (s x)

@[simp] theorem NumericalSubstitution.remove_none (x : Nat) :
    NumericalSubstitution.remove (fun _ => none) x = fun _ => none := by
  funext y
  simp [remove]

@[simp] theorem NumericalSubstitution.remove_update_self
    (σ : NumericalSubstitution) (x : Nat) (v : Option Nat) :
    NumericalSubstitution.remove (Function.update σ x v) x = σ.remove x := by
  funext y
  by_cases h : y = x <;> simp [remove, h]

theorem NumericalSubstitution.remove_update_of_ne
    (σ : NumericalSubstitution) (x z : Nat) (v : Option Nat) (hxz : x ≠ z) :
    NumericalSubstitution.remove (Function.update σ x v) z =
      Function.update (σ.remove z) x v := by
  funext y
  by_cases hyx : y = x
  · subst y
    simp [remove, hxz]
  · by_cases hyz : y = z
    · subst y
      rw [Function.update_of_ne hxz.symm]
      simp [remove]
    · simp [remove, hyx, hyz]

@[simp] theorem NumericalSubstitution.remove_compose
    (σ τ : NumericalSubstitution) (x : Nat) :
    (σ.compose τ).remove x = (σ.remove x).compose (τ.remove x) := by
  funext y
  by_cases h : y = x <;> simp [remove, compose, h]

@[simp] theorem NumericalSubstitution.compose_total
    (σ : NumericalSubstitution) (s : Assignment) :
    σ.compose (fun x => some (s x)) = fun x => some (σ.override s x) := by
  funext x
  cases h : σ x <;> simp [compose, override, h]

@[simp] theorem NumericalSubstitution.override_total (s t : Assignment) :
    NumericalSubstitution.override (fun x => some (s x)) t = s := by
  funext x
  simp [override]

theorem NumericalSubstitution.override_update
    (σ : NumericalSubstitution) (s : Assignment) (x n : Nat) :
    (σ.remove x).override (Function.update s x n) =
      Function.update (σ.override s) x n := by
  funext y
  by_cases h : y = x
  · subst y
    simp [remove, override]
  · simp [remove, override, h]

inductive Term where
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

def numeral : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (numeral n)

def eval (s : Assignment) : Term → Nat
  | .var x => s x
  | .zero => 0
  | .succ t => eval s t + 1
  | .add t u => eval s t + eval s u
  | .mul t u => eval s t * eval s u

def freeVars : Term → Finset Nat
  | .var x => {x}
  | .zero => ∅
  | .succ t => t.freeVars
  | .add t u => t.freeVars ∪ u.freeVars
  | .mul t u => t.freeVars ∪ u.freeVars

def subst (σ : NumericalSubstitution) : Term → Term
  | .var x => match σ x with
    | none => .var x
    | some n => numeral n
  | .zero => .zero
  | .succ t => .succ (t.subst σ)
  | .add t u => .add (t.subst σ) (u.subst σ)
  | .mul t u => .mul (t.subst σ) (u.subst σ)

/-- Syntactic term replacement. Modal semantic laws for arbitrary terms
    are not asserted; the PA successor instance is treated separately. -/
def substTerm (x : Nat) (replacement : Term) : Term → Term
  | .var y => if y = x then replacement else .var y
  | .zero => .zero
  | .succ t => .succ (substTerm x replacement t)
  | .add t u => .add (substTerm x replacement t) (substTerm x replacement u)
  | .mul t u => .mul (substTerm x replacement t) (substTerm x replacement u)

@[simp] theorem subst_none (t : Term) : t.subst (fun _ => none) = t := by
  induction t <;> simp_all [subst]

@[simp] theorem eval_numeral (s : Assignment) (n : Nat) :
    (numeral n).eval s = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, eval, ih]

@[simp] theorem freeVars_numeral (n : Nat) : (numeral n).freeVars = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [numeral, freeVars] using ih

@[simp] theorem subst_numeral (σ : NumericalSubstitution) (n : Nat) :
    (numeral n).subst σ = numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, subst, ih]

@[simp] theorem subst_compose (t : Term) (σ τ : NumericalSubstitution) :
    (t.subst σ).subst τ = t.subst (σ.compose τ) := by
  induction t with
  | var x => cases h : σ x <;> simp [subst, NumericalSubstitution.compose, h]
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add t u iht ihu => simp [subst, iht, ihu]
  | mul t u iht ihu => simp [subst, iht, ihu]

@[simp] theorem eval_subst (t : Term) (σ : NumericalSubstitution) (s : Assignment) :
    (t.subst σ).eval s = t.eval (σ.override s) := by
  induction t with
  | var x => cases h : σ x <;> simp [subst, eval, NumericalSubstitution.override, h]
  | zero => rfl
  | succ t ih => simp [subst, eval, ih]
  | add t u iht ihu => simp [subst, eval, iht, ihu]
  | mul t u iht ihu => simp [subst, eval, iht, ihu]

end Term

inductive Formula (Owner : Type) where
  | falsum : Formula Owner
  | equal : Term → Term → Formula Owner
  | imp : Formula Owner → Formula Owner → Formula Owner
  | conj : Formula Owner → Formula Owner → Formula Owner
  | disj : Formula Owner → Formula Owner → Formula Owner
  | neg : Formula Owner → Formula Owner
  | all : Nat → Formula Owner → Formula Owner
  | ex : Nat → Formula Owner → Formula Owner
  | know : Owner → Formula Owner → Formula Owner
  deriving DecidableEq, Repr

inductive Shape (Owner : Type) where
  | falsum : Shape Owner
  | equal : Shape Owner
  | imp : Shape Owner → Shape Owner → Shape Owner
  | conj : Shape Owner → Shape Owner → Shape Owner
  | disj : Shape Owner → Shape Owner → Shape Owner
  | neg : Shape Owner → Shape Owner
  | all : Shape Owner → Shape Owner
  | ex : Shape Owner → Shape Owner
  | know : Owner → Shape Owner → Shape Owner
  deriving DecidableEq, Repr

namespace Formula

variable {Owner Other : Type}

def iff (φ ψ : Formula Owner) : Formula Owner := .conj (.imp φ ψ) (.imp ψ φ)

def shape : Formula Owner → Shape Owner
  | .falsum => .falsum
  | .equal _ _ => .equal
  | .imp φ ψ => .imp φ.shape ψ.shape
  | .conj φ ψ => .conj φ.shape ψ.shape
  | .disj φ ψ => .disj φ.shape ψ.shape
  | .neg φ => .neg φ.shape
  | .all _ φ => .all φ.shape
  | .ex _ φ => .ex φ.shape
  | .know a φ => .know a φ.shape

def freeVars : Formula Owner → Finset Nat
  | .falsum => ∅
  | .equal t u => t.freeVars ∪ u.freeVars
  | .imp φ ψ => φ.freeVars ∪ ψ.freeVars
  | .conj φ ψ => φ.freeVars ∪ ψ.freeVars
  | .disj φ ψ => φ.freeVars ∪ ψ.freeVars
  | .neg φ => φ.freeVars
  | .all x φ => φ.freeVars.erase x
  | .ex x φ => φ.freeVars.erase x
  | .know _ φ => φ.freeVars

def Closed (φ : Formula Owner) : Prop := φ.freeVars = ∅

def subst (σ : NumericalSubstitution) : Formula Owner → Formula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.subst σ) (u.subst σ)
  | .imp φ ψ => .imp (φ.subst σ) (ψ.subst σ)
  | .conj φ ψ => .conj (φ.subst σ) (ψ.subst σ)
  | .disj φ ψ => .disj (φ.subst σ) (ψ.subst σ)
  | .neg φ => .neg (φ.subst σ)
  | .all x φ => .all x (φ.subst (σ.remove x))
  | .ex x φ => .ex x (φ.subst (σ.remove x))
  | .know a φ => .know a (φ.subst σ)

/-- Named syntactic replacement, stopping under a binder for x. Used in
    PA only with successor of x, which cannot be captured by other binders. -/
def substTerm (x : Nat) (replacement : Term) : Formula Owner → Formula Owner
  | .falsum => .falsum
  | .equal t u => .equal (Term.substTerm x replacement t) (Term.substTerm x replacement u)
  | .imp φ ψ => .imp (φ.substTerm x replacement) (ψ.substTerm x replacement)
  | .conj φ ψ => .conj (φ.substTerm x replacement) (ψ.substTerm x replacement)
  | .disj φ ψ => .disj (φ.substTerm x replacement) (ψ.substTerm x replacement)
  | .neg φ => .neg (φ.substTerm x replacement)
  | .all y φ => if y = x then .all y φ else .all y (φ.substTerm x replacement)
  | .ex y φ => if y = x then .ex y φ else .ex y (φ.substTerm x replacement)
  | .know a φ => .know a (φ.substTerm x replacement)

def close (φ : Formula Owner) (s : Assignment) : Formula Owner :=
  φ.subst (fun x => some (s x))

def mapOwner (f : Owner → Other) : Formula Owner → Formula Other
  | .falsum => .falsum
  | .equal t u => .equal t u
  | .imp φ ψ => .imp (φ.mapOwner f) (ψ.mapOwner f)
  | .conj φ ψ => .conj (φ.mapOwner f) (ψ.mapOwner f)
  | .disj φ ψ => .disj (φ.mapOwner f) (ψ.mapOwner f)
  | .neg φ => .neg (φ.mapOwner f)
  | .all x φ => .all x (φ.mapOwner f)
  | .ex x φ => .ex x (φ.mapOwner f)
  | .know a φ => .know (f a) (φ.mapOwner f)

def «prefix» (a : Owner) : Nat → Formula Owner → Formula Owner
  | 0, φ => φ
  | n + 1, φ => .know a («prefix» a n φ)

@[simp] theorem subst_none (φ : Formula Owner) : φ.subst (fun _ => none) = φ := by
  induction φ <;> simp_all [subst]

@[simp] theorem freeVars_prefix (a : Owner) (n : Nat) (φ : Formula Owner) :
    («prefix» a n φ).freeVars = φ.freeVars := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [«prefix», freeVars] using ih

@[simp] theorem subst_compose (φ : Formula Owner) (σ τ : NumericalSubstitution) :
    (φ.subst σ).subst τ = φ.subst (σ.compose τ) := by
  induction φ generalizing σ τ with
  | falsum => rfl
  | equal t u => simp [subst]
  | imp φ ψ ihφ ihψ => simp [subst, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp [subst, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [subst, ihφ, ihψ]
  | neg φ ih => simp [subst, ih]
  | all x φ ih => simp [subst, ih]
  | ex x φ ih => simp [subst, ih]
  | know a φ ih => simp [subst, ih]

@[simp] theorem close_subst (φ : Formula Owner) (σ : NumericalSubstitution)
    (s : Assignment) : (φ.subst σ).close s = φ.close (σ.override s) := by
  simp [close]

@[simp] theorem close_close (φ : Formula Owner) (s t : Assignment) :
    (φ.close s).close t = φ.close s := by
  simpa [close, NumericalSubstitution.override] using
    close_subst φ (fun x => some (s x)) t

@[simp] theorem shape_subst (φ : Formula Owner) (σ : NumericalSubstitution) :
    (φ.subst σ).shape = φ.shape := by
  induction φ generalizing σ <;> simp_all [subst, shape]

@[simp] theorem shape_close (φ : Formula Owner) (s : Assignment) :
    (φ.close s).shape = φ.shape := shape_subst _ _

@[simp] theorem mapOwner_subst (φ : Formula Owner) (f : Owner → Other)
    (σ : NumericalSubstitution) :
    (φ.subst σ).mapOwner f = (φ.mapOwner f).subst σ := by
  induction φ generalizing σ <;> simp_all [subst, mapOwner]

@[simp] theorem mapOwner_close (φ : Formula Owner) (f : Owner → Other)
    (s : Assignment) : (φ.close s).mapOwner f = (φ.mapOwner f).close s := by
  simp [close]

end Formula

structure UnaryFormula (Owner : Type) where
  body : Formula Owner
  input : Nat
  freeVars_exact : body.freeVars = {input}

end Alexander313
