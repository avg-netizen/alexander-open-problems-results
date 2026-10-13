import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Common

/-!
# Finite relative-term syntax

Raw syntax for Wilken Definitions 2.17, 2.21 and 2.23. Admissibility,
normal forms and ordinal denotation are distinct from raw syntax. This
file does not claim that every raw tree denotes a public ordinal.
-/

namespace Alexander313.Wilken

inductive RelativeTerm (Parameter : Type) where
  | parameter : Parameter → RelativeTerm Parameter
  | sum : RelativeTerm Parameter → RelativeTerm Parameter → RelativeTerm Parameter
  | theta : Nat → RelativeTerm Parameter → RelativeTerm Parameter
  deriving DecidableEq, Repr

namespace RelativeTerm

variable {Parameter : Type}

def size : RelativeTerm Parameter → Nat
  | .parameter _ => 1
  | .sum a b => a.size + b.size + 1
  | .theta _ a => a.size + 1

def height : RelativeTerm Parameter → Nat
  | .parameter _ => 0
  | .sum a b => max a.height b.height
  | .theta k a => max (k + 1) a.height

def indices : RelativeTerm Parameter → Finset Nat
  | .parameter _ => ∅
  | .sum a b => a.indices ∪ b.indices
  | .theta k a => insert k a.indices

def eval (parameters : Parameter → Ordinal)
    (theta : Nat → Ordinal → Ordinal) : RelativeTerm Parameter → Ordinal
  | .parameter p => parameters p
  | .sum a b => a.eval parameters theta + b.eval parameters theta
  | .theta k a => theta k (a.eval parameters theta)

def subtermsAt [DecidableEq Parameter] (m : Nat) :
    RelativeTerm Parameter → Finset (RelativeTerm Parameter)
  | .parameter p => {.parameter p}
  | .sum a b => insert (.sum a b) (a.subtermsAt m ∪ b.subtermsAt m)
  | .theta k a => if m ≤ k then insert (.theta k a) (a.subtermsAt m)
      else {.theta k a}

def parameters [DecidableEq Parameter] : RelativeTerm Parameter → Finset Parameter
  | .parameter p => {p}
  | .sum a b => a.parameters ∪ b.parameters
  | .theta _ a => a.parameters

theorem index_lt_height (t : RelativeTerm Parameter) (k : Nat)
    (hk : k ∈ t.indices) : k < t.height := by
  induction t with
  | parameter p => simp [indices] at hk
  | sum a b iha ihb =>
    simp only [indices, Finset.mem_union] at hk
    rcases hk with hk | hk
    · exact lt_of_lt_of_le (iha hk) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihb hk) (le_max_right _ _)
  | theta j a ih =>
    simp only [indices, Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih hk) (le_max_right _ _)

theorem self_mem_subterms [DecidableEq Parameter]
    (t : RelativeTerm Parameter) (m : Nat) : t ∈ t.subtermsAt m := by
  cases t with
  | parameter p => simp [subtermsAt]
  | sum a b => simp [subtermsAt]
  | theta k a => by_cases h : m ≤ k <;> simp [subtermsAt, h]

theorem sum_left_size_lt (a b : RelativeTerm Parameter) : a.size < (.sum a b : RelativeTerm Parameter).size := by
  simp only [size]
  omega

theorem sum_right_size_lt (a b : RelativeTerm Parameter) : b.size < (.sum a b : RelativeTerm Parameter).size := by
  simp only [size]
  omega

theorem theta_arg_size_lt (k : Nat) (a : RelativeTerm Parameter) :
    a.size < (.theta k a : RelativeTerm Parameter).size := by
  simp only [size]
  omega

end RelativeTerm

end Alexander313.Wilken
