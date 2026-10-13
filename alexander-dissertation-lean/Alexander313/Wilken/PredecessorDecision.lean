import Mathlib.Data.Set.Finite.Basic

/-!
# The greatest-predecessor decision reduction

The input contract must be proved for Wilken's concrete tracking-chain
predecessor. This file proves termination and correctness of the reduction;
it does not assume that a recursive ordinal order decides resemblance.
-/

namespace Alexander313.Wilken

structure PredecessorSystem (Carrier : Type) where
  lt : Carrier → Carrier → Prop
  wf : WellFounded lt
  predecessor : Carrier → Option Carrier
  decreases : ∀ y p, predecessor y = some p → lt p y
  relation : Carrier → Carrier → Prop
  relation_iff : ∀ x y, relation x y ↔
    x = y ∨ ∃ p, predecessor y = some p ∧ relation x p

namespace PredecessorSystem

variable {Carrier : Type} [DecidableEq Carrier]

def walkStep (S : PredecessorSystem Carrier) (y : Carrier)
    (ih : ∀ p, S.lt p y → Carrier → Bool) (x : Carrier) : Bool :=
  if x = y then true else
    match hp : S.predecessor y with
    | none => false
    | some p => ih p (S.decreases y p hp) x

def decide (S : PredecessorSystem Carrier) (x y : Carrier) : Bool :=
  S.wf.fix (S.walkStep) y x

theorem decide_eq (S : PredecessorSystem Carrier) (x y : Carrier) :
    S.decide x y = if x = y then true else
      match S.predecessor y with
      | none => false
      | some p => S.decide x p := by
  have heq : S.decide x y =
      S.walkStep y (fun p _ z => S.decide z p) x := by
    unfold decide
    rw [WellFounded.fix_eq]
  rw [heq]
  unfold walkStep
  by_cases hxy : x = y
  · simp only [hxy, ↓reduceIte]
  · simp only [hxy, ↓reduceIte]
    cases hp : S.predecessor y <;> simp only [hp]

theorem decide_correct (S : PredecessorSystem Carrier) (x y : Carrier) :
    S.decide x y = true ↔ S.relation x y := by
  have all : ∀ y x, S.decide x y = true ↔ S.relation x y := by
    intro y
    induction y using S.wf.induction with
    | h y ih =>
      intro x
      rw [S.decide_eq, S.relation_iff]
      by_cases hxy : x = y
      · simp [hxy]
      · cases hp : S.predecessor y with
        | none => simp [hxy, hp]
        | some p => simpa [hxy, hp] using ih p (S.decreases y p hp) x
  exact all y x

end PredecessorSystem

end Alexander313.Wilken
