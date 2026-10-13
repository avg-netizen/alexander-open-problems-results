import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.DeriveEncodable
import Batteries.Tactic.OpenPrivate

/-!
# Primitive recursion on the original derived S-expression codes

The pinned deriving handler encodes a natural atom as `pair 0 n` and a
cons cell as `pair (encode head + 1) (encode tail)`. Both child codes of a
cons cell are strictly smaller than its code. A course-of-values fold
therefore certifies one uniform primitive-recursive interpreter for every
raw natural input, without changing any derived encoder or decoder.

The interpretation algebra must itself have primitive-recursive atom and
cons operations. This theorem supplies recursion, not those operations.
-/

namespace Alexander313.Carlson.PrimitiveSExpression

variable {α β : Type*}

theorem left_lt {n : ℕ} (h : n.unpair.1 ≠ 0) : n.unpair.1 - 1 < n := by
  have hp := Nat.unpair_left_le n
  omega

theorem right_lt {n : ℕ} (h : n.unpair.1 ≠ 0) : n.unpair.2 < n := by
  obtain ⟨⟨a, b⟩, rfl⟩ := Nat.pairEquiv.surjective n
  simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *
  unfold Nat.pair
  have ha := Nat.le_mul_self a
  have hb := Nat.le_mul_self b
  split <;> omega

/-- Evaluate an atom/cons algebra on every original raw S-expression code. -/
def fold (atom : α → ℕ → β) (cons : α → β → β → β) (a : α) (n : ℕ) : β :=
  if h : n.unpair.1 = 0 then atom a n.unpair.2
  else cons a (fold atom cons a (n.unpair.1 - 1)) (fold atom cons a n.unpair.2)
termination_by n
decreasing_by
  · exact left_lt h
  · exact right_lt h

theorem fold_eq (atom : α → ℕ → β) (cons : α → β → β → β) (a : α) (n : ℕ) :
    fold atom cons a n =
      if n.unpair.1 = 0 then atom a n.unpair.2
      else cons a (fold atom cons a (n.unpair.1 - 1))
        (fold atom cons a n.unpair.2) := by
  rw [fold]
  split <;> rfl

@[simp] theorem fold_atom (atom : α → ℕ → β) (cons : α → β → β → β)
    (a : α) (n : ℕ) : fold atom cons a (Nat.pair 0 n) = atom a n := by
  rw [fold_eq]
  simp

@[simp] theorem fold_cons (atom : α → ℕ → β) (cons : α → β → β → β)
    (a : α) (h t : ℕ) : fold atom cons a (Nat.pair (h + 1) t) =
      cons a (fold atom cons a h) (fold atom cons a t) := by
  rw [fold_eq]
  simp

/-- Both children are obtained from the already computed history. Failure
is represented explicitly in this auxiliary step. -/
def step (atom : α → ℕ → β) (cons : α → β → β → β) (a : α)
    (history : List β) : Option β :=
  let p := history.length.unpair
  if p.1 = 0 then some (atom a p.2)
  else (history[p.1 - 1]?).bind fun head =>
    (history[p.2]?).map fun tail => cons a head tail

theorem step_primrec [Primcodable α] [Primcodable β]
    {atom : α → ℕ → β} {cons : α → β → β → β}
    (ha : Primrec₂ atom) (hc : Primrec (fun p : α × β × β => cons p.1 p.2.1 p.2.2)) :
    Primrec₂ (step atom cons) := by
  apply Primrec₂.mk
  have hp : Primrec (fun p : α × List β => p.2.length.unpair) :=
    Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd)
  unfold step
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hp) (Primrec.const 0))
    (Primrec.option_some.comp (ha.comp Primrec.fst (Primrec.snd.comp hp))) ?_
  refine Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.snd (Primrec.pred.comp (Primrec.fst.comp hp))) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
      ((Primrec.snd.comp hp).comp Primrec.fst)) ?_
  exact (hc.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂

theorem step_history (atom : α → ℕ → β) (cons : α → β → β → β) (a : α) (n : ℕ) :
    step atom cons a ((List.range n).map (fold atom cons a)) =
      some (fold atom cons a n) := by
  rw [fold_eq]
  by_cases h : n.unpair.1 = 0
  · simp [step, h]
  · have hl := left_lt h
    have hr := right_lt h
    simp [step, h, hl, hr]

/-- Primitive-recursive recursion on the original derived tree encoding,
uniformly in a coded parameter and every raw natural input. -/
theorem fold_primrec [Primcodable α] [Primcodable β]
    {atom : α → ℕ → β} {cons : α → β → β → β}
    (ha : Primrec₂ atom) (hc : Primrec (fun p : α × β × β => cons p.1 p.2.1 p.2.2)) :
    Primrec₂ (fold atom cons) :=
  Primrec.nat_strong_rec (fold atom cons) (step_primrec ha hc) (step_history atom cons)

section OriginalDerivedTree

open private S S.nat S.cons S.encode from Mathlib.Tactic.DeriveEncodable

/-- Structural interpretation of the exact tree used by the deriving handler. -/
private def treeFold (atom : α → ℕ → β) (cons : α → β → β → β) (a : α) : S → β
  | S.nat n => atom a n
  | S.cons h t => cons a (treeFold atom cons a h) (treeFold atom cons a t)

private theorem fold_encode (atom : α → ℕ → β) (cons : α → β → β → β)
    (a : α) (s : S) : fold atom cons a (S.encode s) = treeFold atom cons a s := by
  induction s with
  | nat n => rw [fold_eq]; simp [S.encode, treeFold]
  | cons h t ihh iht =>
      rw [fold_eq]
      simp [S.encode, treeFold, ihh, iht]

end OriginalDerivedTree

end Alexander313.Carlson.PrimitiveSExpression
