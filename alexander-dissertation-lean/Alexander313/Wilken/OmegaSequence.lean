import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# The regular-cardinal sequence preceding Wilken Definition 2.1

For each actual ordinal base τ we choose Ω₁ to be the initial ordinal of
the successor of `max aleph0 τ.card`. Thus Ω₁ is uncountable, regular,
and greater than τ. All subsequent levels are cardinal successors.
This is a concrete ZFC construction, with no assumed regular-cardinal tower.
-/

namespace Alexander313.Wilken

open Order

/-- The cardinal predecessor at index zero is auxiliary; Ω₀ itself is τ. -/
noncomputable def levelCardinal (τ : Ordinal) : Nat → Cardinal
  | 0 => max Cardinal.aleph0 τ.card
  | k + 1 => succ (levelCardinal τ k)

noncomputable def omegaSequence (τ : Ordinal) : Nat → Ordinal
  | 0 => τ
  | k + 1 => (levelCardinal τ (k + 1)).ord

theorem levelCardinal_infinite (τ : Ordinal) (k : Nat) :
    Cardinal.aleph0 ≤ levelCardinal τ k := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih => exact ih.trans (le_succ _)

theorem levelCardinal_step (τ : Ordinal) (k : Nat) :
    levelCardinal τ k < levelCardinal τ (k + 1) := by
  exact lt_succ _

theorem levelCardinal_strictMono (τ : Ordinal) :
    StrictMono (levelCardinal τ) :=
  strictMono_nat_of_lt_succ (levelCardinal_step τ)

theorem omegaSequence_zero (τ : Ordinal) : omegaSequence τ 0 = τ := rfl

theorem omegaSequence_base_lt (τ : Ordinal) : τ < omegaSequence τ 1 := by
  apply Cardinal.lt_ord.mpr
  exact (le_max_right Cardinal.aleph0 τ.card).trans_lt (lt_succ _)

theorem omegaSequence_step (τ : Ordinal) (k : Nat) :
    omegaSequence τ k < omegaSequence τ (k + 1) := by
  cases k with
  | zero => exact omegaSequence_base_lt τ
  | succ k =>
    exact Cardinal.ord_strictMono (levelCardinal_step τ (k + 1))

theorem omegaSequence_strictMono (τ : Ordinal) : StrictMono (omegaSequence τ) :=
  strictMono_nat_of_lt_succ (omegaSequence_step τ)

theorem omegaSequence_regular (τ : Ordinal) (k : Nat) :
    (levelCardinal τ (k + 1)).IsRegular :=
  Cardinal.isRegular_succ (levelCardinal_infinite τ k)

theorem omegaSequence_uncountable (τ : Ordinal) (k : Nat) :
    Cardinal.aleph0 < (omegaSequence τ (k + 1)).card := by
  rw [omegaSequence, Cardinal.card_ord]
  exact (levelCardinal_infinite τ k).trans_lt (lt_succ _)

theorem omegaSequence_cardinal_successor (τ : Ordinal) (k : Nat) :
    omegaSequence τ (k + 2) = (succ (omegaSequence τ (k + 1)).card).ord := by
  simp only [omegaSequence, Cardinal.card_ord, levelCardinal]

theorem omegaSequence_add_closed (τ : Ordinal) (k : Nat) :
    Ordinal.IsPrincipal (· + ·) (omegaSequence τ (k + 1)) :=
  Ordinal.isPrincipal_add_ord (levelCardinal_infinite τ (k + 1))

theorem omegaSequence_isSuccLimit (τ : Ordinal) (k : Nat) :
    Order.IsSuccLimit (omegaSequence τ (k + 1)) :=
  Cardinal.isSuccLimit_ord (levelCardinal_infinite τ (k + 1))

end Alexander313.Wilken
