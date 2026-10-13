import Alexander313.Carlson.Rules
import Mathlib.Algebra.Order.Field.Rat

/-!
# Computable least upper anchors in finite ordered carriers

`Str.computableUp S x` filters the finite carrier to the points at or above
`x` and takes its minimum. If no such point exists, it returns `x` itself.
The executable operation uses the supplied linear-order decisions and
finite minimum computation, without requiring an inhabited ambient type.
Its imported proof dependencies still use the project's ordinary allowed
axioms, including `Classical.choice`. The axiom audit records these logical
dependencies separately from checking executable computation.

The result agrees exactly with the existing `Str.up`, including the
unbounded and empty-carrier cases. The `LeastGE` specification holds when
an upper anchor exists; the fallback need not belong to the carrier.
Executable rational constructions can therefore use this operation while
their correctness proofs reuse the existing least-anchor and
arithmetic-lifting arguments.
-/

namespace Alexander313.Carlson.Str

variable {α : Type*} [LinearOrder α]

/-- The least point of a finite carrier at or above `x`, or `x` when the
carrier has no such point. This is an executable finite computation. -/
def computableUp (S : Finset α) (x : α) : α :=
  let T := S.filter (fun p => x ≤ p)
  if hT : T.Nonempty then T.min' hT else x

/-- When an upper anchor exists, the computed point has the original
`LeastGE` specification. -/
theorem computableUp_spec {S : Finset α} {x : α}
    (h : ∃ p ∈ S, x ≤ p) : LeastGE S x (computableUp S x) := by
  let T := S.filter (fun p => x ≤ p)
  have hT : T.Nonempty := by
    obtain ⟨p, hp, hxp⟩ := h
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hxp⟩⟩
  change LeastGE S x (if hT : T.Nonempty then T.min' hT else x)
  rw [dif_pos hT]
  have hmem := Finset.mem_filter.mp (T.min'_mem hT)
  refine ⟨hmem.1, hmem.2, fun q hq hxq => ?_⟩
  exact T.min'_le q (Finset.mem_filter.mpr ⟨hq, hxq⟩)

/-- The computed upper anchor is any point satisfying the least-anchor
specification, by uniqueness. -/
theorem computableUp_eq_of_leastGE {S : Finset α} {x p : α}
    (h : LeastGE S x p) : computableUp S x = p :=
  (computableUp_spec ⟨p, h.1, h.2.1⟩).unique h

/-- Existing carrier points are fixed exactly. -/
@[simp] theorem computableUp_of_mem {S : Finset α} {x : α} (hx : x ∈ S) :
    computableUp S x = x :=
  computableUp_eq_of_leastGE ⟨hx, le_rfl, fun _ _ h => h⟩

/-- If the carrier does not bound `x` from above, the computation returns
`x`; it does not manufacture a carrier point. -/
theorem computableUp_of_not_bounded {S : Finset α} {x : α}
    (h : ¬ ∃ p ∈ S, x ≤ p) : computableUp S x = x := by
  have hT : ¬ (S.filter (fun p => x ≤ p)).Nonempty := by
    rintro ⟨p, hp⟩
    have hp' := Finset.mem_filter.mp hp
    exact h ⟨p, hp'.1, hp'.2⟩
  simp only [computableUp, dif_neg hT]

@[simp] theorem computableUp_empty (x : α) : computableUp ∅ x = x :=
  computableUp_of_not_bounded (by simp)

/-- Exact agreement with the original classical operation, both when an
upper anchor exists and when the fallback branch is used. -/
theorem computableUp_eq_up (S : Finset α) (x : α) : computableUp S x = up S x := by
  classical
  by_cases h : ∃ p ∈ S, x ≤ p
  · exact (computableUp_spec h).unique (up_spec h)
  · have hleast : ¬ ∃ p, LeastGE S x p := by
      rintro ⟨p, hp⟩
      exact h ⟨p, hp.1, hp.2.1⟩
    simp only [computableUp_of_not_bounded h, up, dif_neg hleast]

/-- Computing an upper anchor never decreases the query point. -/
theorem le_computableUp (S : Finset α) (x : α) : x ≤ computableUp S x := by
  classical
  by_cases h : ∃ p ∈ S, x ≤ p
  · exact (computableUp_spec h).2.1
  · simpa only [computableUp_of_not_bounded h] using (le_rfl : x ≤ x)

/-- A bounded query returns a point of the supplied carrier. -/
theorem computableUp_mem {S : Finset α} {x : α}
    (h : ∃ p ∈ S, x ≤ p) : computableUp S x ∈ S :=
  (computableUp_spec h).1

/-- Every carrier point above the query also bounds its computed anchor. -/
theorem computableUp_le_of_mem {S : Finset α} {x p : α}
    (hp : p ∈ S) (hxp : x ≤ p) : computableUp S x ≤ p :=
  (computableUp_spec ⟨p, hp, hxp⟩).2.2 p hp hxp

/-- Upper-anchor lookup is monotone on the whole ambient order, including
the fallback region above all carrier points. -/
theorem computableUp_mono (S : Finset α) : Monotone (computableUp S) := by
  classical
  intro x y hxy
  by_cases hy : ∃ p ∈ S, y ≤ p
  · obtain ⟨p, hp, hyp⟩ := hy
    have hx : ∃ p ∈ S, x ≤ p := ⟨p, hp, hxy.trans hyp⟩
    have hy' := computableUp_spec (S := S) (x := y) ⟨p, hp, hyp⟩
    exact (computableUp_spec hx).2.2 _ hy'.1 (hxy.trans hy'.2.1)
  · rw [computableUp_of_not_bounded hy]
    by_cases hx : ∃ p ∈ S, x ≤ p
    · have hlt : computableUp S x < y := lt_of_not_ge (fun h =>
        hy ⟨computableUp S x, computableUp_mem hx, h⟩)
      exact hlt.le
    · simpa only [computableUp_of_not_bounded hx] using hxy

end Alexander313.Carlson.Str

namespace Alexander313.Carlson.ComputableAnchorsExamples

/-- A small rational carrier with a negative point and a fractional anchor. -/
def anchors : Finset ℚ := {-2, 1 / 2, 3}

/-- The query may lie before the carrier, at an old point, between old
points, or above the whole carrier. The empty-carrier fallback is also
computed directly. All five checks are small kernel reductions. -/
theorem regression_suite :
    Str.computableUp (∅ : Finset ℚ) (-(3 : ℚ) / 2) = -(3 : ℚ) / 2 ∧
    Str.computableUp anchors (-3) = -2 ∧
    Str.computableUp anchors (1 / 2) = 1 / 2 ∧
    Str.computableUp anchors (-(3 : ℚ) / 2) = 1 / 2 ∧
    Str.computableUp anchors 4 = 4 := by
  decide +kernel

end Alexander313.Carlson.ComputableAnchorsExamples
