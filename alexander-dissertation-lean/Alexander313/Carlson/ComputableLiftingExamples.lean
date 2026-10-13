import Alexander313.Carlson.ComputablePatternLifting

/-!
# Kernel computations of complete rational liftings

These examples execute the complete constructor, including rational
placement, finite source images, and both candidate relation tables. The
nontrivial example has a translated base map, a negative source label, a
fractional new target label, and mixed old/new edges in both relations.
Deliberately supplied off-carrier edges do not survive in the output.
-/

namespace Alexander313.Carlson.Finite.ComputableLiftingExamples

open RationalPresentation

def base : RationalPresentation :=
  ⟨{0}, {(0, 0), (99, 99)}, {(0, 0), (98, 99)}⟩

def extended : RationalPresentation :=
  ⟨{-1, 0}, {(-1, -1), (-1, 0), (0, 0), (99, 99)},
    {(-1, -1), (-1, 0), (0, 0), (98, 99)}⟩

def target : RationalPresentation :=
  ⟨{0, 1}, {(0, 0), (0, 1), (1, 1), (9, 9)},
    {(0, 0), (0, 1), (1, 1), (8, 9)}⟩

def expectedEdges : Finset (ℚ × ℚ) :=
  {(0, 0), (0, 1 / 3), (0, 1), (1 / 3, 1 / 3), (1 / 3, 1), (1, 1)}

/-- Both complete output tables and both on-carrier map values are
computed by the Lean kernel, including incoming second-level edges. -/
theorem end_to_end_regression :
    (lift base extended target (fun x => x + 1)).1.U = {0, 1 / 3, 1} ∧
    (lift base extended target (fun x => x + 1)).1.r₁ = expectedEdges ∧
    (lift base extended target (fun x => x + 1)).1.r₂ = expectedEdges ∧
    (lift base extended target (fun x => x + 1)).2 (-1) = 1 / 3 ∧
    (lift base extended target (fun x => x + 1)).2 0 = 1 := by
  decide +kernel

/-- A request with no new source points leaves exactly the target's
on-carrier presentation, without retaining its irrelevant outside edges. -/
theorem stationary_regression :
    (lift base base target (fun x => x + 1)).1 =
      ⟨{0, 1}, {(0, 0), (0, 1), (1, 1)}, {(0, 0), (0, 1), (1, 1)}⟩ := by
  decide +kernel

def empty : RationalPresentation := ⟨∅, ∅, ∅⟩

/-- The complete empty-carrier construction executes without an anchor,
a predecessor, a chosen point, or a division requiring nonemptiness. -/
theorem empty_regression : (lift empty empty empty id).1 = empty := by
  decide +kernel

end Alexander313.Carlson.Finite.ComputableLiftingExamples
