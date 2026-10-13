import Alexander313.Carlson.ComputableAmalgamation
import Alexander313.Carlson.PointedPatternComparison

/-!
# Executable comparison of actual pointed core labels

For two pointed seeds, search for a checked finite-edge amalgamation and
read its finite order and relation tables. The semantic pointed comparison
theorem identifies every answer with the actual least ordinal labels.
No ordinal realization is evaluated by the algorithm.
-/

namespace Alexander313.Carlson

open Finite

namespace PointedPattern

/-- Finite input data for the two-seed amalgamation search. -/
def pairFamily (p q : PointedPattern) (i : Fin 2) : RationalPresentation :=
  Fin.cases p.seed.val (fun _ => q.seed.val) i

theorem pairFamily_pattern (p q : PointedPattern) :
    ∀ i, (pairFamily p q i).toStr.IsPattern :=
  Fin.cases p.seed.property (fun _ => q.seed.property)

private def pairPoints (p q : PointedPattern) (i : Fin 2) : PointedPattern :=
  Fin.cases p (fun _ => q) i

/-- Five answers from the same checked finite amalgamation. -/
structure Comparison where
  eq : Bool
  le : Bool
  lt : Bool
  one : Bool
  two : Bool

/-- A terminating finite-data algorithm for the actual equality, order,
R1 and R2 comparisons of the two least labels. -/
def compare (p q : PointedPattern) : Comparison :=
  let c := ComputableAmalgamation.compute (pairFamily p q) (pairFamily_pattern p q)
  let x := c.maps 0 p.point
  let y := c.maps 1 q.point
  ⟨decide (x = y), decide (x ≤ y), decide (x < y),
    decide ((x, y) ∈ c.1.r₁), decide ((x, y) ∈ c.1.r₂)⟩

/-- Every answer computes the corresponding relation on actual pointed
ordinal labels, rather than merely on an arbitrary quotient presentation. -/
theorem compare_correct (p q : PointedPattern) :
    ((compare p q).eq = true ↔ p.iota = q.iota) ∧
    ((compare p q).le = true ↔ p.iota ≤ q.iota) ∧
    ((compare p q).lt = true ↔ p.iota < q.iota) ∧
    ((compare p q).one = true ↔ R1 p.iota q.iota) ∧
    ((compare p q).two = true ↔ R2 p.iota q.iota) := by
  let c := ComputableAmalgamation.compute (pairFamily p q) (pairFamily_pattern p q)
  have hfamily : (fun i => (pairPoints p q i).seed.val.toStr) =
      (fun i => (pairFamily p q i).toStr) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  have d : Str.Amalgamation (fun i => (pairPoints p q i).seed.val.toStr) c.1.toStr c.maps :=
    hfamily ▸ ComputableAmalgamation.compute_amalgamation (pairFamily p q) (pairFamily_pattern p q)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [compare, decide_eq_true_eq, pairPoints, Fin.cases_zero,
      Fin.cases_succ, show (1 : Fin 2) = Fin.succ 0 from rfl, c] using (d.pointed_eq_iff (p := pairPoints p q) 0 1).symm
  · simpa only [compare, decide_eq_true_eq, pairPoints, Fin.cases_zero,
      Fin.cases_succ, show (1 : Fin 2) = Fin.succ 0 from rfl, c] using (d.pointed_le_iff (p := pairPoints p q) 0 1).symm
  · simpa only [compare, decide_eq_true_eq, pairPoints, Fin.cases_zero,
      Fin.cases_succ, show (1 : Fin 2) = Fin.succ 0 from rfl, c] using (d.pointed_lt_iff (p := pairPoints p q) 0 1).symm
  · simpa only [compare, decide_eq_true_eq, pairPoints, Fin.cases_zero,
      Fin.cases_succ, show (1 : Fin 2) = Fin.succ 0 from rfl, c, RationalPresentation.toStr_r₁] using
      (d.pointed_one_iff (p := pairPoints p q) 0 1).symm
  · simpa only [compare, decide_eq_true_eq, pairPoints, Fin.cases_zero,
      Fin.cases_succ, show (1 : Fin 2) = Fin.succ 0 from rfl, c, RationalPresentation.toStr_r₂] using
      (d.pointed_two_iff (p := pairPoints p q) 0 1).symm

end PointedPattern
end Alexander313.Carlson
