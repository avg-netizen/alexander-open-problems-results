import Alexander313.Specification
import Alexander313.StageSupport
import Alexander313.Hierarchy

/-!
# The stronger genericity induction used for 3-1-2

All lower full predicates are retained; external predicates are quantified
over, rather than frozen. Proving the concrete genericity step from the
transparent stratified construction remains a source-development task.
-/

namespace Alexander313

def DownCone (R : Nat → Nat → Prop) (j i : Nat) : Prop :=
  j = i ∨ StrictBelow R j i

def RetainsCone (R : Nat → Nat → Prop) (source P : RawPredicates Nat)
    (i : Nat) : Prop :=
  ∀ j, DownCone R j i → ∀ φ, P j φ ↔ source j φ

/-- `Admissible` must encode the alphabetic and computability conditions
    proved for actual source/masked predicates. It is an explicit input. -/
def Generic312 (R : Nat → Nat → Prop) (source : RawPredicates Nat)
    (Admissible : RawPredicates Nat → Prop) (i : Nat) : Prop :=
  ∀ P, Admissible P → RetainsCone R source P i → RawSound P i

theorem generic312_wellFounded (R : Nat → Nat → Prop) (wf : WellFounded R)
    (source : RawPredicates Nat) (Admissible : RawPredicates Nat → Prop)
    (step : ∀ i, (∀ j, R j i → Generic312 R source Admissible j) →
      Generic312 R source Admissible i) : ∀ i, Generic312 R source Admissible i := by
  intro i
  induction i using wf.induction with
  | h i ih => exact step i ih

theorem actual_sound_of_generic312 (R : Nat → Nat → Prop)
    (source : RawPredicates Nat) (Admissible : RawPredicates Nat → Prop)
    (hsource : Admissible source)
    (hg : ∀ i, Generic312 R source Admissible i) : ∀ i, RawSound source i := by
  intro i
  exact hg i source hsource (fun _ _ _ => Iff.rfl)

theorem statement312_implies311 (h : Statement312) : Statement311 := by
  intro R hre hwf
  obtain ⟨S⟩ := h R hre hwf
  exact ⟨S.toSolution311⟩

end Alexander313
