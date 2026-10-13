import Alexander313.HereditaryMasks

/-!
# The finite-policy reduction for core and whole-ideal genericity

The full region is retained without restricting any argument. Outside it,
only finitely many owner/argument skeletons remain. Heredity preserves truth
on every retained argument, proving full soundness of the changed outside
predicates from their old full soundness. This is a semantic restriction;
an arbitrary `full` predicate is not asserted to be a computable selector.
-/

namespace Alexander313

def rawShapeMask {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) : RawPredicates Owner :=
  fun a θ => (full a ∨ (a, θ.shape) ∈ H) ∧ P a θ

theorem rawShapeMask_full {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) (a : Owner) (ha : full a)
    (θ : Formula Owner) : rawShapeMask P full H a θ ↔ P a θ :=
  ⟨fun h => h.2, fun h => ⟨Or.inl ha, h⟩⟩

theorem rawShapeMask_omitted {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) (a : Owner) (ha : ¬ full a)
    (θ : Formula Owner) (hθ : (a, θ.shape) ∉ H) :
    ¬ rawShapeMask P full H a θ := by
  intro h
  exact h.1.elim ha hθ

theorem rawShapeMask_agrees {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) (φ : Formula Owner)
    (hφ : φ.queries ⊆ H) : AgreeOn (rawShapeMask P full H) P φ := by
  intro a θ hθ
  exact ⟨fun h => h.2, fun h => ⟨Or.inr (hφ hθ), h⟩⟩

theorem rawShapeMask_truth {Owner : Type} [DecidableEq Owner]
    (filtered : Bool) (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) (φ : Formula Owner)
    (hφ : φ.queries ⊆ H) (s : Assignment) :
    truth filtered (rawShapeMask P full H) φ s ↔ truth filtered P φ s :=
  truth_congr_queries filtered _ P φ s (rawShapeMask_agrees P full H φ hφ)

/-- Soundness means every accepted formula and every assignment, even for
    formulas outside the finite target that share a retained skeleton. -/
theorem rawShapeMask_outside_sound {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) (hereditary : HereditaryQueries H)
    (a : Owner) (ha : ¬ full a) (old_sound : RawSound P a) :
    RawSound (rawShapeMask P full H) a := by
  intro φ s hp
  have hclass : (a, φ.shape) ∈ H := by
    rcases hp.1 with hfull | hshape
    · exact False.elim (ha hfull)
    · simpa only [Formula.shape_close] using hshape
  have hqueries := hereditary a φ.shape hclass
  have hφ : φ.queries ⊆ H := by
    simpa only [Formula.queries_shape] using hqueries
  exact (rawShapeMask_truth true P full H φ hφ s).mpr (old_sound φ s hp.2)

theorem rawShapeMask_all_outside_sound {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) (hereditary : HereditaryQueries H)
    (old_sound : ∀ a, ¬ full a → RawSound P a) :
    ∀ a, ¬ full a → RawSound (rawShapeMask P full H) a :=
  fun a ha => rawShapeMask_outside_sound P full H hereditary a ha (old_sound a ha)

theorem rawShapeMask_target_truth {Owner : Type} [DecidableEq Owner]
    (filtered : Bool) (P : RawPredicates Owner) (full : Owner → Prop)
    (φ : Formula Owner) (s : Assignment) :
    truth filtered (rawShapeMask P full φ.queries) φ s ↔ truth filtered P φ s :=
  rawShapeMask_truth filtered P full φ.queries φ (fun _ h => h) s

theorem rawShapeMask_target_outside_sound {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop) (φ : Formula Owner)
    (old_sound : ∀ a, ¬ full a → RawSound P a) :
    ∀ a, ¬ full a → RawSound (rawShapeMask P full φ.queries) a :=
  rawShapeMask_all_outside_sound P full φ.queries (target_queries_hereditary φ) old_sound

end Alexander313
