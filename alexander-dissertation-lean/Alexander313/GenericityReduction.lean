import Alexander313.FinitePolicy

/-!
# Reduction of genericity to finite outside policies

This proves the finite-policy reduction used in note 26 §§4--5 for any
retained region, including the core alone or a full downward ideal and core.
The local finite-policy genericity theorem and mask admissibility still have
to be obtained from the actual source presentations. They are explicit
premises here, rather than newly asserted source facts.
-/

namespace Alexander313

def FiniteOutsidePolicy {Owner : Type} [DecidableEq Owner]
    (full : Owner → Prop) (P : RawPredicates Owner) : Prop :=
  ∃ H : Finset (Owner × Shape Owner),
    ∀ a θ, ¬ full a → P a θ → (a, θ.shape) ∈ H

theorem rawShapeMask_finite_policy {Owner : Type} [DecidableEq Owner]
    (P : RawPredicates Owner) (full : Owner → Prop)
    (H : Finset (Owner × Shape Owner)) :
    FiniteOutsidePolicy full (rawShapeMask P full H) := by
  refine ⟨H, ?_⟩
  intro a θ ha hθ
  exact hθ.1.resolve_left ha

theorem finite_policy_genericity_reduction {Owner : Type} [DecidableEq Owner]
    (source : RawPredicates Owner) (full : Owner → Prop)
    (Admissible : RawPredicates Owner → Prop)
    (mask_admissible : ∀ P, Admissible P → ∀ φ : Formula Owner,
      Admissible (rawShapeMask P full φ.queries))
    (finite_step : ∀ P, Admissible P →
      (∀ a, full a → ∀ θ, P a θ ↔ source a θ) →
      (∀ a, ¬ full a → RawSound P a) → FiniteOutsidePolicy full P →
      ∀ a, full a → RawSound P a) :
    ∀ P, Admissible P →
      (∀ a, full a → ∀ θ, P a θ ↔ source a θ) →
      (∀ a, ¬ full a → RawSound P a) →
      ∀ a, full a → RawSound P a := by
  intro P hP retained outside a ha φ s hp
  let Q := rawShapeMask P full φ.queries
  have hQ : Admissible Q := mask_admissible P hP φ
  have Qretained : ∀ b, full b → ∀ θ, Q b θ ↔ source b θ := by
    intro b hb θ
    exact (rawShapeMask_full P full φ.queries b hb θ).trans (retained b hb θ)
  have Qoutside : ∀ b, ¬ full b → RawSound Q b :=
    rawShapeMask_target_outside_sound P full φ outside
  have sound : RawSound Q a := finite_step Q hQ Qretained Qoutside
    (rawShapeMask_finite_policy P full φ.queries) a ha
  have hquery : Q a (φ.close s) :=
    (rawShapeMask_full P full φ.queries a ha (φ.close s)).mpr hp
  exact (rawShapeMask_target_truth true P full φ s).mp (sound φ s hquery)

end Alexander313
