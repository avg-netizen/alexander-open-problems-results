import Alexander313.RecordedLabelMaps

/-!
# Pointwise minima of coherent lifts

A paired-label formula records two lifts with the same source syntax, owners
and live/ghost modes. Their literal pointwise minimum preserves global nesting
through every Boolean, quantified, live and ghost context. Every minimum label
is one of the two original labels, so membership in a common chain is retained.
This is the nesting argument in note 24 section 4. Equivalence of the lifts
still requires the actual contextual-collapse generators and their transport.
-/

namespace Alexander313

namespace Formula

variable {Owner Label : Type} [LinearOrder Label]

theorem globallyStratified_minimum
    (φ : Formula (RecordedHead Owner (Label × Label)))
    (left : (φ.relabel Prod.fst).GloballyStratified)
    (right : (φ.relabel Prod.snd).GloballyStratified) :
    (φ.relabel (fun ν => min ν.1 ν.2)).GloballyStratified := by
  revert left right
  induction φ with
  | falsum => intro _ _; trivial
  | equal t u => intro _ _; trivial
  | imp φ ψ ihφ ihψ =>
    intro left right
    exact ⟨ihφ left.1 right.1, ihψ left.2 right.2⟩
  | conj φ ψ ihφ ihψ =>
    intro left right
    exact ⟨ihφ left.1 right.1, ihψ left.2 right.2⟩
  | disj φ ψ ihφ ihψ =>
    intro left right
    exact ⟨ihφ left.1 right.1, ihψ left.2 right.2⟩
  | neg φ ih => intro left right; exact ih left right
  | all x φ ih => intro left right; exact ih left right
  | ex x φ ih => intro left right; exact ih left right
  | know a φ ih =>
    intro left right
    cases a with
    | live a => exact ih left right
    | ghost a => exact ih left right
    | indexed a ν =>
      refine ⟨ih left.1 right.1, ?_⟩
      intro ξ hξ
      change ξ ∈ (φ.relabel (fun μ => min μ.1 μ.2)).labelSupport at hξ
      rw [labelSupport_relabel] at hξ
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hξ
      have hleft : μ.1 < ν.1 := left.2 μ.1 (by
        change μ.1 ∈ (φ.relabel Prod.fst).labelSupport
        rw [labelSupport_relabel]
        exact Finset.mem_image.mpr ⟨μ, hμ, rfl⟩)
      have hright : μ.2 < ν.2 := right.2 μ.2 (by
        change μ.2 ∈ (φ.relabel Prod.snd).labelSupport
        rw [labelSupport_relabel]
        exact Finset.mem_image.mpr ⟨μ, hμ, rfl⟩)
      exact lt_min (lt_of_le_of_lt (min_le_left _ _) hleft)
        (lt_of_le_of_lt (min_le_right _ _) hright)

theorem minimum_support_retained
    (φ : Formula (RecordedHead Owner (Label × Label))) (C : Set Label)
    (left : ∀ ν ∈ (φ.relabel Prod.fst).labelSupport, ν ∈ C)
    (right : ∀ ν ∈ (φ.relabel Prod.snd).labelSupport, ν ∈ C) :
    ∀ ν ∈ (φ.relabel (fun μ => min μ.1 μ.2)).labelSupport, ν ∈ C := by
  intro ν hν
  rw [labelSupport_relabel] at hν
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν
  by_cases h : μ.1 ≤ μ.2
  · rw [min_eq_left h]
    apply left
    rw [labelSupport_relabel]
    exact Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  · rw [min_eq_right (le_of_not_ge h)]
    apply right
    rw [labelSupport_relabel]
    exact Finset.mem_image.mpr ⟨μ, hμ, rfl⟩

end Formula

end Alexander313
