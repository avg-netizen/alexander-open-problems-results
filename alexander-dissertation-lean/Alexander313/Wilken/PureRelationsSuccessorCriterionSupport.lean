import Alexander313.Wilken.PureRelationsSecondSuccessors

/-!
# Complete endpoint replacement for the actual successor criterion

The displayed supremum property supplies a real second successor above every
cut. Replacing only the upper endpoint preserves the complete finite expanded
pattern once its first and second predecessor facts agree with the original
endpoint. Reverse endpoint facts are excluded by the ordinary order, and the
endpoint's self facts follow from actual reflexivity. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SuccessorCriterion

theorem secondSuccessors_above_cut (α δ c : Ordinal.{0})
    (supremum : IsLUB (SecondSuccessorsBelow α δ) α) (hc : c < α) :
    ∃ y : Ordinal.{0}, c < y ∧ y < α ∧ R2 δ y := by
  classical
  by_contra hnone
  apply not_le_of_gt hc
  apply supremum.2
  intro y hy
  apply le_of_not_gt
  intro hcy
  exact hnone ⟨y, hcy, hy.1, hy.2⟩

/-- A single actual endpoint replacement retains EVERY positive and
negative equality, order, first and second fact on the entire original set.
The supplied endpoint equations are proved from actual relations in the
main theorem, not assumptions of the final successor criterion. -/
theorem endpoint_replacement (α y : Ordinal.{0}) (X : Finset Ordinal.{0})
    (hX : ∀ x ∈ X, x < α) (hy : y < α) (above : ∀ x ∈ X, x < y)
    (first : ∀ x ∈ X, R1 x y ↔ R1 x α)
    (second : ∀ x ∈ X, R2 x y ↔ R2 x α) :
    ∃ f : Ordinal.{0} → Ordinal.{0},
      (∀ x ∈ X ∪ {α}, f x < α) ∧ (∀ x ∈ X, f x = x) ∧
        PreservesPattern (X ∪ {α}) f := by
  classical
  let f : Ordinal.{0} → Ordinal.{0} := fun x => if x = α then y else x
  have fixed (x : Ordinal.{0}) (hx : x ∈ X) : f x = x := by
    simp only [f, if_neg (ne_of_lt (hX x hx))]
  have top : f α = y := by simp only [f, if_pos rfl]
  have member (x : Ordinal.{0}) (hx : x ∈ X ∪ {α}) : x ∈ X ∨ x = α := by
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Finset.mem_singleton.mp hx)
  refine ⟨f, ?_, fixed, ?_⟩
  · intro x hx
    rcases member x hx with hxX | hxA
    · rw [fixed x hxX]
      exact hX x hxX
    · subst x
      rw [top]
      exact hy
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx z hz
      rcases member x hx with hxX | hxA
      · rcases member z hz with hzX | hzA
        · rw [fixed x hxX, fixed z hzX]
        · subst z
          rw [fixed x hxX, top]
          simp only [ne_of_lt (above x hxX), ne_of_lt (hX x hxX)]
      · subst x
        rcases member z hz with hzX | hzA
        · rw [top, fixed z hzX]
          simp only [ne_of_gt (above z hzX), ne_of_gt (hX z hzX)]
        · subst z
          rw [top]
          exact ⟨fun _ => rfl, fun _ => rfl⟩
    · intro x hx z hz
      rcases member x hx with hxX | hxA
      · rcases member z hz with hzX | hzA
        · rw [fixed x hxX, fixed z hzX]
        · subst z
          rw [fixed x hxX, top]
          exact ⟨fun _ => hX x hxX, fun _ => above x hxX⟩
      · subst x
        rcases member z hz with hzX | hzA
        · rw [top, fixed z hzX]
          exact ⟨fun h => False.elim ((not_le_of_gt (above z hzX)) h.le),
            fun h => False.elim ((not_le_of_gt (hX z hzX)) h.le)⟩
        · subst z
          rw [top]
          simp only [lt_self_iff_false]
    · intro x hx z hz
      rcases member x hx with hxX | hxA
      · rcases member z hz with hzX | hzA
        · rw [fixed x hxX, fixed z hzX]
        · subst z
          rw [fixed x hxX, top]
          exact first x hxX
      · subst x
        rcases member z hz with hzX | hzA
        · rw [top, fixed z hzX]
          exact ⟨fun h => False.elim ((not_le_of_gt (above z hzX)) (R1_le h)),
            fun h => False.elim ((not_le_of_gt (hX z hzX)) (R1_le h))⟩
        · subst z
          rw [top]
          exact ⟨fun _ => R1_refl α, fun _ => R1_refl y⟩
    · intro x hx z hz
      rcases member x hx with hxX | hxA
      · rcases member z hz with hzX | hzA
        · rw [fixed x hxX, fixed z hzX]
        · subst z
          rw [fixed x hxX, top]
          exact second x hxX
      · subst x
        rcases member z hz with hzX | hzA
        · rw [top, fixed z hzX]
          exact ⟨fun h => False.elim ((not_le_of_gt (above z hzX)) (R2_le h)),
            fun h => False.elim ((not_le_of_gt (hX z hzX)) (R2_le h))⟩
        · subst z
          rw [top]
          exact ⟨fun _ => R2_refl α, fun _ => R2_refl y⟩

end Alexander313.Wilken.PureRelations.SuccessorCriterion
