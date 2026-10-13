import Alexander313.Wilken.PureRelationsLimitClosure

/-!
# Genuine eventual exclusion of negative pure relation facts

Actual right-limit closure proves that if a lower point does not relate to
a proper limit, then its related upper points below that limit are bounded.
The finite theorem constructs ONE cutoff above all original finite points
and all their negative R1/R2 bounds. This is the actual complete-pattern
input needed for the successor criterion; no negative-relation bound oracle
or recursive public decision is supplied. Uncompiled proof candidates.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

theorem R1_negative_bound (α x : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    (hx : x < α) (hnot : ¬ R1 x α) :
    ∃ c : Ordinal.{0}, c < α ∧ ∀ γ : Ordinal.{0}, c ≤ γ → γ < α → ¬ R1 x γ := by
  classical
  by_contra hnone
  have cofinal : ∀ δ : Ordinal.{0}, δ < α →
      ∃ γ : Ordinal.{0}, γ < α ∧ δ ≤ γ ∧ R1 x γ := by
    intro δ hδ
    by_contra hbad
    apply hnone
    refine ⟨δ, hδ, ?_⟩
    intro γ hδγ hγα hR
    exact hbad ⟨γ, hγα, hδγ, hR⟩
  exact hnot (R1_cofinal_limit hα hx cofinal)

theorem R2_negative_bound (α x : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    (hx : x < α) (hnot : ¬ R2 x α) :
    ∃ c : Ordinal.{0}, c < α ∧ ∀ γ : Ordinal.{0}, c ≤ γ → γ < α → ¬ R2 x γ := by
  classical
  by_contra hnone
  have cofinal : ∀ δ : Ordinal.{0}, δ < α →
      ∃ γ : Ordinal.{0}, γ < α ∧ δ ≤ γ ∧ R2 x γ := by
    intro δ hδ
    by_contra hbad
    apply hnone
    refine ⟨δ, hδ, ?_⟩
    intro γ hδγ hγα hR
    exact hbad ⟨γ, hγα, hδγ, hR⟩
  exact hnot (R2_cofinal_limit hα hx cofinal)

/-- A SINGLE actual cutoff bounds every negative first/second endpoint
fact on the original finite set and also lies strictly above all its points.
Both positive and negative original patterns can therefore share one copy. -/
theorem finite_negative_bounds (α : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < α) :
    ∃ c : Ordinal.{0}, c < α ∧ (∀ x ∈ X, x < c) ∧
      ∀ x ∈ X, ∀ γ : Ordinal.{0}, c ≤ γ → γ < α →
        (¬ R1 x α → ¬ R1 x γ) ∧ (¬ R2 x α → ¬ R2 x γ) := by
  classical
  revert hX
  induction X using Finset.induction_on with
  | empty =>
    intro hX
    exact ⟨0, hα.pos, fun _ h => by simp at h,
      fun _ h => by simp at h⟩
  | @insert x X hxm ih =>
    intro hX
    have hx : x < α := hX x (Finset.mem_insert_self _ _)
    have hXS : ∀ y ∈ X, y < α := fun y hy => hX y (Finset.mem_insert_of_mem hy)
    obtain ⟨c, hc, below, negative⟩ := ih hXS
    have h1 : ∃ d : Ordinal.{0}, d < α ∧ ∀ γ : Ordinal.{0}, d ≤ γ → γ < α →
        (¬ R1 x α → ¬ R1 x γ) := by
      by_cases hR : R1 x α
      · exact ⟨0, hα.pos, fun _ _ _ hnot => False.elim (hnot hR)⟩
      · obtain ⟨d, hd, bound⟩ := R1_negative_bound α x hα hx hR
        exact ⟨d, hd, fun γ hdγ hγα _ => bound γ hdγ hγα⟩
    have h2 : ∃ d : Ordinal.{0}, d < α ∧ ∀ γ : Ordinal.{0}, d ≤ γ → γ < α →
        (¬ R2 x α → ¬ R2 x γ) := by
      by_cases hR : R2 x α
      · exact ⟨0, hα.pos, fun _ _ _ hnot => False.elim (hnot hR)⟩
      · obtain ⟨d, hd, bound⟩ := R2_negative_bound α x hα hx hR
        exact ⟨d, hd, fun γ hdγ hγα _ => bound γ hdγ hγα⟩
    obtain ⟨d₁, hd₁, bound₁⟩ := h1
    obtain ⟨d₂, hd₂, bound₂⟩ := h2
    let e := max c (max (x + 1) (max d₁ d₂))
    have hce : c ≤ e := le_max_left c (max (x + 1) (max d₁ d₂))
    have hxe : x + 1 ≤ e := (le_max_left (x + 1) (max d₁ d₂)).trans
      (le_max_right c (max (x + 1) (max d₁ d₂)))
    have hd₁e : d₁ ≤ e := (le_max_left d₁ d₂).trans
      ((le_max_right (x + 1) (max d₁ d₂)).trans
        (le_max_right c (max (x + 1) (max d₁ d₂))))
    have hd₂e : d₂ ≤ e := (le_max_right d₁ d₂).trans
      ((le_max_right (x + 1) (max d₁ d₂)).trans
        (le_max_right c (max (x + 1) (max d₁ d₂))))
    refine ⟨e, max_lt hc (max_lt (hα.add_one_lt hx) (max_lt hd₁ hd₂)), ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (lt_add_one y).trans_le hxe
      · exact (below y hy).trans_le hce
    · intro y hy γ heγ hγα
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨bound₁ γ (hd₁e.trans heγ) hγα, bound₂ γ (hd₂e.trans heγ) hγα⟩
      · exact negative y hy γ (hce.trans heγ) hγα

end Alexander313.Wilken.PureRelations
