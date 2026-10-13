import Alexander313.Wilken.PureRelationsCofinalCopies
import Alexander313.Wilken.PureRelationsSmallLabels

/-!
# Genuine cofinal upper copies on the original small ordinal label type

The actual recursively constructed pure first/second relations on Omega.ToType
inherit source Lemma1.7(1) through the canonical order isomorphism. Every
original lower label stays fixed, every positive AND negative expanded-pattern
fact is retained, and every copied upper label lies above the arbitrary beta
cutoff and below beta. No copy map, recursive label decision or cofinal room
oracle is supplied. These uncompiled candidates stay outside the checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SmallLabels.CofinalCopies

private theorem value_le_iff (Ω : Ordinal.{0}) (x y : Labels Ω) :
    value Ω x ≤ value Ω y ↔ x ≤ y := by
  simpa only [not_lt] using not_congr (value_lt_iff Ω y x)

/-- Full printed source Lemma1.7(1) on the EXACT original Type0 recorded
label universe, with the original nonempty upper pattern and arbitrary upper
cutoff. Its actual expanded-pattern map is constructed, not supplied. -/
theorem finite_cofinal_copy (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : second Ω α β) (hαβ : α < β) (X Y : Finset (Labels Ω))
    (hX : ∀ x ∈ X, x < α) (hY : ∀ y ∈ Y, α ≤ y ∧ y < β) (hYn : Y.Nonempty)
    (c : Labels Ω) (hc : c < β) :
    ∃ f : Labels Ω → Labels Ω, PreservesLabelPattern (first Ω) (second Ω) (X ∪ Y) f ∧
      (∀ x ∈ X, f x = x) ∧ (∀ y ∈ Y, c < f y ∧ f y < β) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x < f y) := by
  let VX := X.image (value Ω)
  let VY := Y.image (value Ω)
  have sourceX (μ : Labels Ω) (hμ : μ ∈ X) : value Ω μ ∈ VX :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have sourceY (μ : Labels Ω) (hμ : μ ∈ Y) : value Ω μ ∈ VY :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have hVX : ∀ ξ ∈ VX, ξ < value Ω α := by
    intro ξ hξ
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hξ
    exact (value_lt_iff Ω μ α).mpr (hX μ hμ)
  have hVY : ∀ ξ ∈ VY, value Ω α ≤ ξ ∧ ξ < value Ω β := by
    intro ξ hξ
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hξ
    exact ⟨(value_le_iff Ω α μ).mpr (hY μ hμ).1,
      (value_lt_iff Ω μ β).mpr (hY μ hμ).2⟩
  have hVYn : VY.Nonempty := by
    obtain ⟨μ, hμ⟩ := hYn
    exact ⟨value Ω μ, sourceY μ hμ⟩
  obtain ⟨g, pattern, fixed, range, separated⟩ :=
    PureRelations.CofinalCopies.finite_cofinal_copy (value Ω α) (value Ω β) hR
      ((value_lt_iff Ω α β).mpr hαβ) VX VY hVX hVY hVYn (value Ω c)
      ((value_lt_iff Ω c β).mpr hc)
  have source (μ : Labels Ω) (hμ : μ ∈ X ∪ Y) : value Ω μ ∈ VX ∪ VY := by
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · exact Finset.mem_union.mpr (Or.inl (sourceX μ hμ))
    · exact Finset.mem_union.mpr (Or.inr (sourceY μ hμ))
  have lower (μ : Labels Ω) (hμ : μ ∈ X ∪ Y) : g (value Ω μ) < value Ω β := by
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rw [fixed _ (sourceX μ hμ)]
      exact (value_lt_iff Ω μ β).mpr ((hX μ hμ).trans hαβ)
    · exact (range _ (sourceY μ hμ)).2
  let f : Labels Ω → Labels Ω := fun μ => if hμ : μ ∈ X ∪ Y then
    ofOrdinal Ω (g (value Ω μ)) ((lower μ hμ).trans (value_lt Ω β)) else μ
  have mapped (μ : Labels Ω) (hμ : μ ∈ X ∪ Y) : value Ω (f μ) = g (value Ω μ) := by
    simp only [f, dif_pos hμ, value_ofOrdinal]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro μ hμ ν hν
      have hv : value Ω (f μ) = value Ω (f ν) ↔ value Ω μ = value Ω ν := by
        rw [mapped μ hμ, mapped ν hν]
        exact pattern.1 _ (source μ hμ) _ (source ν hν)
      exact (value_injective Ω).eq_iff.symm.trans (hv.trans (value_injective Ω).eq_iff)
    · intro μ hμ ν hν
      have hv : value Ω (f μ) < value Ω (f ν) ↔ value Ω μ < value Ω ν := by
        rw [mapped μ hμ, mapped ν hν]
        exact pattern.2.1 _ (source μ hμ) _ (source ν hν)
      exact (value_lt_iff Ω (f μ) (f ν)).symm.trans (hv.trans (value_lt_iff Ω μ ν))
    · intro μ hμ ν hν
      change R1 (value Ω (f μ)) (value Ω (f ν)) ↔ R1 (value Ω μ) (value Ω ν)
      rw [mapped μ hμ, mapped ν hν]
      exact pattern.2.2.1 _ (source μ hμ) _ (source ν hν)
    · intro μ hμ ν hν
      change R2 (value Ω (f μ)) (value Ω (f ν)) ↔ R2 (value Ω μ) (value Ω ν)
      rw [mapped μ hμ, mapped ν hν]
      exact pattern.2.2.2 _ (source μ hμ) _ (source ν hν)
  · intro μ hμ
    apply value_injective Ω
    exact (mapped μ (Finset.mem_union.mpr (Or.inl hμ))).trans (fixed _ (sourceX μ hμ))
  · intro μ hμ
    have hm := mapped μ (Finset.mem_union.mpr (Or.inr hμ))
    constructor
    · apply (value_lt_iff Ω c (f μ)).mp
      rw [hm]
      exact (range _ (sourceY μ hμ)).1
    · apply (value_lt_iff Ω (f μ) β).mp
      rw [hm]
      exact (range _ (sourceY μ hμ)).2
  · intro μ hμ ν hν
    apply (value_lt_iff Ω μ (f ν)).mp
    rw [mapped ν (Finset.mem_union.mpr (Or.inr hν))]
    exact separated _ (sourceX μ hμ) _ (sourceY ν hν)

end Alexander313.Wilken.PureRelations.SmallLabels.CofinalCopies
