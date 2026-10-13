import Alexander313.Wilken.PureRelationsSeparatedCopies
import Alexander313.Wilken.PureRelationsSmallLabels
import Alexander313.GenericityPrescribedLabelExtensionSupport

/-!
# Actual separated copies and whole guard transport on small ordinal labels

The canonical Omega.ToType order carries the actual recursively constructed
pure relations. The genuine Sigma2 separated-copy theorem supplies all maps.
The guard theorem constructs actual marker points from the ORIGINAL bounded
chains, includes every request base and R1 edge endpoint, every extra label,
all prescribed lower support, and the actual base cut BEFORE own prefixes.
That same finite map derives boundedness at the transported actual cut.

Upper source plans remain actual displayed inputs; no fixed plan for an
unbounded certificate column, recursive public labeling or source soundness
is asserted. This uncompiled draft stays outside the package checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SmallLabels.SeparatedCopies

theorem value_le_iff (Ω : Ordinal.{0}) (x y : Labels Ω) : value Ω x ≤ value Ω y ↔ x ≤ y := by
  simpa only [not_lt] using not_congr (value_lt_iff Ω y x)

/-- Source Lemma1.7(2) in the EXACT original Type0 recorded-label universe,
using genuine canonical ordinal points and the actual pure first/second. -/
theorem finite_separated_copy (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : second Ω α β) (hαβ : α < β) (X Y : Finset (Labels Ω))
    (hX : ∀ x ∈ X, x < α) (hY : ∀ y ∈ Y, α ≤ y ∧ y < β)
    (c : Labels Ω) (hc : c < α) :
    ∃ f : Labels Ω → Labels Ω, PreservesLabelPattern (first Ω) (second Ω) (X ∪ Y) f ∧
      (∀ x ∈ X, f x = x) ∧ (∀ y ∈ Y, c < f y ∧ f y < α) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x < f y) ∧
      (∀ y ∈ Y, first Ω y β → first Ω (f y) α) := by
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
  obtain ⟨g, pattern, fixed, range, separated, links⟩ :=
    PureRelations.SeparatedCopies.finite_separated_copy (value Ω α) (value Ω β) hR
      ((value_lt_iff Ω α β).mpr hαβ) VX VY hVX hVY (value Ω c)
      ((value_lt_iff Ω c α).mpr hc)
  have source (μ : Labels Ω) (hμ : μ ∈ X ∪ Y) : value Ω μ ∈ VX ∪ VY := by
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · exact Finset.mem_union.mpr (Or.inl (sourceX μ hμ))
    · exact Finset.mem_union.mpr (Or.inr (sourceY μ hμ))
  have lower (μ : Labels Ω) (hμ : μ ∈ X ∪ Y) : g (value Ω μ) < value Ω α := by
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rw [fixed _ (sourceX μ hμ)]
      exact (value_lt_iff Ω μ α).mpr (hX μ hμ)
    · exact (range _ (sourceY μ hμ)).2
  let f : Labels Ω → Labels Ω := fun μ => if hμ : μ ∈ X ∪ Y then
    ofOrdinal Ω (g (value Ω μ)) ((lower μ hμ).trans (value_lt Ω α)) else μ
  have mapped (μ : Labels Ω) (hμ : μ ∈ X ∪ Y) : value Ω (f μ) = g (value Ω μ) := by
    simp only [f, dif_pos hμ, value_ofOrdinal]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
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
    · apply (value_lt_iff Ω (f μ) α).mp
      rw [hm]
      exact (range _ (sourceY μ hμ)).2
  · intro μ hμ ν hν
    apply (value_lt_iff Ω μ (f ν)).mp
    rw [mapped ν (Finset.mem_union.mpr (Or.inr hν))]
    exact separated _ (sourceX μ hμ) _ (sourceY ν hν)
  · intro μ hμ hlink
    change R1 (value Ω (f μ)) (value Ω α)
    rw [mapped μ (Finset.mem_union.mpr (Or.inr hμ))]
    exact links _ (sourceY μ hμ) hlink

private theorem copied_pattern (Ω : Ordinal.{0}) (α β c : Labels Ω)
    (hR : second Ω α β) (hαβ : α < β) (hc : c < α) (F K : Finset (Labels Ω))
    (all_below : ∀ μ ∈ F, μ < β) (hKF : K ⊆ F) (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ f : Labels Ω → Labels Ω, PreservesLabelPattern (first Ω) (second Ω) F f ∧
      (∀ μ ∈ K, f μ = μ) ∧ (∀ μ ∈ F, f μ < α) ∧
      (∀ μ ∈ F, α ≤ μ → c < f μ) ∧
      (∀ μ ∈ F, first Ω μ β → first Ω (f μ) α) := by
  let X := F.filter (fun μ => μ < α)
  let Y := F.filter (fun μ => ¬ μ < α)
  have hXY : X ∪ Y = F := by
    ext μ
    simp only [X, Y, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
    · intro hm
      by_cases h : μ < α
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, h⟩
  obtain ⟨f, pattern, fixed, range, _, links⟩ := finite_separated_copy Ω α β hR hαβ X Y
    (fun μ hμ => (Finset.mem_filter.mp hμ).2)
    (fun μ hμ => ⟨not_lt.mp (Finset.mem_filter.mp hμ).2,
      all_below μ (Finset.mem_filter.mp hμ).1⟩) c hc
  rw [hXY] at pattern
  refine ⟨f, pattern, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    exact fixed μ (Finset.mem_filter.mpr ⟨hKF hμ, prescribed μ hμ⟩)
  · intro μ hμ
    by_cases hμα : μ < α
    · rw [fixed μ (Finset.mem_filter.mpr ⟨hμ, hμα⟩)]
      exact hμα
    · exact (range μ (Finset.mem_filter.mpr ⟨hμ, hμα⟩)).2
  · intro μ hμ hαμ
    exact (range μ (Finset.mem_filter.mpr ⟨hμ, not_lt_of_ge hαμ⟩)).1
  · intro μ hμ hlink
    by_cases hμα : μ < α
    · rw [fixed μ (Finset.mem_filter.mpr ⟨hμ, hμα⟩)]
      exact R1_between hlink ((value_lt_iff Ω μ α).mpr hμα).le
        ((value_lt_iff Ω α β).mpr hαβ).le
    · exact links μ (Finset.mem_filter.mpr ⟨hμ, hμα⟩) hlink

/-- ONE actual separated map transports a whole finite source plan at its
own original base-row cut, before own prefixes. Every copied marker lies
below the copied cut, every fresh support point lies above the prescribed
cutoff, and every designated R1 connection to the upper endpoint survives.
The upper bounded plan is input data; target chains and maps are conclusions. -/
theorem guard_plan_at_cut (Ω : Ordinal.{0}) (α β δ c : Labels Ω)
    (hR : second Ω α β) (hαβ : α < β) (hδβ : δ < β) (hc : c < α)
    (p : GuardRequirements (Labels Ω)) (L K : Finset (Labels Ω))
    (bounded : GuardRequirements.Bounded (first Ω) (second Ω) δ p)
    (parameters : ∀ μ ∈ GuardRequirements.support p, μ < β)
    (extra : ∀ μ ∈ L, μ < β) (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset (Labels Ω), ∃ f : Labels Ω → Labels Ω,
      GuardRequirements.Holds (first Ω) (second Ω) B p ∧ (∀ μ ∈ B, μ < δ) ∧
      PreservesLabelPattern (first Ω) (second Ω)
        (B ∪ GuardRequirements.support p ∪ L ∪ K ∪ {δ}) f ∧
      (∀ μ ∈ K, f μ = μ) ∧
      GuardRequirements.Bounded (first Ω) (second Ω) (f δ) (GuardRequirements.relabel f p) ∧
      f δ < α ∧
      (∀ μ ∈ B ∪ GuardRequirements.support p ∪ L ∪ K ∪ {δ}, α ≤ μ → c < f μ) ∧
      (∀ μ ∈ B ∪ GuardRequirements.support p ∪ L ∪ K ∪ {δ},
        first Ω μ β → first Ω (f μ) α) := by
  obtain ⟨B, holds, room⟩ := (GuardRequirements.bounded_iff_holds_room
    (first Ω) (second Ω) δ p).mp bounded
  let F := B ∪ GuardRequirements.support p ∪ L ∪ K ∪ {δ}
  have points : B ⊆ F := fun μ hμ => Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl hμ)))))))
  have support : GuardRequirements.support p ⊆ F := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hμ)))))))
  have cut : δ ∈ F := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
  have all_below : ∀ μ ∈ F, μ < β := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rcases Finset.mem_union.mp hμ with hμ | hμ
      · rcases Finset.mem_union.mp hμ with hμ | hμ
        · rcases Finset.mem_union.mp hμ with hμ | hμ
          · exact (room μ hμ).trans hδβ
          · exact parameters μ hμ
        · exact extra μ hμ
      · exact (prescribed μ hμ).trans hαβ
    · have he : μ = δ := Finset.mem_singleton.mp hμ
      simpa only [he] using hδβ
  have hKF : K ⊆ F := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hμ)))
  obtain ⟨f, pattern, fixed, lower, fresh, links⟩ :=
    copied_pattern Ω α β c hR hαβ hc F K all_below hKF prescribed
  exact ⟨B, f, holds, room, pattern, fixed,
    GuardRequirements.cut_relabel (first Ω) (second Ω) p B F δ f
      holds room pattern points support cut, lower δ cut, fresh, links⟩

/-- The OUTER source cut equals the upper endpoint. That endpoint is never
inserted illegally into a finite set below itself: the actual transported
marker points directly lie below alpha, which is the genuine target cut. -/
theorem guard_plan_at_outer_cut (Ω : Ordinal.{0}) (α β c : Labels Ω)
    (hR : second Ω α β) (hαβ : α < β) (hc : c < α)
    (p : GuardRequirements (Labels Ω)) (L K : Finset (Labels Ω))
    (bounded : GuardRequirements.Bounded (first Ω) (second Ω) β p)
    (parameters : ∀ μ ∈ GuardRequirements.support p, μ < β)
    (extra : ∀ μ ∈ L, μ < β) (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset (Labels Ω), ∃ f : Labels Ω → Labels Ω,
      GuardRequirements.Holds (first Ω) (second Ω) B p ∧ (∀ μ ∈ B, μ < β) ∧
      PreservesLabelPattern (first Ω) (second Ω)
        (B ∪ GuardRequirements.support p ∪ L ∪ K) f ∧
      (∀ μ ∈ K, f μ = μ) ∧
      GuardRequirements.Bounded (first Ω) (second Ω) α (GuardRequirements.relabel f p) ∧
      (∀ μ ∈ B ∪ GuardRequirements.support p ∪ L ∪ K, α ≤ μ → c < f μ) ∧
      (∀ μ ∈ B ∪ GuardRequirements.support p ∪ L ∪ K,
        first Ω μ β → first Ω (f μ) α) := by
  obtain ⟨B, holds, room⟩ := (GuardRequirements.bounded_iff_holds_room
    (first Ω) (second Ω) β p).mp bounded
  let F := B ∪ GuardRequirements.support p ∪ L ∪ K
  have points : B ⊆ F := fun μ hμ => Finset.mem_union.mpr (Or.inl
    (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hμ)))))
  have support : GuardRequirements.support p ⊆ F := fun μ hμ =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inr hμ)))))
  have hKF : K ⊆ F := fun μ hμ => Finset.mem_union.mpr (Or.inr hμ)
  have all_below : ∀ μ ∈ F, μ < β := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · rcases Finset.mem_union.mp hμ with hμ | hμ
      · rcases Finset.mem_union.mp hμ with hμ | hμ
        · exact room μ hμ
        · exact parameters μ hμ
      · exact extra μ hμ
    · exact (prescribed μ hμ).trans hαβ
  obtain ⟨f, pattern, fixed, lower, fresh, links⟩ :=
    copied_pattern Ω α β c hR hαβ hc F K all_below hKF prescribed
  refine ⟨B, f, holds, room, pattern, fixed,
    (GuardRequirements.bounded_iff_holds_room (first Ω) (second Ω) α
      (GuardRequirements.relabel f p)).mpr ⟨B.image f, ?_, ?_⟩, fresh, links⟩
  · constructor
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact GuardChainIn.relabel (holds.1 r hr) f pattern.covers points
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hl := support (GuardRequirements.edge_left_mem_support p r hr)
      have hr' := support (GuardRequirements.edge_right_mem_support p r hr)
      exact ⟨(pattern.2.1 _ hl _ hr').mpr (holds.2 r hr).1,
        (pattern.2.2.1 _ hl _ hr').mpr (holds.2 r hr).2⟩
  · intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    exact lower ν (points hν)

end Alexander313.Wilken.PureRelations.SmallLabels.SeparatedCopies
