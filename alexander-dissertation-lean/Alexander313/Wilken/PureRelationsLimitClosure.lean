import Alexander313.Wilken.PureRelationsTransitivity

/-!
# Actual closed upper classes for both pure relations

The first relation's interval closure turns any cofinal family of upper
relationships into a genuine right-limit relationship. For the second
relation, its upper Sigma2 witness fits in one smaller member of the cofinal
family. The universal block restricts there, and actual elementarity reflects
the witness. The forward direction follows from first-relation elementarity
by reflection of every alleged new universal counterexample. Thus BOTH upper
classes are closed under proper limits as in the source text before Lemma1.7.
No cofinality existence, relation or continuity oracle is supplied. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

theorem R1_antisymm {α β : Ordinal.{0}} (hab : R1 α β) (hba : R1 β α) : α = β :=
  le_antisymm (R1_le hab) (R1_le hba)

theorem R2_antisymm {α β : Ordinal.{0}} (hab : R2 α β) (hba : R2 β α) : α = β :=
  le_antisymm (R2_le hab) (R2_le hba)

/-- A genuinely cofinal family of actual first-relation upper endpoints
closes at its proper limit. Cofinality is the displayed family condition,
not an asserted existence of ordinal room. -/
theorem R1_cofinal_limit {α β : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (hαβ : α < β)
    (hcofinal : ∀ δ : Ordinal.{0}, δ < β →
      ∃ γ : Ordinal.{0}, γ < β ∧ δ ≤ γ ∧ R1 α γ) : R1 α β := by
  apply R1_limit hβ hαβ
  intro δ hαδ hδβ
  obtain ⟨γ, _, hδγ, hR⟩ := hcofinal δ hδβ
  exact R1_between hR hαδ hδγ

/-- Genuine right-limit closure for a cofinal family of the actual second
relation. Every finite existential block is bounded in one real family
member; the full universal block restricts to that member. -/
theorem R2_cofinal_limit {α β : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (hαβ : α < β)
    (hcofinal : ∀ δ : Ordinal.{0}, δ < β →
      ∃ γ : Ordinal.{0}, γ < β ∧ δ ≤ γ ∧ R2 α γ) : R2 α β := by
  have h1 : R1 α β := R1_cofinal_limit hβ hαβ (by
    intro δ hδ
    obtain ⟨γ, hγ, hδγ, hR⟩ := hcofinal δ hδ
    exact ⟨γ, hγ, hδγ, R2_R1 hR⟩)
  have he1 := ((R1_actual_iff α β).mp h1).2
  apply (R2_actual_iff α β).mpr
  refine ⟨hαβ.le, ?_⟩
  intro p m n φ v hv
  constructor
  · exact sigma2Truth_mono_of_sigma1 R1 R2 α β hαβ.le he1 p m n φ v hv
  · rintro ⟨w, hw, hφ⟩
    obtain ⟨δ, hδβ, hwδ⟩ := tupleBelow_limit_bounded β hβ w hw
    obtain ⟨γ, hγβ, hδγ, hR⟩ := hcofinal δ hδβ
    have he := ((R2_actual_iff α γ).mp hR).2
    exact (he p m n φ v hv).mpr
      ⟨w, tupleBelow_mono hδγ hwδ,
        fun z hz => hφ z (tupleBelow_mono hγβ.le hz)⟩

/-- The actual second relation is closed at every proper limit of its
intermediate upper relationships, matching the source closed-class claim. -/
theorem R2_limit {α β : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (hαβ : α < β)
    (hintermediate : ∀ γ : Ordinal.{0}, α ≤ γ → γ < β → R2 α γ) : R2 α β := by
  apply R2_cofinal_limit hβ hαβ
  intro δ hδβ
  have hγβ : max α δ < β := max_lt hαβ hδβ
  exact ⟨max α δ, hγβ, le_max_right α δ,
    hintermediate (max α δ) (le_max_left α δ) hγβ⟩

end Alexander313.Wilken.PureRelations
