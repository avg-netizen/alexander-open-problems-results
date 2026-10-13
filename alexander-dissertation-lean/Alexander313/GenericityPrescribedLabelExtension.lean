import Alexander313.GenericityPrescribedLabelExtensionSupport
import Alexander313.Wilken.PureRelationsSmallLabels

/-!
# Whole guard reflection for the actual pure ordinal relations

The label order is the actual canonical Type0 presentation of ordinals below
Omega. The relations are the recursively constructed pure R1 and R2. Their
genuine Sigma1 finite-diagram argument supplies every reflection map used
here; no reflection, pattern-preservation or target-chain oracle is an input.

These lemmas start with actual bounded upper guard plans. They construct
shared lower marker sets and preserve all prescribed lower labels. Full
recorded formulas remain literally unchanged when their whole support is
prescribed. Fresh labels of a single source plan may instead move together.
Separated R2 room, a fixed plan for all source certificates, recursive public
Nat labels and whole-ideal soundness remain separate. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SmallLabels.Guards

theorem first_le (Ω : Ordinal.{0}) {α β : Labels Ω} (hR : first Ω α β) : α ≤ β := by
  apply le_of_not_gt
  intro h
  exact not_lt_of_ge (R1_le hR) ((value_lt_iff Ω β α).mpr h)

/-- All source-plan labels, complete R2 tails, both R1 endpoints and extra
certificate or prefix labels share ONE actual reflected finite map. -/
theorem reflected_relabelled_points_exists (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : first Ω α β) (p : GuardRequirements (Labels Ω)) (L K : Finset (Labels Ω))
    (bounded : GuardRequirements.Bounded (first Ω) (second Ω) β p)
    (parameters : ∀ μ ∈ GuardRequirements.support p, μ < β)
    (extra : ∀ μ ∈ L, μ < β) (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset (Labels Ω), ∃ f : Labels Ω → Labels Ω,
      GuardRequirements.Holds (first Ω) (second Ω) B p ∧ (∀ μ ∈ B, μ < β) ∧
      PreservesLabelPattern (first Ω) (second Ω) (B ∪ GuardRequirements.support p ∪ L ∪ K) f ∧
      (∀ μ ∈ K, f μ = μ) ∧
      GuardRequirements.Holds (first Ω) (second Ω) (B.image f) (GuardRequirements.relabel f p) ∧
      (∀ μ ∈ B ∪ GuardRequirements.support p ∪ L ∪ K, f μ < α) :=
  GuardRequirements.reflected_relabelled_points_exists (first Ω) (second Ω)
    (first_le Ω hR) (SmallLabels.finiteLabelReflection Ω α β hR)
    p L K bounded parameters extra prescribed

theorem bounded_relabel_reflect (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : first Ω α β) (p : GuardRequirements (Labels Ω)) (K : Finset (Labels Ω))
    (bounded : GuardRequirements.Bounded (first Ω) (second Ω) β p)
    (parameters : ∀ μ ∈ GuardRequirements.support p, μ < β)
    (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ f : Labels Ω → Labels Ω, (∀ μ ∈ K, f μ = μ) ∧
      GuardRequirements.Bounded (first Ω) (second Ω) α (GuardRequirements.relabel f p) :=
  GuardRequirements.bounded_relabel_reflect (first Ω) (second Ω)
    (first_le Ω hR) (SmallLabels.finiteLabelReflection Ω α β hR)
    p K bounded parameters prescribed

/-- Every original indexed request and edge stays unchanged when its whole
support lies below the actual lower endpoint of the constructed R1 pair. -/
theorem bounded_reflect (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : first Ω α β) (p : GuardRequirements (Labels Ω))
    (bounded : GuardRequirements.Bounded (first Ω) (second Ω) β p)
    (parameters : ∀ μ ∈ GuardRequirements.support p, μ < α) :
    GuardRequirements.Bounded (first Ω) (second Ω) α p :=
  GuardRequirements.bounded_reflect (first Ω) (second Ω)
    (first_le Ω hR) (SmallLabels.finiteLabelReflection Ω α β hR) p bounded parameters

theorem boundedGuardChain_reflect (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : first Ω α β) (k : Nat) (ν : Labels Ω)
    (chain : BoundedGuardChain (second Ω) β k ν) (base : ν < α) :
    BoundedGuardChain (second Ω) α k ν :=
  GuardRequirements.boundedGuardChain_reflect (first Ω) (second Ω)
    (first_le Ω hR) (SmallLabels.finiteLabelReflection Ω α β hR) k ν chain base

/-- Literal main guards reflect on the UNCHANGED full formula, including
every hidden live and ghost argument and any additional prescribed labels. -/
theorem mainGuarded_reflected_points_exists (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : first Ω α β) (E : Finset Nat) (φ : Formula (RecordedHead Nat (Labels Ω)))
    (K : Finset (Labels Ω))
    (bounded : GuardRequirements.Bounded (first Ω) (second Ω) β (φ.mainGuardRequirements E))
    (support : ∀ μ ∈ φ.labelSupport, μ < α) (prescribed : ∀ μ ∈ K, μ < α) :
    ∃ B : Finset (Labels Ω), ∃ f : Labels Ω → Labels Ω,
      φ.MainGuarded (first Ω) (second Ω) E B ∧ (∀ μ ∈ B, μ < β) ∧
      PreservesLabelPattern (first Ω) (second Ω) (B ∪ φ.labelSupport ∪ K) f ∧
      φ.relabel f = φ ∧ (∀ μ ∈ K, f μ = μ) ∧
      φ.MainGuarded (first Ω) (second Ω) E (B.image f) ∧ ∀ μ ∈ B.image f, μ < α :=
  Formula.mainGuarded_reflected_points_exists (first Ω) (second Ω)
    (first_le Ω hR) (SmallLabels.finiteLabelReflection Ω α β hR)
    E φ K bounded support prescribed

end Alexander313.Wilken.PureRelations.SmallLabels.Guards
