import Alexander313.Wilken.PureRelationsFiniteReflection
import Alexander313.FiniteCertificateTransport

/-!
# Actual small ordinal labels for the recorded reflection interface

Ordinal.{0} lives in Type1, whereas the original recorded syntax has a Type0
label parameter. For any actual ordinal upper bound Omega, its canonical
ToType is a Type0 well-order, with the genuine order isomorphism to [0,Omega).
The already constructed pure relations pull back along this actual map.
Semantic finite reflection gives the literal recorded-label reflection
interface on this constructed label type. No universe change, label-coverage
oracle or reflection contract is supplied.

The ToType presentation is classical. It is not the recursive hereditary
public Nat-code presentation; the effective adapter and separated/cofinal
source results remain separate. Uncompiled proof candidates.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SmallLabels

abbrev Labels (Ω : Ordinal.{0}) := Ω.ToType

def value (Ω : Ordinal.{0}) (x : Labels Ω) : Ordinal.{0} := (Ordinal.ToType.toOrd x).val

theorem value_lt (Ω : Ordinal.{0}) (x : Labels Ω) : value Ω x < Ω :=
  (Ordinal.ToType.toOrd x).property

def ofOrdinal (Ω ξ : Ordinal.{0}) (hξ : ξ < Ω) : Labels Ω := Ordinal.ToType.mk ⟨ξ, hξ⟩

theorem value_ofOrdinal (Ω ξ : Ordinal.{0}) (hξ : ξ < Ω) :
    value Ω (ofOrdinal Ω ξ hξ) = ξ :=
  congrArg Subtype.val ((Ordinal.ToType.mk (o := Ω)).symm_apply_apply ⟨ξ, hξ⟩)

theorem value_injective (Ω : Ordinal.{0}) : Function.Injective (value Ω) := by
  intro x y h
  apply (Ordinal.ToType.mk (o := Ω)).symm.injective
  exact Subtype.ext h

theorem value_lt_iff (Ω : Ordinal.{0}) (x y : Labels Ω) : value Ω x < value Ω y ↔ x < y :=
  (Ordinal.ToType.mk (o := Ω)).symm.lt_iff_lt

def first (Ω : Ordinal.{0}) (x y : Labels Ω) : Prop := R1 (value Ω x) (value Ω y)

def second (Ω : Ordinal.{0}) (x y : Labels Ω) : Prop := R2 (value Ω x) (value Ω y)

/-- The actual source R1 relationship on the constructed Type0 label order
supplies the EXACT recorded finite-pattern reflection proposition. -/
theorem finiteLabelReflection (Ω : Ordinal.{0}) (α β : Labels Ω) (hR : first Ω α β) :
    Alexander313.FiniteLabelReflection (first Ω) (second Ω) α β := by
  intro F below
  let V := F.image (value Ω)
  have source (μ : Labels Ω) (hμ : μ ∈ F) : value Ω μ ∈ V :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have all_below : ∀ ξ ∈ V, ξ < value Ω β := by
    intro ξ hξ
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hξ
    exact (value_lt_iff Ω μ β).mpr (below μ hμ)
  obtain ⟨g, lower, fixed, pattern⟩ :=
    PureRelations.finiteLabelReflection (value Ω α) (value Ω β) hR V all_below
  let f : Labels Ω → Labels Ω := fun μ => if hμ : μ ∈ F then
    ofOrdinal Ω (g (value Ω μ)) ((lower (value Ω μ) (source μ hμ)).trans (value_lt Ω α)) else μ
  have mapped (μ : Labels Ω) (hμ : μ ∈ F) : value Ω (f μ) = g (value Ω μ) := by
    simp only [f, dif_pos hμ, value_ofOrdinal]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro μ hμ
    apply (value_lt_iff Ω (f μ) α).mp
    rw [mapped μ hμ]
    exact lower (value Ω μ) (source μ hμ)
  · intro μ hμ hμα
    apply value_injective Ω
    exact (mapped μ hμ).trans
      (fixed (value Ω μ) (source μ hμ) ((value_lt_iff Ω μ α).mpr hμα))
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

theorem finiteLabelReflection_of_second (Ω : Ordinal.{0}) (α β : Labels Ω)
    (hR : second Ω α β) :
    Alexander313.FiniteLabelReflection (first Ω) (second Ω) α β :=
  finiteLabelReflection Ω α β (R2_R1 hR)

end Alexander313.Wilken.PureRelations.SmallLabels
