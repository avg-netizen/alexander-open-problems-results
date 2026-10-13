import Alexander313.Effective.HereditaryOrdinalLabels

/-!
# The coherent genuine order of small hereditary ordinal labels

The named order uses actual ordinal values for its non-strict relation, and
literally the existing executing Bool comparison for its strict relation.
Both relations have concrete comparison decidability. No natural-code order
or semantic order oracle is used to decide them.

The carrier is a reducible subtype of `Nat`. We therefore keep the order as
a named object rather than introduce a competing global instance; local uses
pin its `LE`, the unchanged `LT`, and the full `LinearOrder` explicitly. The
value map is an order embedding and the previous genuine interval equivalence
is an order equivalence. This does not identify printed source spellings or
the actual finite-base supremum with the independently prescribed endpoint.
All proof terms remain uncompiled candidates.
-/

noncomputable section

namespace Alexander313.HereditaryOrdinalLabels

open Wilken.RelativeTerm.Hereditary

def labelLE : LE Label := ⟨fun μ ν => value μ ≤ value ν⟩

theorem labelLE_iff (μ ν : Label) :
    @LE.le Label labelLE μ ν ↔ value μ ≤ value ν := Iff.rfl

theorem labelLE_bool (μ ν : Label) :
    @LE.le Label labelLE μ ν ↔ Canonical.less ν.1 μ.1 = false := by
  change value μ ≤ value ν ↔ _
  rw [← not_lt, ← label_lt_iff]
  change (¬Canonical.less ν.1 μ.1 = true) ↔ Canonical.less ν.1 μ.1 = false
  cases h : Canonical.less ν.1 μ.1 <;> simp [h]

/-- Deciding non-strict order runs the real reverse strict comparison. -/
def labelLEDecidable (μ ν : Label) : Decidable (@LE.le Label labelLE μ ν) :=
  decidable_of_iff (Canonical.less ν.1 μ.1 = false) (labelLE_bool μ ν).symm

/-- Strict comparison is the existing executable Bool equality, unchanged. -/
def labelLTDecidable (μ ν : Label) : Decidable (@LT.lt Label labelLT μ ν) := by
  change Decidable (Canonical.less μ.1 ν.1 = true)
  infer_instance

@[reducible] def labelLinearOrder : LinearOrder Label where
  le := @LE.le Label labelLE
  lt := @LT.lt Label labelLT
  le_refl μ := show value μ ≤ value μ from le_rfl
  le_trans μ ν ξ hμν hνξ :=
    (show value μ ≤ value ν from hμν).trans (show value ν ≤ value ξ from hνξ)
  le_antisymm μ ν hμν hνμ := value_injective (le_antisymm hμν hνμ)
  lt_iff_le_not_ge μ ν := (label_lt_iff μ ν).trans
    (show value μ < value ν ↔ value μ ≤ value ν ∧ ¬value ν ≤ value μ from
      lt_iff_le_not_ge)
  le_total μ ν := le_total (value μ) (value ν)
  toDecidableLE := labelLEDecidable
  toDecidableLT := labelLTDecidable
  toDecidableEq := inferInstance
  min μ ν := @ite Label (@LE.le Label labelLE μ ν) (labelLEDecidable μ ν) μ ν
  max μ ν := @ite Label (@LE.le Label labelLE μ ν) (labelLEDecidable μ ν) ν μ
  compare μ ν := @compareOfLessAndEq Label μ ν labelLT (labelLTDecidable μ ν) inferInstance

theorem labelLinearOrder_toLE : labelLinearOrder.toLE = labelLE := rfl

theorem labelLinearOrder_toLT : labelLinearOrder.toLT = labelLT := rfl

theorem labelLinearOrder_le (μ ν : Label) :
    @LE.le Label labelLinearOrder.toLE μ ν ↔ value μ ≤ value ν := Iff.rfl

theorem labelLinearOrder_lt (μ ν : Label) :
    @LT.lt Label labelLinearOrder.toLT μ ν ↔ @LT.lt Label labelLT μ ν := Iff.rfl

theorem labelLinearOrder_lt_value (μ ν : Label) :
    @LT.lt Label labelLinearOrder.toLT μ ν ↔ value μ < value ν := label_lt_iff μ ν

theorem label_lt_wellFounded : WellFounded (@LT.lt Label labelLT) := by
  have hrel : @LT.lt Label labelLT =
      (fun μ ν : Label => value μ < value ν) := by
    funext μ ν
    exact propext (label_lt_iff μ ν)
  rw [hrel]
  exact InvImage.wf value Ordinal.lt_wf

theorem labelLinearOrder_wellFounded :
    WellFounded (@LT.lt Label labelLinearOrder.toLT) := label_lt_wellFounded

section GenuineOrder

local instance genuineLabelLE : LE Label := labelLE
local instance genuineLabelLT : LT Label := labelLT
local instance genuineLabelLinearOrder : LinearOrder Label := labelLinearOrder

theorem value_le_iff (μ ν : Label) : μ ≤ ν ↔ value μ ≤ value ν := Iff.rfl

theorem value_lt_iff (μ ν : Label) : μ < ν ↔ value μ < value ν := label_lt_iff μ ν

theorem value_eq_iff (μ ν : Label) : value μ = value ν ↔ μ = ν :=
  ⟨fun h => value_injective h, fun h => congrArg value h⟩

def valueOrderEmbedding : Label ↪o Ordinal.{0} where
  toFun := value
  inj' := value_injective
  map_rel_iff' := by
    intro μ ν
    rfl

@[simp] theorem valueOrderEmbedding_apply (μ : Label) :
    valueOrderEmbedding μ = value μ := rfl

theorem valueOrderEmbedding_range : Set.range valueOrderEmbedding = Set.Iio finiteBaseLimit := by
  ext ξ
  constructor
  · rintro ⟨μ, rfl⟩
    exact value_lt_limit μ
  · intro hξ
    exact value_covers ξ hξ

def intervalOrderEquiv : Label ≃o Set.Iio finiteBaseLimit where
  toEquiv := Canonical.intervalEquiv
  map_rel_iff' := by
    intro μ ν
    change value μ ≤ value ν ↔ value μ ≤ value ν
    rfl

@[simp] theorem intervalOrderEquiv_value (μ : Label) :
    (intervalOrderEquiv μ).1 = value μ := rfl

@[simp] theorem intervalOrderEquiv_symm_value (ξ : Set.Iio finiteBaseLimit) :
    value (intervalOrderEquiv.symm ξ) = ξ.1 := by
  have h := intervalOrderEquiv.apply_symm_apply ξ
  exact congrArg Subtype.val h

theorem zeroLabel_le (μ : Label) : zeroLabel ≤ μ := by
  change value zeroLabel ≤ value μ
  rw [zeroLabel_value]
  exact zero_le

theorem le_zeroLabel_iff (μ : Label) : μ ≤ zeroLabel ↔ μ = zeroLabel := by
  constructor
  · intro h
    exact value_injective (le_antisymm h (show value zeroLabel ≤ value μ from zeroLabel_le μ))
  · rintro rfl
    exact (show value zeroLabel ≤ value zeroLabel from le_rfl)

theorem value_eq_zero_iff (μ : Label) : value μ = 0 ↔ μ = zeroLabel := by
  rw [← zeroLabel_value, value_eq_iff]

theorem zeroLabel_lt_iff (μ : Label) : zeroLabel < μ ↔ μ ≠ zeroLabel := by
  rw [value_lt_iff, zeroLabel_value, pos_iff_ne_zero]
  exact not_congr (value_eq_zero_iff μ)

theorem value_pos_iff (μ : Label) : 0 < value μ ↔ μ ≠ zeroLabel := by
  rw [← zeroLabel_value, ← value_lt_iff, zeroLabel_lt_iff]

theorem label_interval_bounds (μ : Label) : 0 ≤ value μ ∧ value μ < finiteBaseLimit :=
  ⟨zero_le, value_lt_limit μ⟩

theorem labelOf_le_iff (c d : Nat) (hc : unionCheck c = true) (hd : unionCheck d = true) :
    labelOf c ≤ labelOf d ↔ unionInterpretation c ≤ unionInterpretation d := by
  rw [value_le_iff, labelOf_value c hc, labelOf_value d hd]

theorem label_below_cut_iff (μ : Label) (δ : Nat) (hδ : unionCheck δ = true) :
    μ < labelOf δ ↔ value μ < unionInterpretation δ := by
  rw [value_lt_iff, labelOf_value δ hδ]

end GenuineOrder
end Alexander313.HereditaryOrdinalLabels
