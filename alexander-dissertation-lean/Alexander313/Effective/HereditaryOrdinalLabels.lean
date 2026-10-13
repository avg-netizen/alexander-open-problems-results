import Alexander313.Wilken.HereditaryCanonicalCodes

/-!
# Small labels for genuine hereditary ordinals

The frozen formula syntax takes labels in `Type 0`; `Ordinal.{0}` itself
lives in `Type 1`. Actual least accepted normal codes form a small carrier
with an injective genuine ordinal value and coverage of the proved finite-base
interval. Its explicit strict order is the executing canonical comparison.
No natural-number order on raw labels is installed.

The total label map canonicalizes old admitted union codes; malformed inputs
map to an actual canonical zero. Value fidelity is stated only on the original
union domain. This carrier does not identify printed structural normal forms
or the finite-base endpoint with the prescribed source endpoint.
-/

noncomputable section

namespace Alexander313.HereditaryOrdinalLabels

open Wilken.RelativeTerm.Hereditary

abbrev Label := Canonical.Code

def value : Label → Ordinal.{0} := Canonical.value

instance labelLT : LT Label := Canonical.orderLT

theorem label_lt_iff (μ ν : Label) : μ < ν ↔ value μ < value ν :=
  Canonical.code_lt_iff μ ν

theorem value_injective : Function.Injective value := Canonical.value_injective

theorem value_lt_limit (μ : Label) : value μ < finiteBaseLimit :=
  Canonical.value_lt_limit μ

theorem value_covers (ξ : Ordinal.{0}) (hξ : ξ < finiteBaseLimit) :
    ∃ μ : Label, value μ = ξ := Canonical.value_covers hξ

def zeroCode : Nat := Nat.pair 0 (zeroTree 0).code

theorem zeroCode_checked : unionCheck zeroCode = true := by
  simpa only [zeroCode, unionCheck_pair, lowCheckCode_code] using zeroTree_lowCheck 0

theorem zeroCode_value : unionInterpretation zeroCode = 0 := by
  simp only [zeroCode, unionInterpretation_pair, interpretation_code, zeroTree_denote]

def zeroLabel : Label :=
  ⟨Canonical.canonicalize zeroCode, Canonical.canonicalize_check zeroCode zeroCode_checked⟩

theorem zeroLabel_value : value zeroLabel = 0 :=
  (Canonical.canonicalize_value zeroCode zeroCode_checked).trans zeroCode_value

/-- Every admitted raw code maps to its genuine canonical representative.
The explicit malformed-input fallback is the represented ordinal zero. -/
def labelOf (c : Nat) : Label :=
  if hc : unionCheck c = true then
    ⟨Canonical.canonicalize c, Canonical.canonicalize_check c hc⟩ else zeroLabel

theorem labelOf_value (c : Nat) (hc : unionCheck c = true) :
    value (labelOf c) = unionInterpretation c := by
  simp only [labelOf, dif_pos hc, value, Canonical.value]
  exact Canonical.canonicalize_value c hc

theorem labelOf_rejected (c : Nat) (hc : unionCheck c = false) : labelOf c = zeroLabel := by
  have h : ¬unionCheck c = true := by rw [hc]; decide
  simp only [labelOf, dif_neg h]

theorem labelOf_code (μ : Label) : labelOf μ.1 = μ := by
  apply Subtype.ext
  have hμ := Canonical.check_original μ.2
  simp only [labelOf, dif_pos hμ]
  exact Canonical.check_fixed μ.2

theorem labelOf_lt_iff (c d : Nat) (hc : unionCheck c = true) (hd : unionCheck d = true) :
    labelOf c < labelOf d ↔ unionInterpretation c < unionInterpretation d := by
  rw [label_lt_iff, labelOf_value c hc, labelOf_value d hd]

theorem labelOf_eq_iff (c d : Nat) (hc : unionCheck c = true) (hd : unionCheck d = true) :
    labelOf c = labelOf d ↔ unionInterpretation c = unionInterpretation d := by
  constructor
  · intro h
    simpa only [labelOf_value c hc, labelOf_value d hd] using congrArg value h
  · intro h
    apply value_injective
    simpa only [labelOf_value c hc, labelOf_value d hd] using h

/-- Each genuine small ordinal label is literally represented by an admitted
old union code, with its label image exactly that label. -/
theorem original_code_covers (μ : Label) :
    ∃ c : Nat, unionCheck c = true ∧ labelOf c = μ :=
  ⟨μ.1, Canonical.check_original μ.2, labelOf_code μ⟩

theorem original_code_below_cut (δ : Nat) (hδ : unionCheck δ = true)
    (μ : Label) (hμ : μ < labelOf δ) :
    ∃ c : Nat, unionCheck c = true ∧ labelOf c = μ ∧
      unionInterpretation c < unionInterpretation δ := by
  obtain ⟨c, hc, he⟩ := original_code_covers μ
  refine ⟨c, hc, he, ?_⟩
  exact (labelOf_lt_iff c δ hc hδ).mp (by simpa only [he] using hμ)

end Alexander313.HereditaryOrdinalLabels
