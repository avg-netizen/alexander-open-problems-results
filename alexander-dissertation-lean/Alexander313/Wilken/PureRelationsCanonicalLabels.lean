import Alexander313.Effective.HereditaryOrdinalLinearOrder
import Alexander313.Wilken.FiniteUpsilonDomain
import Alexander313.Wilken.PureRelationsSmallCofinalCopies
import Alexander313.Wilken.PureRelationsSmallSeparatedCopies
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Actual pure relations on the existing canonical public codes

The carrier is EXACTLY the existing accepted canonical Nat-code subtype,
with its existing genuine executing order. The actual interval order
isomorphism supplies a genuine equivalence with finiteBaseLimit.ToType.
Consequently the already constructed pure relations supply full finite
reflection, cofinal upper copies and separated lower copies with endpoint
links on these very codes. Both positive AND negative expanded-pattern facts
are retained; the maps and room are conclusions.

The endpoint has countable cardinality and lies strictly below omega_1.
Thus an omega_1 semantic chain cannot furnish room inside this public bound.
The existing literal finite/omega source closure proves sourceUpsilonOmega
equals this very endpoint. No executing R1/R2 algorithm or source1.8 tracking
and resemblance correspondence is asserted. The canonical transport theorems
are checked by CompileOrdinalRoom.lean.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.CanonicalLabels

open Alexander313.HereditaryOrdinalLabels
open RelativeTerm.Hereditary (finiteBaseLimit)

local instance genuineLabelLE : LE Label := labelLE
local instance genuineLabelLT : LT Label := labelLT
local instance genuineLabelLinearOrder : LinearOrder Label := labelLinearOrder

/-- The existing genuine public codes, with their unchanged executing order,
are isomorphic to the whole proved finite-base interval's small well-order. -/
def smallOrderEquiv : Label ≃o SmallLabels.Labels finiteBaseLimit :=
  intervalOrderEquiv.trans (Ordinal.ToType.mk (o := finiteBaseLimit))

theorem small_value (μ : Label) :
    SmallLabels.value finiteBaseLimit (smallOrderEquiv μ) = value μ := by
  exact (congrArg Subtype.val
    ((Ordinal.ToType.mk (o := finiteBaseLimit)).symm_apply_apply (intervalOrderEquiv μ))).trans
      (intervalOrderEquiv_value μ)

theorem small_symm_value (x : SmallLabels.Labels finiteBaseLimit) :
    value (smallOrderEquiv.symm x) = SmallLabels.value finiteBaseLimit x := by
  rw [← small_value, smallOrderEquiv.apply_symm_apply]

/-- Explicit value comparison keeps the named executable label LT instance
aligned when transporting through the small-ordinal order isomorphism. -/
theorem small_lt_iff (μ ν : Label) :
    smallOrderEquiv μ < smallOrderEquiv ν ↔ μ < ν := by
  calc
    smallOrderEquiv μ < smallOrderEquiv ν ↔
        SmallLabels.value finiteBaseLimit (smallOrderEquiv μ) <
          SmallLabels.value finiteBaseLimit (smallOrderEquiv ν) :=
      (SmallLabels.value_lt_iff finiteBaseLimit _ _).symm
    _ ↔ value μ < value ν := by rw [small_value, small_value]
    _ ↔ μ < ν := (label_lt_iff μ ν).symm

/-- Actual recursively constructed ordinal first relation, on genuine codes. -/
def first (μ ν : Label) : Prop := R1 (value μ) (value ν)

/-- Actual recursively constructed ordinal second relation, on genuine codes. -/
def second (μ ν : Label) : Prop := R2 (value μ) (value ν)

theorem first_small_iff (μ ν : Label) :
    SmallLabels.first finiteBaseLimit (smallOrderEquiv μ) (smallOrderEquiv ν) ↔ first μ ν := by
  change R1 (SmallLabels.value finiteBaseLimit (smallOrderEquiv μ))
    (SmallLabels.value finiteBaseLimit (smallOrderEquiv ν)) ↔ R1 (value μ) (value ν)
  rw [small_value, small_value]

theorem second_small_iff (μ ν : Label) :
    SmallLabels.second finiteBaseLimit (smallOrderEquiv μ) (smallOrderEquiv ν) ↔ second μ ν := by
  change R2 (SmallLabels.value finiteBaseLimit (smallOrderEquiv μ))
    (SmallLabels.value finiteBaseLimit (smallOrderEquiv ν)) ↔ R2 (value μ) (value ν)
  rw [small_value, small_value]

/-- The actual public endpoint is countable, using the existing total interval
coverage and the genuine Nat-code subtype; no countability oracle is input. -/
theorem finiteBaseLimit_card_le_aleph0 : finiteBaseLimit.card ≤ Cardinal.aleph0 := by
  calc
    finiteBaseLimit.card = Cardinal.mk (SmallLabels.Labels finiteBaseLimit) :=
      (Cardinal.mk_toType finiteBaseLimit).symm
    _ = Cardinal.mk Label := (Cardinal.mk_congr smallOrderEquiv.toEquiv).symm
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0

/-- In particular the real public endpoint is below the first uncountable
ordinal, so room at omega_1 cannot be pulled into this interval. -/
theorem finiteBaseLimit_lt_omega_one : finiteBaseLimit < Ordinal.omega 1 := by
  rw [← Cardinal.ord_aleph]
  exact Cardinal.lt_ord.mpr (Cardinal.lt_aleph_one_iff.mpr finiteBaseLimit_card_le_aleph0)

/-- The whole genuine canonical carrier covers EXACTLY the actual source
finite/omega closure interval, using its already proved literal-grammar
endpoint identity rather than an assumed prescribed-endpoint alignment. -/
theorem value_range_sourceUpsilonOmega : Set.range value = Set.Iio sourceUpsilonOmega := by
  rw [sourceUpsilonOmega_eq_finiteBaseLimit]
  exact valueOrderEmbedding_range

theorem sourceUpsilonOmega_card_le_aleph0 : sourceUpsilonOmega.card ≤ Cardinal.aleph0 := by
  rw [sourceUpsilonOmega_eq_finiteBaseLimit]
  exact finiteBaseLimit_card_le_aleph0

theorem sourceUpsilonOmega_lt_omega_one : sourceUpsilonOmega < Ordinal.omega 1 := by
  rw [sourceUpsilonOmega_eq_finiteBaseLimit]
  exact finiteBaseLimit_lt_omega_one

/-- Conjugation returns every actual small copied point as a genuine existing
canonical code, rather than a raw Nat with an assumed value or guard. -/
def returnedMap (g : SmallLabels.Labels finiteBaseLimit → SmallLabels.Labels finiteBaseLimit)
    (μ : Label) : Label := smallOrderEquiv.symm (g (smallOrderEquiv μ))

theorem returnedMap_small
    (g : SmallLabels.Labels finiteBaseLimit → SmallLabels.Labels finiteBaseLimit) (μ : Label) :
    smallOrderEquiv (returnedMap g μ) = g (smallOrderEquiv μ) :=
  smallOrderEquiv.apply_symm_apply _

/-- One returned finite map preserves the WHOLE original expanded pattern,
including every negative equality/order/first/second fact. -/
theorem returnedMap_pattern (F : Finset Label)
    (g : SmallLabels.Labels finiteBaseLimit → SmallLabels.Labels finiteBaseLimit)
    (pattern : PreservesLabelPattern (SmallLabels.first finiteBaseLimit)
      (SmallLabels.second finiteBaseLimit) (F.image smallOrderEquiv) g) :
    PreservesLabelPattern first second F (returnedMap g) := by
  have source (μ : Label) (hμ : μ ∈ F) : smallOrderEquiv μ ∈ F.image smallOrderEquiv :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro μ hμ ν hν
    have hp := pattern.1 _ (source μ hμ) _ (source ν hν)
    rw [← returnedMap_small g μ, ← returnedMap_small g ν] at hp
    exact smallOrderEquiv.injective.eq_iff.symm.trans
      (hp.trans smallOrderEquiv.injective.eq_iff)
  · intro μ hμ ν hν
    have hp := pattern.2.1 _ (source μ hμ) _ (source ν hν)
    rw [← returnedMap_small g μ, ← returnedMap_small g ν] at hp
    exact (small_lt_iff _ _).symm.trans (hp.trans (small_lt_iff _ _))
  · intro μ hμ ν hν
    have hp := pattern.2.2.1 _ (source μ hμ) _ (source ν hν)
    rw [← returnedMap_small g μ, ← returnedMap_small g ν] at hp
    exact (first_small_iff (returnedMap g μ) (returnedMap g ν)).symm.trans
      (hp.trans (first_small_iff μ ν))
  · intro μ hμ ν hν
    have hp := pattern.2.2.2 _ (source μ hμ) _ (source ν hν)
    rw [← returnedMap_small g μ, ← returnedMap_small g ν] at hp
    exact (second_small_iff (returnedMap g μ) (returnedMap g ν)).symm.trans
      (hp.trans (second_small_iff μ ν))

/-- Actual first on the existing checked-code carrier derives the EXACT
frozen recorded-label finite reflection interface, with no supplied map. -/
theorem finiteLabelReflection (α β : Label) (hR : first α β) :
    Alexander313.FiniteLabelReflection first second α β := by
  intro F below
  have all_below : ∀ x ∈ F.image smallOrderEquiv, x < smallOrderEquiv β := by
    intro x hx
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hx
    exact (small_lt_iff _ _).mpr (below μ hμ)
  obtain ⟨g, lower, fixed, pattern⟩ :=
    SmallLabels.finiteLabelReflection finiteBaseLimit (smallOrderEquiv α) (smallOrderEquiv β)
      ((first_small_iff α β).mpr hR) (F.image smallOrderEquiv) all_below
  have source (μ : Label) (hμ : μ ∈ F) : smallOrderEquiv μ ∈ F.image smallOrderEquiv :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  refine ⟨returnedMap g, ?_, ?_, returnedMap_pattern F g pattern⟩
  · intro μ hμ
    apply (small_lt_iff _ _).mp
    rw [returnedMap_small]
    exact lower _ (source μ hμ)
  · intro μ hμ hμα
    apply smallOrderEquiv.injective
    exact (returnedMap_small g μ).trans
      (fixed _ (source μ hμ) ((small_lt_iff _ _).mpr hμα))

/-- Full source1.7(1) on the ORIGINAL canonical public codes: every original
lower code is fixed; upper codes are copied above ANY upper cutoff below beta;
the whole finite pattern, including all negatives, is preserved. -/
theorem finite_cofinal_copy (α β : Label) (hR : second α β) (hαβ : α < β)
    (X Y : Finset Label) (hX : ∀ x ∈ X, x < α)
    (hY : ∀ y ∈ Y, α ≤ y ∧ y < β) (hYn : Y.Nonempty) (c : Label) (hc : c < β) :
    ∃ f : Label → Label, PreservesLabelPattern first second (X ∪ Y) f ∧
      (∀ x ∈ X, f x = x) ∧ (∀ y ∈ Y, c < f y ∧ f y < β) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x < f y) := by
  let SX := X.image smallOrderEquiv
  let SY := Y.image smallOrderEquiv
  have sourceX (μ : Label) (hμ : μ ∈ X) : smallOrderEquiv μ ∈ SX :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have sourceY (μ : Label) (hμ : μ ∈ Y) : smallOrderEquiv μ ∈ SY :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have hSX : ∀ x ∈ SX, x < smallOrderEquiv α := by
    intro x hx
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hx
    exact (small_lt_iff _ _).mpr (hX μ hμ)
  have hSY : ∀ y ∈ SY, smallOrderEquiv α ≤ y ∧ y < smallOrderEquiv β := by
    intro y hy
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨smallOrderEquiv.le_iff_le.mpr (hY μ hμ).1,
      (small_lt_iff _ _).mpr (hY μ hμ).2⟩
  have hSYn : SY.Nonempty := by
    obtain ⟨μ, hμ⟩ := hYn
    exact ⟨smallOrderEquiv μ, sourceY μ hμ⟩
  obtain ⟨g, pattern, fixed, range, separated⟩ :=
    SmallLabels.CofinalCopies.finite_cofinal_copy finiteBaseLimit
      (smallOrderEquiv α) (smallOrderEquiv β) ((second_small_iff α β).mpr hR)
      ((small_lt_iff _ _).mpr hαβ) SX SY hSX hSY hSYn
      (smallOrderEquiv c) ((small_lt_iff _ _).mpr hc)
  have pattern' : PreservesLabelPattern (SmallLabels.first finiteBaseLimit)
      (SmallLabels.second finiteBaseLimit) ((X ∪ Y).image smallOrderEquiv) g := by
    simpa only [Finset.image_union] using pattern
  refine ⟨returnedMap g, returnedMap_pattern (X ∪ Y) g pattern', ?_, ?_, ?_⟩
  · intro μ hμ
    apply smallOrderEquiv.injective
    exact (returnedMap_small g μ).trans (fixed _ (sourceX μ hμ))
  · intro μ hμ
    have hm := range _ (sourceY μ hμ)
    constructor
    · apply (small_lt_iff _ _).mp
      rw [returnedMap_small]
      exact hm.1
    · apply (small_lt_iff _ _).mp
      rw [returnedMap_small]
      exact hm.2
  · intro μ hμ ν hν
    apply (small_lt_iff _ _).mp
    rw [returnedMap_small]
    exact separated _ (sourceX μ hμ) _ (sourceY ν hν)

/-- Full source1.7(2) on the ORIGINAL canonical public codes: a single map
copies upper points cofinally below alpha, fixes every lower point, preserves
all positive AND negative pattern facts, and retains designated endpoint
first-links. No semantic room or source tracking correspondence is assumed. -/
theorem finite_separated_copy (α β : Label) (hR : second α β) (hαβ : α < β)
    (X Y : Finset Label) (hX : ∀ x ∈ X, x < α)
    (hY : ∀ y ∈ Y, α ≤ y ∧ y < β) (c : Label) (hc : c < α) :
    ∃ f : Label → Label, PreservesLabelPattern first second (X ∪ Y) f ∧
      (∀ x ∈ X, f x = x) ∧ (∀ y ∈ Y, c < f y ∧ f y < α) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x < f y) ∧
      (∀ y ∈ Y, first y β → first (f y) α) := by
  let SX := X.image smallOrderEquiv
  let SY := Y.image smallOrderEquiv
  have sourceX (μ : Label) (hμ : μ ∈ X) : smallOrderEquiv μ ∈ SX :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have sourceY (μ : Label) (hμ : μ ∈ Y) : smallOrderEquiv μ ∈ SY :=
    Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have hSX : ∀ x ∈ SX, x < smallOrderEquiv α := by
    intro x hx
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hx
    exact (small_lt_iff _ _).mpr (hX μ hμ)
  have hSY : ∀ y ∈ SY, smallOrderEquiv α ≤ y ∧ y < smallOrderEquiv β := by
    intro y hy
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨smallOrderEquiv.le_iff_le.mpr (hY μ hμ).1,
      (small_lt_iff _ _).mpr (hY μ hμ).2⟩
  obtain ⟨g, pattern, fixed, range, separated, links⟩ :=
    SmallLabels.SeparatedCopies.finite_separated_copy finiteBaseLimit
      (smallOrderEquiv α) (smallOrderEquiv β) ((second_small_iff α β).mpr hR)
      ((small_lt_iff _ _).mpr hαβ) SX SY hSX hSY
      (smallOrderEquiv c) ((small_lt_iff _ _).mpr hc)
  have pattern' : PreservesLabelPattern (SmallLabels.first finiteBaseLimit)
      (SmallLabels.second finiteBaseLimit) ((X ∪ Y).image smallOrderEquiv) g := by
    simpa only [Finset.image_union] using pattern
  refine ⟨returnedMap g, returnedMap_pattern (X ∪ Y) g pattern', ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    apply smallOrderEquiv.injective
    exact (returnedMap_small g μ).trans (fixed _ (sourceX μ hμ))
  · intro μ hμ
    have hm := range _ (sourceY μ hμ)
    constructor
    · apply (small_lt_iff _ _).mp
      rw [returnedMap_small]
      exact hm.1
    · apply (small_lt_iff _ _).mp
      rw [returnedMap_small]
      exact hm.2
  · intro μ hμ ν hν
    apply (small_lt_iff _ _).mp
    rw [returnedMap_small]
    exact separated _ (sourceX μ hμ) _ (sourceY ν hν)
  · intro μ hμ hlink
    apply (first_small_iff (returnedMap g μ) α).mp
    rw [returnedMap_small]
    exact links _ (sourceY μ hμ) ((first_small_iff μ β).mpr hlink)

end Alexander313.Wilken.PureRelations.CanonicalLabels
