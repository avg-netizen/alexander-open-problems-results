import Alexander313.Carlson.Rules
import Alexander313.Carlson.FiniteOrderMaps

/-!
# Arithmetic liftings in the pure case

Carlson, *Patterns of resemblance of order 2*, Definition 11.1 and
Lemma 11.2, with the bounded hypotheses of Definition 11.1.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 44–46 of the author's October 16, 2008 manuscript.

For the pure base language `{≤}`, finite arithmetic structures are finite
linear orders, every point is indecomposable, and every subset is closed.
The lifting map extends an increasing map from `A` into `B`. Each new
source point just below `a ∈ A` is sent just below `h a` in `B`, and the
target consists of `B` together with the image of the extended source.

Definition 11.1(3) prints the lower target prefix with superscript `B⁺`.
Taken literally, that prefix contains the new image itself and contradicts
the displayed strict inequality. We use the old target `B`, as required by
the section's motivation and the placement in the proof of Lemma 11.4.

The boundedness hypothesis says that every point of the extended source
lies below an old source point. In particular, there is no unanchored block
above the whole source. This is the version used by continuous pattern
rules; the unrestricted upper-tail discussion in the proof of Lemma 11.4
is not needed here.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

namespace Str

/-- A point just below an old point has that point as its least old upper bound. -/
theorem JustBelow.leastGE {S : Finset α} {a x : α} (h : JustBelow S a x) :
    LeastGE S x a := by
  refine ⟨h.1, h.2.1.le, fun y hy hxy => ?_⟩
  by_contra hnot
  exact absurd hxy (not_le.mpr (h.2.2 y hy (not_le.mp hnot)))

theorem up_of_mem {S : Finset α} {x : α} (hx : x ∈ S) : up S x = x :=
  (up_spec ⟨x, hx, le_rfl⟩).unique ⟨hx, le_rfl, fun _ _ h => h⟩

/-- Taking the least old upper bound preserves order wherever it is defined. -/
theorem up_mono {S : Finset α} {x y : α}
    (hx : ∃ a ∈ S, x ≤ a) (hy : ∃ a ∈ S, y ≤ a) (hxy : x ≤ y) :
    up S x ≤ up S y :=
  (up_spec hx).2.2 _ (up_spec hy).1 (hxy.trans (up_spec hy).2.1)

/-- Every old point below the least old upper bound of `x` is below `x`. -/
theorem lt_of_lt_up {S : Finset α} {x a : α}
    (hx : ∃ p ∈ S, x ≤ p) (ha : a ∈ S) (hlt : a < up S x) : a < x := by
  by_contra hnot
  exact absurd ((up_spec hx).2.2 a ha (not_lt.mp hnot)) (not_le.mpr hlt)

end Str

/-- Definition 11.1 for finite pure arithmetic structures. The source and
target may use different ambient linear orders. -/
structure ArithmeticLifting (A Aplus : Finset α) (B Bplus : Finset β)
    (h f : α → β) : Prop where
  source_sub : A ⊆ Aplus
  source_bounded : ∀ x ∈ Aplus, ∃ a ∈ A, x ≤ a
  base_mono : ∀ x ∈ A, ∀ y ∈ A, x < y → h x < h y
  base_mem : ∀ x ∈ A, h x ∈ B
  target_sub : B ⊆ Bplus
  mono : ∀ x ∈ Aplus, ∀ y ∈ Aplus, x < y → f x < f y
  mem : ∀ x ∈ Aplus, f x ∈ Bplus
  agrees : ∀ x ∈ A, f x = h x
  carrier_eq : Bplus = B ∪ Aplus.image f
  justBelow : ∀ a x, x ∈ Aplus → Str.JustBelow A a x → Str.JustBelow B (h a) (f x)

namespace ArithmeticLifting

variable {A Aplus : Finset α} {B Bplus : Finset β} {h f : α → β}
  (D : ArithmeticLifting A Aplus B Bplus h f)
include D

theorem le_of_le {x y : α} (hx : x ∈ Aplus) (hy : y ∈ Aplus) (hxy : x ≤ y) :
    f x ≤ f y := by
  rcases hxy.lt_or_eq with hlt | rfl
  · exact (D.mono x hx y hy hlt).le
  · exact le_rfl

theorem le_iff {x y : α} (hx : x ∈ Aplus) (hy : y ∈ Aplus) :
    f x ≤ f y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra hnot
    exact absurd hxy (not_le.mpr (D.mono y hy x hx (not_le.mp hnot)))
  · exact D.le_of_le hx hy

/-- Injectivity is asserted only on the finite source carrier. -/
theorem injective {x y : α} (hx : x ∈ Aplus) (hy : y ∈ Aplus) (hxy : f x = f y) : x = y :=
  le_antisymm ((D.le_iff hx hy).mp hxy.le) ((D.le_iff hy hx).mp hxy.ge)

/-- Every new source point belongs to an anchored block. -/
theorem source_justBelow {x : α} (hx : x ∈ Aplus) (hxA : x ∉ A) :
    Str.JustBelow A (Str.up A x) x :=
  Str.justBelow_of_leastGE (Str.up_spec (D.source_bounded x hx)) hxA

theorem mapped_justBelow {x : α} (hx : x ∈ Aplus) (hxA : x ∉ A) :
    Str.JustBelow B (h (Str.up A x)) (f x) :=
  D.justBelow _ x hx (D.source_justBelow hx hxA)

/-- In the pure case new source points cannot be identified with old target points. -/
theorem new_not_mem {x : α} (hx : x ∈ Aplus) (hxA : x ∉ A) : f x ∉ B :=
  (D.mapped_justBelow hx hxA).not_mem

theorem image_mem_base_iff {x : α} (hx : x ∈ Aplus) : f x ∈ B ↔ x ∈ A := by
  constructor
  · intro hfx
    by_contra hxA
    exact D.new_not_mem hx hxA hfx
  · intro hxA
    rw [D.agrees x hxA]
    exact D.base_mem x hxA

/-- The new source points map exactly onto the new target points. -/
theorem tail_image : (Aplus \ A).image f = Bplus \ B := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx, hxA⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨D.mem x hx, D.new_not_mem hx hxA⟩
  · intro hy
    obtain ⟨hy, hyB⟩ := Finset.mem_sdiff.mp hy
    rw [D.carrier_eq] at hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (hyB hy).elim
    · obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      refine Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, ?_⟩, hxy⟩
      intro hxA
      apply hyB
      rw [← hxy, D.agrees x hxA]
      exact D.base_mem x hxA

theorem exists_new_preimage {y : β} (hy : y ∈ Bplus) (hyB : y ∉ B) :
    ∃ x ∈ Aplus, x ∉ A ∧ f x = y := by
  have hy' : y ∈ Bplus \ B := Finset.mem_sdiff.mpr ⟨hy, hyB⟩
  rw [← D.tail_image] at hy'
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy'
  exact ⟨x, (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2, hxy⟩

theorem tail_card : (Bplus \ B).card = (Aplus \ A).card := by
  rw [← D.tail_image]
  exact card_image_of_mono (Aplus \ A) f (fun x hx y hy hxy =>
    D.mono x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hxy)

/-- The lifted target has exactly one new point for each new source point. -/
theorem card_target : Bplus.card = B.card + (Aplus \ A).card := by
  classical
  calc
    Bplus.card = (Bplus \ B).card + B.card := by
      rw [Finset.card_sdiff_add_card, Finset.union_eq_left.mpr D.target_sub]
    _ = B.card + (Aplus \ A).card := by rw [D.tail_card, Nat.add_comm]

/-- The target also has no new maximum. -/
theorem target_bounded : ∀ y ∈ Bplus, ∃ b ∈ B, y ≤ b := by
  intro y hy
  rw [D.carrier_eq] at hy
  rcases Finset.mem_union.mp hy with hy | hy
  · exact ⟨y, hy, le_rfl⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a, ha, hxa⟩ := D.source_bounded x hx
    refine ⟨h a, D.base_mem a ha, ?_⟩
    rw [← D.agrees a ha]
    exact D.le_of_le hx (D.source_sub ha) hxa

/-- Least old upper bounds commute with the lifting map. -/
theorem leastGE_image {x a : α} (hx : x ∈ Aplus) (ha : Str.LeastGE A x a) :
    Str.LeastGE B (f x) (h a) := by
  by_cases hxA : x ∈ A
  · have hax : a = x := ha.unique ⟨hxA, le_rfl, fun _ _ h => h⟩
    rw [hax, D.agrees x hxA]
    exact ⟨D.base_mem x hxA, le_rfl, fun _ _ h => h⟩
  · exact (D.justBelow a x hx (Str.justBelow_of_leastGE ha hxA)).leastGE

theorem up_image {x : α} (hx : x ∈ Aplus) : Str.up B (f x) = h (Str.up A x) :=
  (Str.up_spec (D.target_bounded _ (D.mem x hx))).unique
    (D.leastGE_image hx (Str.up_spec (D.source_bounded x hx)))

/-- Comparisons between an old target point and a new image depend only on
the old upper endpoint of the source block. -/
theorem old_lt_image_iff {x : α} {y : β} (hx : x ∈ Aplus) (hxA : x ∉ A) (hy : y ∈ B) :
    y < f x ↔ y < h (Str.up A x) := by
  have hj := D.mapped_justBelow hx hxA
  exact ⟨fun hyx => hyx.trans hj.2.1, fun hya => hj.2.2 y hy hya⟩

theorem image_lt_old_iff {x : α} {y : β} (hx : x ∈ Aplus) (hxA : x ∉ A) (hy : y ∈ B) :
    f x < y ↔ h (Str.up A x) ≤ y := by
  have hj := D.mapped_justBelow hx hxA
  constructor
  · intro hxy
    by_contra hnot
    exact lt_asymm hxy (hj.2.2 y hy (not_le.mp hnot))
  · intro hay
    exact hj.2.1.trans_le hay

/-- Lemma 11.2, pure case: two lifting maps into the same finite target
agree at every point of the extended source. -/
theorem unique {g : α → β} (E : ArithmeticLifting A Aplus B Bplus h g)
    {x : α} (hx : x ∈ Aplus) : f x = g x := by
  by_cases hxA : x ∈ A
  · exact (D.agrees x hxA).trans (E.agrees x hxA).symm
  · have himage : (Aplus \ A).image f = (Aplus \ A).image g :=
      D.tail_image.trans E.tail_image.symm
    exact eqOn_of_strictMonoOn_image_eq
      (fun u hu v hv huv => D.mono u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 huv)
      (fun u hu v hv huv => E.mono u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 huv)
      himage x (Finset.mem_sdiff.mpr ⟨hx, hxA⟩)

end ArithmeticLifting

end Alexander313.Carlson
