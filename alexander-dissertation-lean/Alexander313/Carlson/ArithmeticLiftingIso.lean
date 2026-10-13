import Alexander313.Carlson.ArithmeticLifting

/-!
# Uniqueness of arithmetic liftings over the target base

Carlson, *Patterns of resemblance of order 2*, the uniqueness assertion of
Lemma 11.4, under the bounded hypotheses of Definition 11.1, pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 46–47 of the author's October 16, 2008 manuscript.

Two arithmetic liftings of the same source extension along the same base
map have isomorphic target orders. The isomorphism fixes the target base
pointwise and sends the first image of each source point to its second image.
It is presented as a total map with exact finite image and strict monotonicity,
matching the finite-carrier convention used for pattern isomorphisms.
-/

noncomputable section

namespace Alexander313.Carlson

namespace ArithmeticLifting

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
variable {A Aplus : Finset α} {B Bplus Cplus : Finset β} {h f g : α → β}

/-- The bounded pure case of Lemma 11.4: any two lifted target orders are
isomorphic over the target base, compatibly with their source lifting maps. -/
theorem exists_orderIso_over (D : ArithmeticLifting A Aplus B Bplus h f)
    (E : ArithmeticLifting A Aplus B Cplus h g) :
    ∃ j : β → β, Bplus.image j = Cplus ∧
      (∀ x ∈ Bplus, ∀ y ∈ Bplus, x < y → j x < j y) ∧
      (∀ y ∈ B, j y = y) ∧ (∀ x ∈ Aplus, j (f x) = g x) := by
  classical
  have pre : ∀ y, y ∈ Bplus \ B → ∃ x ∈ Aplus, x ∉ A ∧ f x = y := by
    intro y hy
    exact D.exists_new_preimage (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  let j : β → β := fun y =>
    if hy : y ∈ Bplus \ B then g (Classical.choose (pre y hy)) else y
  have j_old {y : β} (hy : y ∈ B) : j y = y := by
    simp only [j, dif_neg (fun hy' => (Finset.mem_sdiff.mp hy').2 hy)]
  have j_image {x : α} (hx : x ∈ Aplus) : j (f x) = g x := by
    by_cases hxA : x ∈ A
    · rw [D.agrees x hxA, j_old (D.base_mem x hxA), E.agrees x hxA]
    · have hfx : f x ∈ Bplus \ B :=
        Finset.mem_sdiff.mpr ⟨D.mem x hx, D.new_not_mem hx hxA⟩
      have hs := Classical.choose_spec (pre (f x) hfx)
      have heq : Classical.choose (pre (f x) hfx) = x :=
        D.injective hs.1 hx hs.2.2
      simp only [j, dif_pos hfx, heq]
  have old_lt {x : α} {y : β} (hx : x ∈ Aplus) (hy : y ∈ B) :
      y < f x ↔ y < g x := by
    by_cases hxA : x ∈ A
    · rw [D.agrees x hxA, E.agrees x hxA]
    · exact (D.old_lt_image_iff hx hxA hy).trans (E.old_lt_image_iff hx hxA hy).symm
  have lt_old {x : α} {y : β} (hx : x ∈ Aplus) (hy : y ∈ B) :
      f x < y ↔ g x < y := by
    by_cases hxA : x ∈ A
    · rw [D.agrees x hxA, E.agrees x hxA]
    · exact (D.image_lt_old_iff hx hxA hy).trans (E.image_lt_old_iff hx hxA hy).symm
  refine ⟨j, ?_, ?_, fun y hy => j_old hy, fun x hx => j_image hx⟩
  · have hB : B.image j = B := by
      calc
        B.image j = B.image id := Finset.image_congr fun y hy => j_old hy
        _ = B := Finset.image_id
    have hA : (Aplus.image f).image j = Aplus.image g := by
      rw [Finset.image_image]
      exact Finset.image_congr fun x hx => j_image hx
    rw [D.carrier_eq, Finset.image_union, hB, hA, ← E.carrier_eq]
  · intro u hu v hv huv
    rw [D.carrier_eq] at hu hv
    rcases Finset.mem_union.mp hu with hu | hu <;>
      rcases Finset.mem_union.mp hv with hv | hv
    · rw [j_old hu, j_old hv]
      exact huv
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      rw [j_old hu, j_image hy]
      exact (old_lt hy hu).mp huv
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      rw [j_image hx, j_old hv]
      exact (lt_old hx hv).mp huv
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      rw [j_image hx, j_image hy]
      have hxy : x < y := by
        by_contra hnot
        exact absurd huv (not_lt.mpr (D.le_of_le hy hx (not_lt.mp hnot)))
      exact E.mono x hx y hy hxy

end ArithmeticLifting

end Alexander313.Carlson
