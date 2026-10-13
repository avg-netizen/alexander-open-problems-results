import Alexander313.Carlson.ArithmeticLifting
import Alexander313.Carlson.DownwardExistence

/-!
# Existence of arithmetic liftings on rational labels

Carlson, *Patterns of resemblance of order 2*, Definition 11.1 and the
existence assertion of Lemma 11.4, pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 45–47 of the author's October 16, 2008 manuscript.

Every point of the source extension is assumed bounded above by a point of
the source base, as in Definition 11.1 and applications to continuous rules.
Each new point belongs to the block just below its least old upper bound.
Rational labels have room to copy that block just below the image of its
upper bound, above every earlier point of the target base.

The construction chooses an increasing placement of the finite source
extension below each target anchor, then uses each placement only on the
corresponding block. Empty bases and empty blocks need no separate assumption.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

/-- Every finite set of rational labels admits an increasing placement just
below a specified point of another finite set. The source set may be empty. -/
theorem exists_increasing_justBelow_rat (B X : Finset ℚ) {a : ℚ} (ha : a ∈ B) :
    ∃ f : ℚ → ℚ, (∀ x ∈ X, JustBelow B a (f x)) ∧
      (∀ x ∈ X, ∀ y ∈ X, x < y → f x < f y) := by
  classical
  by_cases hX : X.Nonempty
  · have hsingle : ∀ x ∈ ({a} : Finset ℚ), a ≤ x ∧ x < a + 1 := by
      intro x hx
      have hxa : x = a := Finset.mem_singleton.mp hx
      subst x
      exact ⟨le_rfl, by linarith⟩
    obtain ⟨N, g, hN, himage, _⟩ :=
      exists_copy_justBelow_rat B {a} (b := a + 1) ha (by linarith) hsingle
    have haimage : a ∈ N.image g := by
      rw [himage]
      exact Finset.mem_singleton_self a
    obtain ⟨c, hcN, _⟩ := Finset.mem_image.mp haimage
    have hc : JustBelow B a c := hN c hcN
    let l := X.min' hX
    let u := X.max' hX
    have hlu : l ≤ u := X.min'_le _ (X.max'_mem hX)
    have hden : 0 < u - l + 2 := by linarith
    let t : ℚ := (a - c) / (u - l + 2)
    have ht : 0 < t := div_pos (sub_pos.mpr hc.2.1) hden
    have htden : t * (u - l + 2) = a - c := div_mul_cancel₀ _ (ne_of_gt hden)
    let f : ℚ → ℚ := fun x => c + t * (x - l + 1)
    refine ⟨f, ?_, ?_⟩
    · intro x hx
      have hlx : l ≤ x := X.min'_le x hx
      have hxu : x ≤ u := X.le_max' x hx
      have hpos : 0 < t * (x - l + 1) := mul_pos ht (by linarith)
      have hlt : t * (x - l + 1) < t * (u - l + 2) :=
        mul_lt_mul_of_pos_left (by linarith) ht
      rw [htden] at hlt
      have hcf : c < f x := by
        dsimp only [f]
        linarith
      have hfa : f x < a := by
        dsimp only [f]
        linarith
      exact ⟨ha, hfa, fun q hq hqa => (hc.2.2 q hq hqa).trans hcf⟩
    · intro x _ y _ hxy
      have hlt : t * (x - l + 1) < t * (y - l + 1) :=
        mul_lt_mul_of_pos_left (by linarith) ht
      dsimp only [f]
      linarith
  · refine ⟨id, ?_, ?_⟩
    · intro x hx
      exact (hX ⟨x, hx⟩).elim
    · intro x hx y hy hxy
      exact (hX ⟨x, hx⟩).elim

end Str

namespace ArithmeticLifting

/-- Definition 11.1 and Lemma 11.4, existence in the bounded pure case:
a finite rational extension lifts along any increasing map of its base into
a finite rational target, without assuming the placement of new points. -/
theorem exists_rat {A Aplus B : Finset ℚ} {h : ℚ → ℚ}
    (hsub : A ⊆ Aplus)
    (hbounded : ∀ x ∈ Aplus, ∃ a ∈ A, x ≤ a)
    (hmono : ∀ x ∈ A, ∀ y ∈ A, x < y → h x < h y)
    (hmem : ∀ a ∈ A, h a ∈ B) :
    ∃ (Bplus : Finset ℚ) (f : ℚ → ℚ), ArithmeticLifting A Aplus B Bplus h f := by
  classical
  have placements : ∀ a : ℚ, ∃ p : ℚ → ℚ, a ∈ A →
      (∀ x ∈ Aplus, Str.JustBelow B (h a) (p x)) ∧
      (∀ x ∈ Aplus, ∀ y ∈ Aplus, x < y → p x < p y) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨p, hp, hm⟩ := Str.exists_increasing_justBelow_rat B Aplus (hmem a ha)
      exact ⟨p, fun _ => ⟨hp, hm⟩⟩
    · exact ⟨id, fun ha' => (ha ha').elim⟩
  let place : ℚ → ℚ → ℚ := fun a => Classical.choose (placements a)
  have hplace (a : ℚ) (ha : a ∈ A) :
      (∀ x ∈ Aplus, Str.JustBelow B (h a) (place a x)) ∧
      (∀ x ∈ Aplus, ∀ y ∈ Aplus, x < y → place a x < place a y) :=
    Classical.choose_spec (placements a) ha
  let f : ℚ → ℚ := fun x => if x ∈ A then h x else place (Str.up A x) x
  have f_old {x : ℚ} (hx : x ∈ A) : f x = h x := by
    simp only [f, if_pos hx]
  have f_new {x : ℚ} (hx : x ∉ A) : f x = place (Str.up A x) x := by
    simp only [f, if_neg hx]
  have copied {x : ℚ} (hx : x ∈ Aplus) (hxA : x ∉ A) :
      Str.JustBelow B (h (Str.up A x)) (f x) := by
    rw [f_new hxA]
    exact (hplace (Str.up A x) (Str.up_spec (hbounded x hx)).1).1 x hx
  have hfmono : ∀ x ∈ Aplus, ∀ y ∈ Aplus, x < y → f x < f y := by
    intro x hx y hy hxy
    have hpx := Str.up_spec (hbounded x hx)
    have hpy := Str.up_spec (hbounded y hy)
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · rw [f_old hxA, f_old hyA]
      exact hmono x hxA y hyA hxy
    · rw [f_old hxA]
      exact (copied hy hyA).2.2 (h x) (hmem x hxA)
        (hmono x hxA (Str.up A y) hpy.1 (hxy.trans_le hpy.2.1))
    · rw [f_old hyA]
      have hpyle : h (Str.up A x) ≤ h y := by
        rcases (hpx.2.2 y hyA hxy.le).lt_or_eq with hp | hp
        · exact (hmono (Str.up A x) hpx.1 y hyA hp).le
        · exact (congrArg h hp).le
      exact (copied hx hxA).2.1.trans_le hpyle
    · have hpq : Str.up A x ≤ Str.up A y :=
        Str.up_mono (hbounded x hx) (hbounded y hy) hxy.le
      rcases hpq.lt_or_eq with hpq | hpq
      · exact (copied hx hxA).2.1.trans
          ((copied hy hyA).2.2 (h (Str.up A x)) (hmem (Str.up A x) hpx.1)
            (hmono (Str.up A x) hpx.1 (Str.up A y) hpy.1 hpq))
      · rw [f_new hxA, f_new hyA, hpq]
        exact (hplace (Str.up A y) hpy.1).2 x hx y hy hxy
  refine ⟨B ∪ Aplus.image f, f, {
    source_sub := hsub
    source_bounded := hbounded
    base_mono := hmono
    base_mem := hmem
    target_sub := Finset.subset_union_left
    mono := hfmono
    mem := fun x hx => Finset.mem_union_right B (Finset.mem_image_of_mem f hx)
    agrees := fun x hx => f_old hx
    carrier_eq := rfl
    justBelow := ?_
  }⟩
  intro a x hx hax
  have hup : Str.up A x = a :=
    (Str.up_spec (hbounded x hx)).unique hax.leastGE
  have hcopy := copied hx hax.not_mem
  rwa [hup] at hcopy

end ArithmeticLifting

end Alexander313.Carlson
