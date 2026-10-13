import Alexander313.Carlson.ArithmeticLifting
import Alexander313.Carlson.ComputableAnchors
import Mathlib.Tactic.Linarith

/-!
# Computable arithmetic liftings on rational labels

The bounded pure arithmetic lifting can be computed directly from its finite
source and target carriers. For an anchor `a`, `Str.computablePredBound B a`
finds the greatest old target point below `a`, using `a - 1` if there is no
such point. A positive affine map puts the finite source strictly between
this bound and `a`. The lifting uses that map at each point's computed least
old upper anchor and retains the prescribed map on old source points.

All data-producing definitions in this file are executable. Their proofs
may use classical reasoning, but computation uses only finite rational
minimum, maximum, membership, and arithmetic operations. The correctness
theorem has exactly the bounded hypotheses of `ArithmeticLifting.exists_rat`;
no source or target nonemptiness assumption is needed.
-/

namespace Alexander313.Carlson

namespace Str

/-- A computable lower boundary for the gap before `a`: the greatest old
point below `a`, or `a - 1` if there is no such point. -/
def computablePredBound (B : Finset ℚ) (a : ℚ) : ℚ :=
  let T := B.filter (fun p => p < a)
  if hT : T.Nonempty then T.max' hT else a - 1

/-- The computed boundary is strictly below the anchor and weakly above
every old point below that anchor. The anchor need not belong to `B`. -/
theorem computablePredBound_spec (B : Finset ℚ) (a : ℚ) :
    computablePredBound B a < a ∧
      ∀ q ∈ B, q < a → q ≤ computablePredBound B a := by
  let T := B.filter (fun p => p < a)
  change (if hT : T.Nonempty then T.max' hT else a - 1) < a ∧
    ∀ q ∈ B, q < a → q ≤ (if hT : T.Nonempty then T.max' hT else a - 1)
  by_cases hT : T.Nonempty
  · simp only [dif_pos hT]
    refine ⟨(Finset.mem_filter.mp (T.max'_mem hT)).2, ?_⟩
    intro q hq hqa
    exact T.le_max' q (Finset.mem_filter.mpr ⟨hq, hqa⟩)
  · simp only [dif_neg hT]
    refine ⟨by linarith, ?_⟩
    intro q hq hqa
    exact (hT ⟨q, Finset.mem_filter.mpr ⟨hq, hqa⟩⟩).elim

/-- A deterministic increasing placement of `X` in the open gap before
`a`. An empty source uses the identity function. -/
def computablePlaceBelow (B X : Finset ℚ) (a x : ℚ) : ℚ :=
  if hX : X.Nonempty then
    let c := computablePredBound B a
    let l := X.min' hX
    let u := X.max' hX
    c + ((a - c) / (u - l + 2)) * (x - l + 1)
  else x

@[simp] theorem computablePlaceBelow_empty (B : Finset ℚ) (a x : ℚ) :
    computablePlaceBelow B ∅ a x = x := by
  simp [computablePlaceBelow]

/-- Computed affine placement puts every source point just below its
anchor and preserves strict order on the source carrier. -/
theorem computablePlaceBelow_spec (B X : Finset ℚ) {a : ℚ} (ha : a ∈ B) :
    (∀ x ∈ X, JustBelow B a (computablePlaceBelow B X a x)) ∧
      (∀ x ∈ X, ∀ y ∈ X, x < y →
        computablePlaceBelow B X a x < computablePlaceBelow B X a y) := by
  by_cases hX : X.Nonempty
  · let c := computablePredBound B a
    let l := X.min' hX
    let u := X.max' hX
    have hc : c < a ∧ ∀ q ∈ B, q < a → q ≤ c := computablePredBound_spec B a
    have hlu : l ≤ u := X.min'_le _ (X.max'_mem hX)
    have hden : 0 < u - l + 2 := by linarith
    let t : ℚ := (a - c) / (u - l + 2)
    have ht : 0 < t := div_pos (sub_pos.mpr hc.1) hden
    have htden : t * (u - l + 2) = a - c := div_mul_cancel₀ _ (ne_of_gt hden)
    have hformula (x : ℚ) :
        computablePlaceBelow B X a x = c + t * (x - l + 1) := by
      simp only [computablePlaceBelow, dif_pos hX]
      rfl
    constructor
    · intro x hx
      have hlx : l ≤ x := X.min'_le x hx
      have hxu : x ≤ u := X.le_max' x hx
      have hpos : 0 < t * (x - l + 1) := mul_pos ht (by linarith)
      have hlt : t * (x - l + 1) < t * (u - l + 2) :=
        mul_lt_mul_of_pos_left (by linarith) ht
      rw [htden] at hlt
      have hcf : c < computablePlaceBelow B X a x := by
        rw [hformula]
        linarith
      have hfa : computablePlaceBelow B X a x < a := by
        rw [hformula]
        linarith
      exact ⟨ha, hfa, fun q hq hqa => (hc.2 q hq hqa).trans_lt hcf⟩
    · intro x _ y _ hxy
      have hlt : t * (x - l + 1) < t * (y - l + 1) :=
        mul_lt_mul_of_pos_left (by linarith) ht
      rw [hformula, hformula]
      linarith
  · constructor
    · intro x hx
      exact (hX ⟨x, hx⟩).elim
    · intro x hx y hy hxy
      exact (hX ⟨x, hx⟩).elim

end Str

namespace ArithmeticLifting

/-- The executable rational lifting map. Old source points retain their
prescribed images; new points use their computed least old upper anchor. -/
def computableMap (A Aplus B : Finset ℚ) (h : ℚ → ℚ) (x : ℚ) : ℚ :=
  if x ∈ A then h x
  else Str.computablePlaceBelow B Aplus (h (Str.computableUp A x)) x

/-- The executable target carrier of the rational lifting. -/
def computableTarget (A Aplus B : Finset ℚ) (h : ℚ → ℚ) : Finset ℚ :=
  B ∪ Aplus.image (computableMap A Aplus B h)

@[simp] theorem computableMap_of_mem {A Aplus B : Finset ℚ} {h : ℚ → ℚ}
    {x : ℚ} (hx : x ∈ A) : computableMap A Aplus B h x = h x := by
  simp only [computableMap, if_pos hx]

theorem computableMap_of_not_mem {A Aplus B : Finset ℚ} {h : ℚ → ℚ}
    {x : ℚ} (hx : x ∉ A) :
    computableMap A Aplus B h x =
      Str.computablePlaceBelow B Aplus (h (Str.computableUp A x)) x := by
  simp only [computableMap, if_neg hx]

/-- The computed map and target satisfy the bounded pure arithmetic
lifting specification under the same hypotheses as `exists_rat`. -/
theorem computable_rat {A Aplus B : Finset ℚ} {h : ℚ → ℚ}
    (hsub : A ⊆ Aplus)
    (hbounded : ∀ x ∈ Aplus, ∃ a ∈ A, x ≤ a)
    (hmono : ∀ x ∈ A, ∀ y ∈ A, x < y → h x < h y)
    (hmem : ∀ a ∈ A, h a ∈ B) :
    ArithmeticLifting A Aplus B (computableTarget A Aplus B h) h
      (computableMap A Aplus B h) := by
  let f := computableMap A Aplus B h
  have f_old {x : ℚ} (hx : x ∈ A) : f x = h x :=
    computableMap_of_mem hx
  have f_new {x : ℚ} (hx : x ∉ A) :
      f x = Str.computablePlaceBelow B Aplus (h (Str.computableUp A x)) x :=
    computableMap_of_not_mem hx
  have hplace (a : ℚ) (ha : a ∈ A) :=
    Str.computablePlaceBelow_spec B Aplus (hmem a ha)
  have copied {x : ℚ} (hx : x ∈ Aplus) (hxA : x ∉ A) :
      Str.JustBelow B (h (Str.computableUp A x)) (f x) := by
    rw [f_new hxA]
    exact (hplace (Str.computableUp A x) (Str.computableUp_spec (hbounded x hx)).1).1 x hx
  have hfmono : ∀ x ∈ Aplus, ∀ y ∈ Aplus, x < y → f x < f y := by
    intro x hx y hy hxy
    have hpx := Str.computableUp_spec (hbounded x hx)
    have hpy := Str.computableUp_spec (hbounded y hy)
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · rw [f_old hxA, f_old hyA]
      exact hmono x hxA y hyA hxy
    · rw [f_old hxA]
      exact (copied hy hyA).2.2 (h x) (hmem x hxA)
        (hmono x hxA (Str.computableUp A y) hpy.1 (hxy.trans_le hpy.2.1))
    · rw [f_old hyA]
      have hpyle : h (Str.computableUp A x) ≤ h y := by
        rcases (hpx.2.2 y hyA hxy.le).lt_or_eq with hp | hp
        · exact (hmono (Str.computableUp A x) hpx.1 y hyA hp).le
        · exact (congrArg h hp).le
      exact (copied hx hxA).2.1.trans_le hpyle
    · have hpq : Str.computableUp A x ≤ Str.computableUp A y :=
        Str.computableUp_mono A hxy.le
      rcases hpq.lt_or_eq with hpq | hpq
      · exact (copied hx hxA).2.1.trans
          ((copied hy hyA).2.2 (h (Str.computableUp A x))
            (hmem (Str.computableUp A x) hpx.1)
            (hmono (Str.computableUp A x) hpx.1 (Str.computableUp A y) hpy.1 hpq))
      · rw [f_new hxA, f_new hyA, hpq]
        exact (hplace (Str.computableUp A y) hpy.1).2 x hx y hy hxy
  refine {
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
  }
  intro a x hx hax
  have hup : Str.computableUp A x = a :=
    (Str.computableUp_spec (hbounded x hx)).unique hax.leastGE
  have hcopy := copied hx hax.not_mem
  rwa [hup] at hcopy

end ArithmeticLifting

namespace ComputableArithmeticLiftingExamples

/-- Two anchored blocks; the target also has old points outside the base
image, so the placement must respect target gaps as well as source order. -/
def source : Finset ℚ := {0, 2}

def sourcePlus : Finset ℚ := {-2, -1, 0, 1 / 2, 1, 2}

def target : Finset ℚ := {-2, 0, 3, 4}

def baseMap (x : ℚ) : ℚ := 2 * x

/-- Exact rational values check two points in each new block, old-point
agreement, and the complete computed carrier cardinality. -/
theorem two_block_regression :
    ArithmeticLifting.computableMap source sourcePlus target baseMap (-2) = -5 / 3 ∧
    ArithmeticLifting.computableMap source sourcePlus target baseMap (-1) = -4 / 3 ∧
    ArithmeticLifting.computableMap source sourcePlus target baseMap 0 = 0 ∧
    ArithmeticLifting.computableMap source sourcePlus target baseMap (1 / 2) = 43 / 12 ∧
    ArithmeticLifting.computableMap source sourcePlus target baseMap 1 = 11 / 3 ∧
    ArithmeticLifting.computableMap source sourcePlus target baseMap 2 = 4 ∧
    (ArithmeticLifting.computableTarget source sourcePlus target baseMap).card = 8 := by
  decide +kernel

/-- Kernel computation covers no predecessor, an existing predecessor,
empty placement, an empty source extension, and an empty target. -/
theorem boundary_regression :
    Str.computablePredBound ({4} : Finset ℚ) 4 = 3 ∧
    Str.computablePredBound ({-2, 0, 3, 4} : Finset ℚ) 4 = 3 ∧
    Str.computablePredBound (∅ : Finset ℚ) (-2) = -3 ∧
    Str.computablePlaceBelow ({4} : Finset ℚ) ∅ 4 (7 / 3) = 7 / 3 ∧
    ArithmeticLifting.computableMap {2} {-1, 1, 2} {4} baseMap (-1) = 16 / 5 ∧
    ArithmeticLifting.computableMap {2} {-1, 1, 2} {4} baseMap 1 = 18 / 5 ∧
    ArithmeticLifting.computableTarget ∅ ∅ target baseMap = target ∧
    ArithmeticLifting.computableTarget ∅ ∅ ∅ baseMap = ∅ := by
  decide +kernel

end ComputableArithmeticLiftingExamples

end Alexander313.Carlson
