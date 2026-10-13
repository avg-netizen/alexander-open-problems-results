import Alexander313.Carlson.Rules

/-!
# Upward reflection

Carlson, *Patterns of resemblance of order 2*, Definition 10.1 and the pattern
and continuity assertions of Lemma 10.2, pure case.

Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
pp. 40–43 of the author's October 16, 2008 manuscript.

Suppose `Q` is a continuous extension of `P` at `a` and `a <₂ b` in `P`.
Move a copy of the new points of `Q` to just below `b`. On old points the
relations remain those of `P`; on the new points they are copied from `Q`.
An old point `x < a` has the same relations to a copied point as to its
original. An old point in `[a, b)` is `≤₁` a copied point precisely when it
is `≤₁ b`, and it is never `≤₂` a copied point. No new point relates to an
old point.

For `≤₁`, continuity and `a ≤₁ b` let us use the uniform formula
`x < b ∧ x ≤₁ b` for an old point `x` relating to a new point.
`UpData.r₁_PN_below` verifies that this agrees with the copied relation
below `a`. `UpData.copiedBlock_isIso` proves the full substructure isomorphism
required by Definition 10.1(4), including reflection of both relations.

The manuscript's Lemma 10.2(2) says the result is an extension at `a`.
Definition 10.1(2) places all the new points just below `b`, so the extension
point in that assertion must be `b`. The theorem `UpData.extensionAt` uses
this corrected endpoint.

This module proves the explicit construction is a pattern and a continuous
extension at `b`. The cofinal validity assertion of Lemma 10.3 is separate.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α : Type*} [LinearOrder α]

/-- Upward 2-reflection of the new points of `Q` from `a` to `b` over `P`.
The matching `g` sends the new points `N` to their originals in `Q`. -/
def upward (P Q : Str α) (a b : α) (N : Finset α) (g : α → α) : Str α where
  U := P.U ∪ N
  r₁ u v := (u ∈ P.U ∧ v ∈ P.U ∧ P.r₁ u v) ∨
    (u ∈ P.U ∧ v ∈ N ∧ u < b ∧ P.r₁ u b) ∨
    (u ∈ N ∧ v ∈ N ∧ Q.r₁ (g u) (g v))
  r₂ u v := (u ∈ P.U ∧ v ∈ P.U ∧ P.r₂ u v) ∨
    (u ∈ P.U ∧ u < a ∧ v ∈ N ∧ Q.r₂ u (g v)) ∨
    (u ∈ N ∧ v ∈ N ∧ Q.r₂ (g u) (g v))

/-- The hypotheses of Definition 10.1, with an explicit placement and
matching of the copied points. -/
structure UpData (P Q : Str α) (a b : α) (N : Finset α) (g : α → α) : Prop where
  pat : Q.IsPattern
  cont : Continuous P Q
  ext : ExtensionAt P Q a
  hb : b ∈ P.U
  hab : a < b
  hrel : P.r₂ a b
  hNP : ∀ n ∈ N, n ∉ P.U
  hNb : ∀ n ∈ N, n < b
  hNL : ∀ n ∈ N, ∀ x ∈ P.U, x < b → x < n
  himage : N.image g = Q.U \ P.U
  hmono : ∀ x ∈ N, ∀ y ∈ N, x < y → g x < g y

namespace UpData

variable {P Q : Str α} {a b : α} {N : Finset α} {g : α → α}
  (D : UpData P Q a b N g)
include D

theorem ha : a ∈ P.U := D.ext.2.1

theorem basePattern : P.IsPattern := D.pat.mono D.cont.1

theorem ab₁ : P.r₁ a b := D.basePattern.sub₂ a D.ha b D.hb D.hrel

theorem g_mem {n : α} (hn : n ∈ N) : g n ∈ Q.U ∧ g n ∉ P.U := by
  apply Finset.mem_sdiff.mp
  rw [← D.himage]
  exact Finset.mem_image_of_mem g hn

theorem g_justBelow {n : α} (hn : n ∈ N) : JustBelow P.U a (g n) :=
  D.ext.2.2.2 (g n) (D.g_mem hn).1 (D.g_mem hn).2

theorem old_lt_g {x n : α} (hx : x ∈ P.U) (hxa : x < a) (hn : n ∈ N) : x < g n :=
  (D.g_justBelow hn).2.2 x hx hxa

theorem g_le_iff {x y : α} (hx : x ∈ N) (hy : y ∈ N) : g x ≤ g y ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hlt
    exact absurd (D.hmono y hy x hx (not_le.mp hlt)) (not_lt.mpr h)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact (D.hmono x hx y hy h).le
    · exact le_rfl

theorem leastGE_old {x : α} (hx : x ∈ P.U) : LeastGE P.U x x :=
  ⟨hx, le_rfl, fun _ _ h => h⟩

theorem leastGE_original {n : α} (hn : n ∈ N) : LeastGE P.U (g n) a := by
  refine ⟨D.ha, (D.g_justBelow hn).2.1.le, fun x hx hnx => ?_⟩
  by_contra hnot
  exact absurd hnx (not_le.mpr (D.old_lt_g hx (not_le.mp hnot) hn))

theorem leastGE_new {n : α} (hn : n ∈ N) : LeastGE P.U n b := by
  refine ⟨D.hb, (D.hNb n hn).le, fun x hx hnx => ?_⟩
  by_contra hnot
  exact absurd hnx (not_le.mpr (D.hNL n hn x hx (not_le.mp hnot)))

/-- Continuity of the source rule sends an edge into its new block to `a`. -/
theorem original_rel_to_a (k : Lvl) {x n : α} (hx : x ∈ P.U) (hxa : x < a)
    (hn : n ∈ N) (h : Q.rel k x (g n)) : P.rel k x a := by
  have hcorrect : KCorrect P Q k := by
    cases k
    · exact D.cont.2.2.1
    · exact D.cont.2.2.2
  obtain ⟨c, hc, hxc⟩ := hcorrect x x (g n) (D.cont.1.1 hx) (D.g_mem hn).1
    (D.leastGE_old hx) (D.old_lt_g hx hxa hn) h
  have hca : c = a := hc.unique (D.leastGE_original hn)
  rwa [hca] at hxc

/-- Below `a`, the copied first relation is equivalent to the old link to `b`. -/
theorem original_r₁_iff {x n : α} (hx : x ∈ P.U) (hxa : x < a) (hn : n ∈ N) :
    Q.r₁ x (g n) ↔ P.r₁ x b := by
  constructor
  · intro h
    exact D.basePattern.trans₁ x hx a D.ha b D.hb
      (D.original_rel_to_a .one hx hxa hn h) D.ab₁
  · intro h
    have hQ : Q.r₁ x b := (D.cont.1.2 x hx b D.hb).1.mp h
    exact D.pat.convex₁ x (D.cont.1.1 hx) (g n) (D.g_mem hn).1 b (D.cont.1.1 D.hb)
      (D.old_lt_g hx hxa hn).le ((D.g_justBelow hn).2.1.trans D.hab).le hQ

theorem r₁_PP {u v : α} (hu : u ∈ P.U) (hv : v ∈ P.U) :
    (P.upward Q a b N g).r₁ u v ↔ P.r₁ u v := by
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, hvN, _⟩ | ⟨huN, _⟩)
    · exact h
    · exact absurd hv (D.hNP v hvN)
    · exact absurd hu (D.hNP u huN)
  · intro h
    exact Or.inl ⟨hu, hv, h⟩

theorem r₂_PP {u v : α} (hu : u ∈ P.U) (hv : v ∈ P.U) :
    (P.upward Q a b N g).r₂ u v ↔ P.r₂ u v := by
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, _, hvN, _⟩ | ⟨huN, _⟩)
    · exact h
    · exact absurd hv (D.hNP v hvN)
    · exact absurd hu (D.hNP u huN)
  · intro h
    exact Or.inl ⟨hu, hv, h⟩

theorem r₁_PN {u v : α} (hu : u ∈ P.U) (hv : v ∈ N) :
    (P.upward Q a b N g).r₁ u v ↔ u < b ∧ P.r₁ u b := by
  constructor
  · rintro (⟨_, hvP, _⟩ | ⟨_, _, hub, h⟩ | ⟨huN, _⟩)
    · exact absurd hvP (D.hNP v hv)
    · exact ⟨hub, h⟩
    · exact absurd hu (D.hNP u huN)
  · rintro ⟨hub, h⟩
    exact Or.inr (Or.inl ⟨hu, hv, hub, h⟩)

theorem r₂_PN {u v : α} (hu : u ∈ P.U) (hv : v ∈ N) :
    (P.upward Q a b N g).r₂ u v ↔ u < a ∧ Q.r₂ u (g v) := by
  constructor
  · rintro (⟨_, hvP, _⟩ | ⟨_, hua, _, h⟩ | ⟨huN, _⟩)
    · exact absurd hvP (D.hNP v hv)
    · exact ⟨hua, h⟩
    · exact absurd hu (D.hNP u huN)
  · rintro ⟨hua, h⟩
    exact Or.inr (Or.inl ⟨hu, hua, hv, h⟩)

/-- Definition 10.1(4), old-to-new first relations below `a`. -/
theorem r₁_PN_below {u v : α} (hu : u ∈ P.U) (hua : u < a) (hv : v ∈ N) :
    (P.upward Q a b N g).r₁ u v ↔ Q.r₁ u (g v) := by
  rw [D.r₁_PN hu hv]
  constructor
  · intro h
    exact (D.original_r₁_iff hu hua hv).mpr h.2
  · intro h
    exact ⟨hua.trans D.hab, (D.original_r₁_iff hu hua hv).mp h⟩

theorem r₁_NN {u v : α} (hu : u ∈ N) (hv : v ∈ N) :
    (P.upward Q a b N g).r₁ u v ↔ Q.r₁ (g u) (g v) := by
  constructor
  · rintro (⟨huP, _⟩ | ⟨huP, _⟩ | ⟨_, _, h⟩)
    · exact absurd huP (D.hNP u hu)
    · exact absurd huP (D.hNP u hu)
    · exact h
  · intro h
    exact Or.inr (Or.inr ⟨hu, hv, h⟩)

theorem r₂_NN {u v : α} (hu : u ∈ N) (hv : v ∈ N) :
    (P.upward Q a b N g).r₂ u v ↔ Q.r₂ (g u) (g v) := by
  constructor
  · rintro (⟨huP, _⟩ | ⟨huP, _⟩ | ⟨_, _, h⟩)
    · exact absurd huP (D.hNP u hu)
    · exact absurd huP (D.hNP u hu)
    · exact h
  · intro h
    exact Or.inr (Or.inr ⟨hu, hv, h⟩)

theorem not_r₁_NP {u v : α} (hu : u ∈ N) (hv : v ∈ P.U) :
    ¬ (P.upward Q a b N g).r₁ u v := by
  rintro (⟨huP, _⟩ | ⟨huP, _⟩ | ⟨_, hvN, _⟩)
  · exact D.hNP u hu huP
  · exact D.hNP u hu huP
  · exact D.hNP v hvN hv

theorem not_r₂_NP {u v : α} (hu : u ∈ N) (hv : v ∈ P.U) :
    ¬ (P.upward Q a b N g).r₂ u v := by
  rintro (⟨huP, _⟩ | ⟨huP, _⟩ | ⟨_, hvN, _⟩)
  · exact D.hNP u hu huP
  · exact D.hNP u hu huP
  · exact D.hNP v hvN hv

/-- Definition 10.1(4): the copied block together with the old points below
`a` is isomorphic to the corresponding substructure of the source rule.
The matching fixes every old point below `a`. -/
theorem copiedBlock_isIso :
    IsIso ((P.upward Q a b N g).restrict ((P.U.filter (· < a)) ∪ N))
      (Q.restrict ((P.U.filter (· < a)) ∪ (Q.U \ P.U)))
      (fun z => if z ∈ N then g z else z) := by
  classical
  let L : Finset α := P.U.filter (· < a)
  let f : α → α := fun z => if z ∈ N then g z else z
  have f_new {z : α} (hz : z ∈ N) : f z = g z := by
    simp only [f, if_pos hz]
  have f_old {z : α} (hz : z ∈ P.U) : f z = z := by
    have hzN : z ∉ N := fun h => D.hNP z h hz
    simp only [f, if_neg hzN]
  change IsIso ((P.upward Q a b N g).restrict (L ∪ N))
    (Q.restrict (L ∪ (Q.U \ P.U))) f
  refine ⟨?_, ?_, ?_⟩
  · change (L ∪ N).image f = L ∪ (Q.U \ P.U)
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hz with hz | hz
      · rw [f_old (Finset.mem_filter.mp hz).1]
        exact Finset.mem_union_left _ hz
      · rw [f_new hz]
        exact Finset.mem_union_right L (Finset.mem_sdiff.mpr (D.g_mem hz))
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_image.mpr
          ⟨x, Finset.mem_union_left N hx, f_old (Finset.mem_filter.mp hx).1⟩
      · rw [← D.himage] at hx
        obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨z, Finset.mem_union_right L hz, (f_new hz).trans hzx⟩
  · intro x hx y hy hxy
    change f x < f y
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · rw [f_old (Finset.mem_filter.mp hx).1, f_old (Finset.mem_filter.mp hy).1]
      exact hxy
    · obtain ⟨hxP, hxa⟩ := Finset.mem_filter.mp hx
      rw [f_old hxP, f_new hy]
      exact D.old_lt_g hxP hxa hy
    · obtain ⟨hyP, hya⟩ := Finset.mem_filter.mp hy
      exact absurd hxy (not_lt.mpr (D.hNL x hx y hyP (hya.trans D.hab)).le)
    · rw [f_new hx, f_new hy]
      exact D.hmono x hx y hy hxy
  · intro x hx y hy
    change ((P.upward Q a b N g).r₁ x y ↔ Q.r₁ (f x) (f y)) ∧
      ((P.upward Q a b N g).r₂ x y ↔ Q.r₂ (f x) (f y))
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · have hxP := (Finset.mem_filter.mp hx).1
      have hyP := (Finset.mem_filter.mp hy).1
      rw [f_old hxP, f_old hyP]
      exact ⟨(D.r₁_PP hxP hyP).trans (D.cont.1.2 x hxP y hyP).1,
        (D.r₂_PP hxP hyP).trans (D.cont.1.2 x hxP y hyP).2⟩
    · obtain ⟨hxP, hxa⟩ := Finset.mem_filter.mp hx
      rw [f_old hxP, f_new hy]
      exact ⟨D.r₁_PN_below hxP hxa hy,
        (D.r₂_PN hxP hy).trans (and_iff_right hxa)⟩
    · obtain ⟨hyP, hya⟩ := Finset.mem_filter.mp hy
      rw [f_new hx, f_old hyP]
      have hQ₁ : ¬ Q.r₁ (g x) y := by
        intro h
        exact absurd (D.pat.le₁ (g x) (D.g_mem hx).1 y (D.cont.1.1 hyP) h)
          (not_le.mpr (D.old_lt_g hyP hya hx))
      have hQ₂ : ¬ Q.r₂ (g x) y := by
        intro h
        exact hQ₁ (D.pat.sub₂ (g x) (D.g_mem hx).1 y (D.cont.1.1 hyP) h)
      exact ⟨⟨fun h => (D.not_r₁_NP hx hyP h).elim, fun h => (hQ₁ h).elim⟩,
        ⟨fun h => (D.not_r₂_NP hx hyP h).elim, fun h => (hQ₂ h).elim⟩⟩
    · rw [f_new hx, f_new hy]
      exact ⟨D.r₁_NN hx hy, D.r₂_NN hx hy⟩

theorem r₂_to_b {u v : α} (hu : u ∈ P.U) (hv : v ∈ N)
    (h : (P.upward Q a b N g).r₂ u v) : P.r₂ u b := by
  obtain ⟨hua, hQ⟩ := (D.r₂_PN hu hv).mp h
  exact D.basePattern.trans₂ u hu a D.ha b D.hb
    (D.original_rel_to_a .two hu hua hv hQ) D.hrel

theorem le₁ {u v : α} (h : (P.upward Q a b N g).r₁ u v) : u ≤ v := by
  rcases h with ⟨hu, hv, h⟩ | ⟨hu, hv, hub, _⟩ | ⟨hu, hv, h⟩
  · exact D.basePattern.le₁ u hu v hv h
  · exact (D.hNL v hv u hu hub).le
  · exact (D.g_le_iff hu hv).mp (D.pat.le₁ _ (D.g_mem hu).1 _ (D.g_mem hv).1 h)

theorem sub₂ {u v : α} (h : (P.upward Q a b N g).r₂ u v) :
    (P.upward Q a b N g).r₁ u v := by
  rcases h with ⟨hu, hv, h⟩ | ⟨hu, hua, hv, h⟩ | ⟨hu, hv, h⟩
  · exact (D.r₁_PP hu hv).mpr (D.basePattern.sub₂ u hu v hv h)
  · exact (D.r₁_PN hu hv).mpr ⟨hua.trans D.hab, (D.original_r₁_iff hu hua hv).mp
      (D.pat.sub₂ u (D.cont.1.1 hu) (g v) (D.g_mem hv).1 h)⟩
  · exact (D.r₁_NN hu hv).mpr (D.pat.sub₂ _ (D.g_mem hu).1 _ (D.g_mem hv).1 h)

theorem trans₁ {u v w : α} (hu : u ∈ (P.upward Q a b N g).U)
    (hv : v ∈ (P.upward Q a b N g).U) (hw : w ∈ (P.upward Q a b N g).U)
    (h₁ : (P.upward Q a b N g).r₁ u v) (h₂ : (P.upward Q a b N g).r₁ v w) :
    (P.upward Q a b N g).r₁ u w := by
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv <;>
    rcases Finset.mem_union.mp hw with hw | hw
  · exact (D.r₁_PP hu hw).mpr (D.basePattern.trans₁ u hu v hv w hw
      ((D.r₁_PP hu hv).mp h₁) ((D.r₁_PP hv hw).mp h₂))
  · obtain ⟨hvb, hvb₁⟩ := (D.r₁_PN hv hw).mp h₂
    exact (D.r₁_PN hu hw).mpr ⟨(D.le₁ h₁).trans_lt hvb,
      D.basePattern.trans₁ u hu v hv b D.hb ((D.r₁_PP hu hv).mp h₁) hvb₁⟩
  · exact absurd h₂ (D.not_r₁_NP hv hw)
  · exact (D.r₁_PN hu hw).mpr ((D.r₁_PN hu hv).mp h₁)
  · exact absurd h₁ (D.not_r₁_NP hu hv)
  · exact absurd h₁ (D.not_r₁_NP hu hv)
  · exact absurd h₂ (D.not_r₁_NP hv hw)
  · exact (D.r₁_NN hu hw).mpr (D.pat.trans₁ _ (D.g_mem hu).1 _ (D.g_mem hv).1 _
      (D.g_mem hw).1 ((D.r₁_NN hu hv).mp h₁) ((D.r₁_NN hv hw).mp h₂))

theorem trans₂ {u v w : α} (hu : u ∈ (P.upward Q a b N g).U)
    (hv : v ∈ (P.upward Q a b N g).U) (hw : w ∈ (P.upward Q a b N g).U)
    (h₁ : (P.upward Q a b N g).r₂ u v) (h₂ : (P.upward Q a b N g).r₂ v w) :
    (P.upward Q a b N g).r₂ u w := by
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv <;>
    rcases Finset.mem_union.mp hw with hw | hw
  · exact (D.r₂_PP hu hw).mpr (D.basePattern.trans₂ u hu v hv w hw
      ((D.r₂_PP hu hv).mp h₁) ((D.r₂_PP hv hw).mp h₂))
  · obtain ⟨hva, hvw⟩ := (D.r₂_PN hv hw).mp h₂
    have huv : Q.r₂ u v := (D.cont.1.2 u hu v hv).2.mp ((D.r₂_PP hu hv).mp h₁)
    exact (D.r₂_PN hu hw).mpr ⟨(D.le₁ (D.sub₂ h₁)).trans_lt hva,
      D.pat.trans₂ u (D.cont.1.1 hu) v (D.cont.1.1 hv) (g w) (D.g_mem hw).1 huv hvw⟩
  · exact absurd h₂ (D.not_r₂_NP hv hw)
  · obtain ⟨hua, huv⟩ := (D.r₂_PN hu hv).mp h₁
    exact (D.r₂_PN hu hw).mpr ⟨hua,
      D.pat.trans₂ u (D.cont.1.1 hu) (g v) (D.g_mem hv).1 (g w) (D.g_mem hw).1 huv
        ((D.r₂_NN hv hw).mp h₂)⟩
  · exact absurd h₁ (D.not_r₂_NP hu hv)
  · exact absurd h₁ (D.not_r₂_NP hu hv)
  · exact absurd h₂ (D.not_r₂_NP hv hw)
  · exact (D.r₂_NN hu hw).mpr (D.pat.trans₂ _ (D.g_mem hu).1 _ (D.g_mem hv).1 _
      (D.g_mem hw).1 ((D.r₂_NN hu hv).mp h₁) ((D.r₂_NN hv hw).mp h₂))

theorem convex₁ {u v w : α} (hu : u ∈ (P.upward Q a b N g).U)
    (hv : v ∈ (P.upward Q a b N g).U) (hw : w ∈ (P.upward Q a b N g).U)
    (huv : u ≤ v) (hvw : v ≤ w) (h : (P.upward Q a b N g).r₁ u w) :
    (P.upward Q a b N g).r₁ u v := by
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv <;>
    rcases Finset.mem_union.mp hw with hw | hw
  · exact (D.r₁_PP hu hv).mpr (D.basePattern.convex₁ u hu v hv w hw huv hvw
      ((D.r₁_PP hu hw).mp h))
  · obtain ⟨_, hub⟩ := (D.r₁_PN hu hw).mp h
    exact (D.r₁_PP hu hv).mpr (D.basePattern.convex₁ u hu v hv b D.hb huv
      (hvw.trans_lt (D.hNb w hw)).le hub)
  · have hbw : b ≤ w := by
      by_contra hnot
      exact absurd hvw (not_le.mpr (D.hNL v hv w hw (not_le.mp hnot)))
    exact (D.r₁_PN hu hv).mpr ⟨huv.trans_lt (D.hNb v hv),
      D.basePattern.convex₁ u hu b D.hb w hw (huv.trans_lt (D.hNb v hv)).le hbw
        ((D.r₁_PP hu hw).mp h)⟩
  · exact (D.r₁_PN hu hv).mpr ((D.r₁_PN hu hw).mp h)
  · exact absurd h (D.not_r₁_NP hu hw)
  · exact absurd huv (not_le.mpr (D.hNL u hu v hv (hvw.trans_lt (D.hNb w hw))))
  · exact absurd h (D.not_r₁_NP hu hw)
  · exact (D.r₁_NN hu hv).mpr (D.pat.convex₁ _ (D.g_mem hu).1 _ (D.g_mem hv).1 _
      (D.g_mem hw).1 ((D.g_le_iff hu hv).mpr huv) ((D.g_le_iff hv hw).mpr hvw)
      ((D.r₁_NN hu hw).mp h))

theorem respect₂ {u v w : α} (hu : u ∈ (P.upward Q a b N g).U)
    (hv : v ∈ (P.upward Q a b N g).U) (hw : w ∈ (P.upward Q a b N g).U)
    (huv : u ≤ v) (hvw : v ≤ w) (h₂ : (P.upward Q a b N g).r₂ u w)
    (h₁ : (P.upward Q a b N g).r₁ v w) : (P.upward Q a b N g).r₂ u v := by
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv <;>
    rcases Finset.mem_union.mp hw with hw | hw
  · exact (D.r₂_PP hu hv).mpr (D.basePattern.respect₂ u hu v hv w hw huv hvw
      ((D.r₂_PP hu hw).mp h₂) ((D.r₁_PP hv hw).mp h₁))
  · obtain ⟨hvb, hvb₁⟩ := (D.r₁_PN hv hw).mp h₁
    exact (D.r₂_PP hu hv).mpr (D.basePattern.respect₂ u hu v hv b D.hb huv hvb.le
      (D.r₂_to_b hu hw h₂) hvb₁)
  · exact absurd h₁ (D.not_r₁_NP hv hw)
  · obtain ⟨hua, huw⟩ := (D.r₂_PN hu hw).mp h₂
    exact (D.r₂_PN hu hv).mpr ⟨hua,
      D.pat.respect₂ u (D.cont.1.1 hu) (g v) (D.g_mem hv).1 (g w) (D.g_mem hw).1
        (D.old_lt_g hu hua hv).le ((D.g_le_iff hv hw).mpr hvw) huw
        ((D.r₁_NN hv hw).mp h₁)⟩
  · exact absurd h₂ (D.not_r₂_NP hu hw)
  · exact absurd huv (not_le.mpr (D.hNL u hu v hv (hvw.trans_lt (D.hNb w hw))))
  · exact absurd h₂ (D.not_r₂_NP hu hw)
  · exact (D.r₂_NN hu hv).mpr (D.pat.respect₂ _ (D.g_mem hu).1 _ (D.g_mem hv).1 _
      (D.g_mem hw).1 ((D.g_le_iff hu hv).mpr huv) ((D.g_le_iff hv hw).mpr hvw)
      ((D.r₂_NN hu hw).mp h₂) ((D.r₁_NN hv hw).mp h₁))

/-- Lemma 10.2, pattern assertion. -/
theorem isPattern : (P.upward Q a b N g).IsPattern := by
  refine ⟨fun _ _ _ _ h => D.le₁ h, fun _ _ _ _ h => D.sub₂ h, ?_, ?_,
    fun _ hu _ hv _ hw h₁ h₂ => D.trans₁ hu hv hw h₁ h₂,
    fun _ hu _ hv _ hw h₁ h₂ => D.trans₂ hu hv hw h₁ h₂,
    fun _ hu _ hv _ hw huv hvw h => D.convex₁ hu hv hw huv hvw h,
    fun _ hu _ hv _ hw huv hvw h₂ h₁ => D.respect₂ hu hv hw huv hvw h₂ h₁⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact (D.r₁_PP hu hu).mpr (D.basePattern.refl₁ u hu)
    · exact (D.r₁_NN hu hu).mpr (D.pat.refl₁ _ (D.g_mem hu).1)
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact (D.r₂_PP hu hu).mpr (D.basePattern.refl₂ u hu)
    · exact (D.r₂_NN hu hu).mpr (D.pat.refl₂ _ (D.g_mem hu).1)

theorem isSub : IsSub P (P.upward Q a b N g) :=
  ⟨Finset.subset_union_left, fun x hx y hy => ⟨(D.r₁_PP hx hy).symm, (D.r₂_PP hx hy).symm⟩⟩

theorem N_nonempty : N.Nonempty := by
  obtain ⟨x, hxQ, hxP⟩ := D.ext.2.2.1
  have hx : x ∈ Q.U \ P.U := Finset.mem_sdiff.mpr ⟨hxQ, hxP⟩
  rw [← D.himage] at hx
  obtain ⟨n, hn, _⟩ := Finset.mem_image.mp hx
  exact ⟨n, hn⟩

/-- Lemma 10.2(2), with `b` correcting the printed endpoint `a`. -/
theorem extensionAt : ExtensionAt P (P.upward Q a b N g) b := by
  refine ⟨D.isSub, D.hb, ?_, fun x hx hxP => ?_⟩
  · obtain ⟨n, hn⟩ := D.N_nonempty
    exact ⟨n, Finset.mem_union_right P.U hn, D.hNP n hn⟩
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact absurd hx hxP
    · exact ⟨D.hb, D.hNb x hx, D.hNL x hx⟩

theorem kCorrect (k : Lvl) : KCorrect P (P.upward Q a b N g) k := by
  intro p x y hx hy hp hpy hxy
  rcases Finset.mem_union.mp hx with hxP | hxN
  · rw [hp.unique (D.leastGE_old hxP)] at hpy ⊢
    rcases Finset.mem_union.mp hy with hyP | hyN
    · refine ⟨y, D.leastGE_old hyP, ?_⟩
      cases k
      · exact (D.r₁_PP hxP hyP).mp hxy
      · exact (D.r₂_PP hxP hyP).mp hxy
    · refine ⟨b, D.leastGE_new hyN, ?_⟩
      cases k
      · exact ((D.r₁_PN hxP hyN).mp hxy).2
      · exact D.r₂_to_b hxP hyN hxy
  · exfalso
    rw [hp.unique (D.leastGE_new hxN)] at hpy
    rcases Finset.mem_union.mp hy with hyP | hyN
    · cases k
      · exact D.not_r₁_NP hxN hyP hxy
      · exact D.not_r₂_NP hxN hyP hxy
    · exact absurd (hpy.trans (D.hNb y hyN)) (lt_irrefl b)

/-- Lemma 10.2(2): upward reflection is continuous over the base pattern. -/
theorem continuous : Continuous P (P.upward Q a b N g) := by
  refine ⟨D.isSub, fun x hx => ?_, D.kCorrect .one, D.kCorrect .two⟩
  rcases Finset.mem_union.mp hx with hx | hx
  · exact ⟨x, hx, le_rfl⟩
  · exact ⟨b, D.hb, (D.hNb x hx).le⟩

end UpData

end Str

end Alexander313.Carlson
