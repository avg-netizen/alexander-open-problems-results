import Alexander313.Carlson.Patterns

/-!
# Valid rules and continuity

Carlson, *Patterns of resemblance of order 2*, §6–§8, pure case.

A rule `P|P⁺` is valid when every covering of `P` in `R₂` extends to one of `P⁺`.
It is cofinally valid when, in addition, every new point just below an old
point `a` can be placed above any prescribed cutoff below the image of `a`
(Definitions 6.1–6.3; the regressive function of Definition 6.2 is a cutoff
for each old point). Lemma 6.4 gives composition and restriction.

`P⁺` is a k-correct extension of `P` (Definition 7.1) when a `≤ₖ`-edge of `P⁺`
leaving the block just below an old point `p` and landing in the block just below
an old point `p'` forces `p ≤ₖ p'` in `P`. A continuous extension (Definition 7.4)
adds no new maximum and is both 1- and 2-correct.

In the pure case every point is indecomposable, so an arithmetic extension adds
no points, and the arithmetic generating rules of Definition 13.10(1) are the
identity rules.
-/

noncomputable section

namespace Alexander313.Carlson

/-- The two relation levels. -/
inductive Lvl | one | two
  deriving DecidableEq

namespace Str

variable {α : Type*} [LinearOrder α]

/-- The relation of level `k`. -/
def rel (P : Str α) : Lvl → α → α → Prop
  | .one => P.r₁
  | .two => P.r₂

/-- The relation one level down: the order for level one, `≤₁` for level two. -/
def relDown (P : Str α) : Lvl → α → α → Prop
  | .one => (· ≤ ·)
  | .two => P.r₁

/-- `p` is the least point of `S` at or above `x`. -/
def LeastGE (S : Finset α) (x p : α) : Prop := p ∈ S ∧ x ≤ p ∧ ∀ q ∈ S, x ≤ q → p ≤ q

/-- `b` lies just below `a`: `a ∈ P` and `b` is above every point of `P` below `a`. -/
def JustBelow (S : Finset α) (a b : α) : Prop := a ∈ S ∧ b < a ∧ ∀ q ∈ S, q < a → q < b

theorem LeastGE.unique {S : Finset α} {x p p' : α} (h : LeastGE S x p) (h' : LeastGE S x p') :
    p = p' :=
  le_antisymm (h.2.2 p' h'.1 h'.2.1) (h'.2.2 p h.1 h.2.1)

theorem LeastGE.exists {S : Finset α} {x : α} (h : ∃ p ∈ S, x ≤ p) : ∃ p, LeastGE S x p := by
  classical
  let T := S.filter (fun q => x ≤ q)
  have hT : T.Nonempty := by
    obtain ⟨p, hp, hxp⟩ := h
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hxp⟩⟩
  refine ⟨T.min' hT, (Finset.mem_filter.mp (T.min'_mem hT)).1,
    (Finset.mem_filter.mp (T.min'_mem hT)).2, fun q hq hxq => ?_⟩
  exact T.min'_le q (Finset.mem_filter.mpr ⟨hq, hxq⟩)

/-- Definition 7.1, pure case. -/
def KCorrect (P Q : Str α) (k : Lvl) : Prop :=
  ∀ p x y : α, x ∈ Q.U → y ∈ Q.U → LeastGE P.U x p → p < y → Q.rel k x y →
    ∃ p', LeastGE P.U y p' ∧ P.rel k p p'

/-- Definition 7.4, pure case: `Q` is a continuous extension of `P`. -/
def Continuous (P Q : Str α) : Prop :=
  IsSub P Q ∧ (∀ x ∈ Q.U, ∃ p ∈ P.U, x ≤ p) ∧ KCorrect P Q .one ∧ KCorrect P Q .two

/-- Definition 8.6, pure case: `Q` is an extension of `P` at `a`. -/
def ExtensionAt (P Q : Str α) (a : α) : Prop :=
  IsSub P Q ∧ a ∈ P.U ∧ (∃ x ∈ Q.U, x ∉ P.U) ∧ ∀ x ∈ Q.U, x ∉ P.U → JustBelow P.U a x

/-- Coverings of `Q` in `R₂` that extend a covering `h` of `P`. -/
def Extends (P : Str α) (h h' : α → Ordinal.{0}) : Prop := ∀ x ∈ P.U, h' x = h x

/-- Definition 6.1: the rule `P|Q` is valid. -/
def Valid (P Q : Str α) : Prop :=
  IsSub P Q ∧ ∀ h, CoveringR P h → ∃ h', CoveringR Q h' ∧ Extends P h h'

/-- Definition 6.3: the rule `P|Q` is cofinally valid. -/
def CofinallyValid (P Q : Str α) : Prop :=
  IsSub P Q ∧ ∀ h, CoveringR P h → ∀ cut : α → Ordinal.{0},
    (∀ a ∈ P.U, 0 < h a → cut a < h a) →
    ∃ h', CoveringR Q h' ∧ Extends P h h' ∧
      ∀ a b, b ∈ Q.U → JustBelow P.U a b → cut a < h' b

theorem CofinallyValid.valid {P Q : Str α} (hv : CofinallyValid P Q) : Valid P Q := by
  refine ⟨hv.1, fun h hh => ?_⟩
  obtain ⟨h', cov, ext, _⟩ := hv.2 h hh (fun _ => 0) (fun _ _ h0 => h0)
  exact ⟨h', cov, ext⟩

theorem IsSub.refl (P : Str α) : IsSub P P := ⟨subset_rfl, fun _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩

theorem IsSub.trans {P Q R : Str α} (hPQ : IsSub P Q) (hQR : IsSub Q R) : IsSub P R := by
  refine ⟨hPQ.1.trans hQR.1, fun x hx y hy => ?_⟩
  have h₁ := hPQ.2 x hx y hy
  have h₂ := hQR.2 x (hPQ.1 hx) y (hPQ.1 hy)
  exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Restriction of a substructure chain (Lemma 2.4(2b), pure case). -/
theorem IsSub.of_sub {P Q R : Str α} (hPR : IsSub P R) (hQR : IsSub Q R) (hPQ : P.U ⊆ Q.U) :
    IsSub P Q := by
  refine ⟨hPQ, fun x hx y hy => ?_⟩
  have h₁ := hPR.2 x hx y hy
  have h₂ := hQR.2 x (hPQ hx) y (hPQ hy)
  exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩

theorem IsSub.rel_iff {P Q : Str α} (h : IsSub P Q) {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U)
    (k : Lvl) : P.rel k x y ↔ Q.rel k x y := by
  cases k
  · exact (h.2 x hx y hy).1
  · exact (h.2 x hx y hy).2

/-- Lemma 6.4(1): valid rules compose. -/
theorem Valid.trans {P Q R : Str α} (h₁ : Valid P Q) (h₂ : Valid Q R) : Valid P R := by
  refine ⟨h₁.1.trans h₂.1, fun h hh => ?_⟩
  obtain ⟨g, gcov, gext⟩ := h₁.2 h hh
  obtain ⟨g', gcov', gext'⟩ := h₂.2 g gcov
  exact ⟨g', gcov', fun x hx => (gext' x (h₁.1.1 hx)).trans (gext x hx)⟩

/-- Lemma 6.4(3): restriction of a valid rule. -/
theorem Valid.restrict {P Q R : Str α} (hPR : Valid P R) (hQR : IsSub Q R)
    (hPQ : P.U ⊆ Q.U) : Valid P Q := by
  refine ⟨IsSub.of_sub hPR.1 hQR hPQ, fun h hh => ?_⟩
  obtain ⟨g, gcov, gext⟩ := hPR.2 h hh
  exact ⟨g, gcov.mono hQR, gext⟩

/-- Lemma 6.4(4): restriction of a cofinally valid rule. -/
theorem CofinallyValid.restrict {P Q R : Str α} (hPR : CofinallyValid P R) (hQR : IsSub Q R)
    (hPQ : P.U ⊆ Q.U) : CofinallyValid P Q := by
  refine ⟨IsSub.of_sub hPR.1 hQR hPQ, fun h hh cut hcut => ?_⟩
  obtain ⟨g, gcov, gext, gcut⟩ := hPR.2 h hh cut hcut
  exact ⟨g, gcov.mono hQR, gext, fun a b hb hab => gcut a b (hQR.1 hb) hab⟩

open Classical in
/-- The least point of `S` at or above `x`, when one exists. -/
def up (S : Finset α) (x : α) : α :=
  if hx : ∃ p, LeastGE S x p then Classical.choose hx else x

theorem up_spec {S : Finset α} {x : α} (h : ∃ p ∈ S, x ≤ p) : LeastGE S x (up S x) := by
  have hex : ∃ p, LeastGE S x p := LeastGE.exists h
  rw [up, dif_pos hex]
  exact Classical.choose_spec hex

/-- A point strictly below the least point of `S` above it lies just below that point. -/
theorem justBelow_of_leastGE {S : Finset α} {x p : α} (h : LeastGE S x p) (hx : x ∉ S) :
    JustBelow S p x := by
  obtain ⟨hp, hxp, hmin⟩ := h
  have hlt : x < p := lt_of_le_of_ne hxp (fun h => hx (h ▸ hp))
  refine ⟨hp, hlt, fun q hq hqp => ?_⟩
  by_contra hnot
  exact absurd (hmin q hq (not_lt.mp hnot)) (not_le.mpr hqp)

/-- Lemma 6.4(2): cofinally valid rules compose, when the middle structure adds
no new maximum. The cutoff for a point of the middle structure is the cutoff of
the least point of the first structure above it. -/
theorem CofinallyValid.trans {P Q R : Str α} (h₁ : CofinallyValid P Q)
    (h₂ : CofinallyValid Q R) (bounded : ∀ x ∈ Q.U, ∃ p ∈ P.U, x ≤ p) :
    CofinallyValid P R := by
  refine ⟨h₁.1.trans h₂.1, fun h hh cut hcut => ?_⟩
  obtain ⟨g, gcov, gext, gcut⟩ := h₁.2 h hh cut hcut
  let cut' : α → Ordinal.{0} := fun x => cut (up P.U x)
  have hcut' : ∀ a ∈ Q.U, 0 < g a → cut' a < g a := by
    intro a ha hga
    have hspec := up_spec (bounded a ha)
    by_cases haP : a ∈ P.U
    · have hup : up P.U a = a :=
        hspec.unique ⟨haP, le_rfl, fun q _ hq => hq⟩
      have hg : g a = h a := gext a haP
      change cut (up P.U a) < g a
      rw [hup, hg]
      exact hcut a haP (hg ▸ hga)
    · exact gcut (up P.U a) a ha (justBelow_of_leastGE hspec haP)
  obtain ⟨g', gcov', gext', gcut'⟩ := h₂.2 g gcov cut' hcut'
  refine ⟨g', gcov', fun x hx => (gext' x (h₁.1.1 hx)).trans (gext x hx), ?_⟩
  intro a c hc hac
  obtain ⟨ha, hca, hbelow⟩ := hac
  by_cases hcQ : c ∈ Q.U
  · rw [gext' c hcQ]
    exact gcut a c hcQ ⟨ha, hca, hbelow⟩
  · have hex : ∃ q ∈ Q.U, c ≤ q := ⟨a, h₁.1.1 ha, hca.le⟩
    have hspec := up_spec hex
    have hjb := justBelow_of_leastGE hspec hcQ
    have ha' := hspec.1
    have hup : up P.U (up Q.U c) = a := by
      apply (up_spec (bounded _ ha')).unique
      refine ⟨ha, hspec.2.2 a (h₁.1.1 ha) hca.le, fun q hq hq' => ?_⟩
      by_contra hnot
      have hqa : q < a := not_le.mp hnot
      have hqc : q < c := hbelow q hq hqa
      exact absurd (lt_of_lt_of_le (hqc.trans hjb.2.1) hq') (lt_irrefl q)
    have hfinal := gcut' (up Q.U c) c hc hjb
    change cut (up P.U (up Q.U c)) < g' c at hfinal
    rwa [hup] at hfinal

/-- The least point of the larger structure above `x` is at most the least
point of the smaller one, and the least point of the smaller one above it is
unchanged. -/
theorem leastGE_through {S T : Finset α} (hST : S ⊆ T) {x p q : α}
    (hp : LeastGE S x p) (hq : LeastGE T x q) : LeastGE S q p := by
  refine ⟨hp.1, hq.2.2 p (hST hp.1) hp.2.1, fun r hr hqr => hp.2.2 r hr (hq.2.1.trans hqr)⟩

/-- Lemma 7.3(1), pure case: k-correctness composes. -/
theorem KCorrect.trans {P Q R : Str α} {k : Lvl} (hPQ : IsSub P Q) (hQR : IsSub Q R)
    (h₁ : KCorrect P Q k) (h₂ : KCorrect Q R k) : KCorrect P R k := by
  intro p x y hx hy hp hpy hxy
  have hq : ∃ q, LeastGE Q.U x q := LeastGE.exists ⟨p, hPQ.1 hp.1, hp.2.1⟩
  obtain ⟨q, hq⟩ := hq
  have hqp : q ≤ p := hq.2.2 p (hPQ.1 hp.1) hp.2.1
  have hqy : q < y := hqp.trans_lt hpy
  obtain ⟨q', hq', hqq'⟩ := h₂ q x y hx hy hq hqy hxy
  have hpq : LeastGE P.U q p := leastGE_through hPQ.1 hp hq
  have hpq' : p < q' := hpy.trans_le hq'.2.1
  obtain ⟨p', hp', hpp'⟩ := h₁ p q q' hq.1 hq'.1 hpq hpq' hqq'
  refine ⟨p', ?_, hpp'⟩
  refine ⟨hp'.1, hq'.2.1.trans hp'.2.1, fun r hr hyr => hp'.2.2 r hr (hq'.2.2 r (hPQ.1 hr) hyr)⟩

/-- Lemma 7.3(2), pure case: k-correctness passes to an intermediate structure. -/
theorem KCorrect.restrict {P Q R : Str α} {k : Lvl} (hQR : IsSub Q R) (h : KCorrect P R k) :
    KCorrect P Q k := by
  intro p x y hx hy hp hpy hxy
  exact h p x y (hQR.1 hx) (hQR.1 hy) hp hpy ((hQR.rel_iff hx hy k).mp hxy)

/-- Lemma 7.6(1): continuous extensions compose. -/
theorem Continuous.trans {P Q R : Str α} (h₁ : Continuous P Q) (h₂ : Continuous Q R) :
    Continuous P R := by
  refine ⟨h₁.1.trans h₂.1, fun x hx => ?_, h₁.2.2.1.trans h₁.1 h₂.1 h₂.2.2.1,
    h₁.2.2.2.trans h₁.1 h₂.1 h₂.2.2.2⟩
  obtain ⟨q, hq, hxq⟩ := h₂.2.1 x hx
  obtain ⟨p, hp, hqp⟩ := h₁.2.1 q hq
  exact ⟨p, hp, hxq.trans hqp⟩

/-- Lemma 7.6(2): continuity passes to an intermediate structure. -/
theorem Continuous.restrict {P Q R : Str α} (h : Continuous P R) (hQR : IsSub Q R)
    (hPQ : P.U ⊆ Q.U) : Continuous P Q :=
  ⟨IsSub.of_sub h.1 hQR hPQ, fun x hx => h.2.1 x (hQR.1 hx), h.2.2.1.restrict hQR,
    h.2.2.2.restrict hQR⟩

theorem KCorrect.refl (P : Str α) (k : Lvl) : KCorrect P P k := by
  intro p x y hx hy hp _ hxy
  have hpx : p = x := hp.unique ⟨hx, le_rfl, fun _ _ h => h⟩
  subst hpx
  exact ⟨y, ⟨hy, le_rfl, fun _ _ h => h⟩, hxy⟩

theorem Continuous.refl (P : Str α) : Continuous P P :=
  ⟨IsSub.refl P, fun x hx => ⟨x, hx, le_rfl⟩, KCorrect.refl P .one, KCorrect.refl P .two⟩

theorem JustBelow.unique {S : Finset α} {a a' c : α} (h : JustBelow S a c)
    (h' : JustBelow S a' c) : a = a' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h'.2.2 a h.1 hlt) (not_lt.mpr h.2.1.le)
  · exact absurd (h.2.2 a' h'.1 hlt) (not_lt.mpr h'.2.1.le)

theorem JustBelow.not_mem {S : Finset α} {a c : α} (h : JustBelow S a c) : c ∉ S :=
  fun hc => lt_irrefl c (h.2.2 c hc h.2.1)

theorem IsCovering.le_of_le {β : Type*} [LinearOrder β] {P : Str α} {S₁ S₂ : β → β → Prop}
    {h : α → β} (hh : IsCovering P S₁ S₂ h) {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U)
    (hxy : x ≤ y) : h x ≤ h y := by
  rcases hxy.lt_or_eq with hlt | rfl
  · exact (hh.1 x hx y hy hlt).le
  · exact le_rfl

end Str

end Alexander313.Carlson
