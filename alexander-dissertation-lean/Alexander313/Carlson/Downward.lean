import Alexander313.Carlson.Rules
import Mathlib.Tactic.Order

/-!
# Downward reflection

Carlson, *Patterns of resemblance of order 2*, Definitions 9.1 and 9.4, pure
case. Let `a ≤ₖ b` in a pattern `P`, with `a < b`, and let `X` be a nonempty
set of points of `P` in `[a, b)`. A copy `N` of `X` is placed just below `a`,
matched with `X` by a strictly increasing `g`. Below `a`, the new points relate
to each other and to the old points exactly as their originals do. A new point
relates to no old point `≥ a`, except that for `k = 2` it is `≤₁` an old point
`y ≥ a` exactly when its original is `≤₁ b` and `a ≤₁ y`. No old point `≥ a`
relates to a new point.

`downward` writes this structure out explicitly. Carlson leaves implicit that
old points above the copy do not relate to it; any structure meeting his
conditions and having this property agrees with `downward`.

Proved here: `downward` is a pattern (Lemmas 9.2 and 9.5, pattern part) and a
continuous extension of `P` at `a` (Lemmas 9.2(2), 9.5(2)).
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α : Type*} [LinearOrder α]

open Classical in
/-- New points to their originals; identity elsewhere. -/
def back (N : Finset α) (g : α → α) (z : α) : α := if z ∈ N then g z else z

theorem back_of_mem {N : Finset α} {g : α → α} {z : α} (h : z ∈ N) : back N g z = g z := by
  rw [back, if_pos h]

theorem back_of_not_mem {N : Finset α} {g : α → α} {z : α} (h : z ∉ N) : back N g z = z := by
  rw [back, if_neg h]

/-- The structure obtained from `P` by `k`-reflecting a set downward from `b`
to `a`, with new points `N` matched to their originals by `g`. -/
def downward (P : Str α) (k : Lvl) (a b : α) (N : Finset α) (g : α → α) : Str α where
  U := P.U ∪ N
  r₁ u v := (u ∈ P.U ∧ v ∈ P.U ∧ P.r₁ u v) ∨
    ((u ∈ N ∨ v ∈ N) ∧ (u ∈ N ∨ u < a) ∧ (v ∈ N ∨ v < a) ∧
      P.r₁ (back N g u) (back N g v)) ∨
    (k = .two ∧ u ∈ N ∧ v ∈ P.U ∧ a ≤ v ∧ P.r₁ (g u) b ∧ P.r₁ a v)
  r₂ u v := (u ∈ P.U ∧ v ∈ P.U ∧ P.r₂ u v) ∨
    ((u ∈ N ∨ v ∈ N) ∧ (u ∈ N ∨ u < a) ∧ (v ∈ N ∨ v < a) ∧
      P.r₂ (back N g u) (back N g v))

/-- The lower block: old points below `a` together with the new points. -/
def InLow (N : Finset α) (P : Str α) (a z : α) : Prop := z ∈ N ∨ (z ∈ P.U ∧ z < a)

/-- The hypotheses of downward `k`-reflection of `X` from `b` to `a`. -/
structure DownData (P : Str α) (k : Lvl) (a b : α) (X N : Finset α) (g : α → α) : Prop where
  pat : P.IsPattern
  ha : a ∈ P.U
  hb : b ∈ P.U
  hab : a < b
  hrel : P.rel k a b
  hX : ∀ x ∈ X, x ∈ P.U ∧ a ≤ x ∧ x < b
  hXne : X.Nonempty
  hNP : ∀ n ∈ N, n ∉ P.U
  hNa : ∀ n ∈ N, n < a
  hNL : ∀ n ∈ N, ∀ q ∈ P.U, q < a → q < n
  himage : N.image g = X
  hmono : ∀ x ∈ N, ∀ y ∈ N, x < y → g x < g y

namespace DownData

variable {P : Str α} {k : Lvl} {a b : α} {X N : Finset α} {g : α → α}
  (D : DownData P k a b X N g)
include D

theorem g_mem {n : α} (hn : n ∈ N) : g n ∈ X := by
  rw [← D.himage]
  exact Finset.mem_image_of_mem g hn

theorem g_props {n : α} (hn : n ∈ N) : g n ∈ P.U ∧ a ≤ g n ∧ g n < b := D.hX _ (D.g_mem hn)

theorem ab₁ : P.r₁ a b := by
  have := D.hrel
  cases k
  · exact this
  · exact D.pat.sub₂ a D.ha b D.hb this

/-- Every new point is `≤₁`-reached from `a` within `[a, b]`: `a ≤₁ g n`. -/
theorem a_r₁_g {n : α} (hn : n ∈ N) : P.r₁ a (g n) :=
  D.pat.convex₁ a D.ha (g n) (D.g_props hn).1 b D.hb (D.g_props hn).2.1
    (D.g_props hn).2.2.le D.ab₁

theorem g_le_iff {x y : α} (hx : x ∈ N) (hy : y ∈ N) : g x ≤ g y ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hlt
    exact absurd (D.hmono y hy x hx (not_le.mp hlt)) (not_lt.mpr h)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact (D.hmono x hx y hy h).le
    · exact le_rfl

theorem r₁_PP {u v : α} (hu : u ∈ P.U) (hv : v ∈ P.U) :
    (P.downward k a b N g).r₁ u v ↔ P.r₁ u v := by
  constructor
  · rintro (⟨_, _, h⟩ | ⟨hN, _, _, _⟩ | ⟨_, hN, _⟩)
    · exact h
    · rcases hN with hN | hN
      · exact absurd hu (D.hNP u hN)
      · exact absurd hv (D.hNP v hN)
    · exact absurd hu (D.hNP u hN)
  · intro h
    exact Or.inl ⟨hu, hv, h⟩

theorem r₂_PP {u v : α} (hu : u ∈ P.U) (hv : v ∈ P.U) :
    (P.downward k a b N g).r₂ u v ↔ P.r₂ u v := by
  constructor
  · rintro (⟨_, _, h⟩ | ⟨hN, _, _, _⟩)
    · exact h
    · rcases hN with hN | hN
      · exact absurd hu (D.hNP u hN)
      · exact absurd hv (D.hNP v hN)
  · intro h
    exact Or.inl ⟨hu, hv, h⟩

theorem low_back_mem {z : α} (hz : InLow N P a z) : back N g z ∈ P.U := by
  rcases hz with hz | ⟨hz, _⟩
  · rw [back_of_mem hz]
    exact (D.g_props hz).1
  · rw [back_of_not_mem (fun h => D.hNP z h hz)]
    exact hz

theorem low_back_mono {u v : α} (hu : InLow N P a u) (hv : InLow N P a v) (huv : u < v) :
    back N g u < back N g v := by
  rcases hu with hu | ⟨huP, hua⟩ <;> rcases hv with hv | ⟨hvP, hva⟩
  · rw [back_of_mem hu, back_of_mem hv]
    exact D.hmono u hu v hv huv
  · exact absurd huv (not_lt.mpr (D.hNL u hu v hvP hva).le)
  · rw [back_of_not_mem (fun h => D.hNP u h huP), back_of_mem hv]
    exact hua.trans_le (D.g_props hv).2.1
  · rw [back_of_not_mem (fun h => D.hNP u h huP), back_of_not_mem (fun h => D.hNP v h hvP)]
    exact huv

theorem r₁_low {u v : α} (hu : InLow N P a u) (hv : InLow N P a v) :
    (P.downward k a b N g).r₁ u v ↔ P.r₁ (back N g u) (back N g v) := by
  by_cases hboth : u ∈ N ∨ v ∈ N
  · constructor
    · rintro (⟨huP, hvP, h⟩ | ⟨_, _, _, h⟩ | ⟨_, huN, hvP, hav, _⟩)
      · rcases hboth with h' | h'
        · exact absurd huP (D.hNP u h')
        · exact absurd hvP (D.hNP v h')
      · exact h
      · rcases hv with hv | ⟨_, hva⟩
        · exact absurd hvP (D.hNP v hv)
        · exact absurd hav (not_le.mpr hva)
    · intro h
      refine Or.inr (Or.inl ⟨hboth, ?_, ?_, h⟩)
      · rcases hu with hu | ⟨_, hua⟩
        · exact Or.inl hu
        · exact Or.inr hua
      · rcases hv with hv | ⟨_, hva⟩
        · exact Or.inl hv
        · exact Or.inr hva
  · push_neg at hboth
    obtain ⟨huN, hvN⟩ := hboth
    have huP : u ∈ P.U := by
      rcases hu with hu | ⟨hu, _⟩
      · exact absurd hu huN
      · exact hu
    have hvP : v ∈ P.U := by
      rcases hv with hv | ⟨hv, _⟩
      · exact absurd hv hvN
      · exact hv
    rw [D.r₁_PP huP hvP, back_of_not_mem huN, back_of_not_mem hvN]

theorem r₂_low {u v : α} (hu : InLow N P a u) (hv : InLow N P a v) :
    (P.downward k a b N g).r₂ u v ↔ P.r₂ (back N g u) (back N g v) := by
  by_cases hboth : u ∈ N ∨ v ∈ N
  · constructor
    · rintro (⟨huP, hvP, h⟩ | ⟨_, _, _, h⟩)
      · rcases hboth with h' | h'
        · exact absurd huP (D.hNP u h')
        · exact absurd hvP (D.hNP v h')
      · exact h
    · intro h
      refine Or.inr ⟨hboth, ?_, ?_, h⟩
      · rcases hu with hu | ⟨_, hua⟩
        · exact Or.inl hu
        · exact Or.inr hua
      · rcases hv with hv | ⟨_, hva⟩
        · exact Or.inl hv
        · exact Or.inr hva
  · push_neg at hboth
    obtain ⟨huN, hvN⟩ := hboth
    have huP : u ∈ P.U := by
      rcases hu with hu | ⟨hu, _⟩
      · exact absurd hu huN
      · exact hu
    have hvP : v ∈ P.U := by
      rcases hv with hv | ⟨hv, _⟩
      · exact absurd hv hvN
      · exact hv
    rw [D.r₂_PP huP hvP, back_of_not_mem huN, back_of_not_mem hvN]

/-- A new point and an old point at or above `a`. -/
theorem r₁_NH {u v : α} (hu : u ∈ N) (hv : v ∈ P.U) (hav : a ≤ v) :
    (P.downward k a b N g).r₁ u v ↔ k = .two ∧ P.r₁ (g u) b ∧ P.r₁ a v := by
  constructor
  · rintro (⟨huP, _, _⟩ | ⟨_, _, hv', _⟩ | ⟨hk, _, _, _, h₁, h₂⟩)
    · exact absurd huP (D.hNP u hu)
    · rcases hv' with hv' | hv'
      · exact absurd hv (D.hNP v hv')
      · exact absurd hav (not_le.mpr hv')
    · exact ⟨hk, h₁, h₂⟩
  · rintro ⟨hk, h₁, h₂⟩
    exact Or.inr (Or.inr ⟨hk, hu, hv, hav, h₁, h₂⟩)

theorem not_r₂_NH {u v : α} (hu : u ∈ N) (hv : v ∈ P.U) (hav : a ≤ v) :
    ¬ (P.downward k a b N g).r₂ u v := by
  rintro (⟨huP, _, _⟩ | ⟨_, _, hv', _⟩)
  · exact D.hNP u hu huP
  · rcases hv' with hv' | hv'
    · exact D.hNP v hv' hv
    · exact absurd hav (not_le.mpr hv')

theorem not_r₁_HN {u v : α} (hu : u ∈ P.U) (hau : a ≤ u) (hv : v ∈ N) :
    ¬ (P.downward k a b N g).r₁ u v := by
  rintro (⟨_, hvP, _⟩ | ⟨_, hu', _, _⟩ | ⟨_, huN, _⟩)
  · exact D.hNP v hv hvP
  · rcases hu' with hu' | hu'
    · exact D.hNP u hu' hu
    · exact absurd hau (not_le.mpr hu')
  · exact D.hNP u huN hu

theorem not_r₂_HN {u v : α} (hu : u ∈ P.U) (hau : a ≤ u) (hv : v ∈ N) :
    ¬ (P.downward k a b N g).r₂ u v := by
  rintro (⟨_, hvP, _⟩ | ⟨_, hu', _, _⟩)
  · exact D.hNP v hv hvP
  · rcases hu' with hu' | hu'
    · exact D.hNP u hu' hu
    · exact absurd hau (not_le.mpr hu')

/-- Every point of the new structure is new, old below `a`, or old at or above `a`. -/
theorem region {z : α} (hz : z ∈ (P.downward k a b N g).U) :
    z ∈ N ∨ (z ∈ P.U ∧ z < a) ∨ (z ∈ P.U ∧ a ≤ z) := by
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases lt_or_ge z a with h | h
    · exact Or.inr (Or.inl ⟨hz, h⟩)
    · exact Or.inr (Or.inr ⟨hz, h⟩)
  · exact Or.inl hz

theorem low_back_le {u v : α} (hu : InLow N P a u) (hv : InLow N P a v) (huv : u ≤ v) :
    back N g u ≤ back N g v := by
  rcases huv.lt_or_eq with h | rfl
  · exact (D.low_back_mono hu hv h).le
  · exact le_rfl

theorem low_of_N {z : α} (hz : z ∈ N) : InLow N P a z := Or.inl hz

theorem low_of_L {z : α} (hz : z ∈ P.U) (hza : z < a) : InLow N P a z := Or.inr ⟨hz, hza⟩

theorem back_N {z : α} (hz : z ∈ N) : back N g z = g z := back_of_mem hz

theorem back_L {z : α} (hz : z ∈ P.U) : back N g z = z := back_of_not_mem (fun h => D.hNP z h hz)

/-- Pairs of points of the reflected structure: both low, both old, or a new
point with an old point at or above `a` in either order. -/
theorem pair_cases {u v : α} (hu : u ∈ (P.downward k a b N g).U)
    (hv : v ∈ (P.downward k a b N g).U) :
    (InLow N P a u ∧ InLow N P a v) ∨ (u ∈ P.U ∧ v ∈ P.U) ∨
    (u ∈ N ∧ v ∈ P.U ∧ a ≤ v) ∨ (u ∈ P.U ∧ a ≤ u ∧ v ∈ N) := by
  rcases D.region hu with hu | ⟨huP, hua⟩ | ⟨huP, hau⟩ <;>
  rcases D.region hv with hv | ⟨hvP, hva⟩ | ⟨hvP, hav⟩
  · exact Or.inl ⟨D.low_of_N hu, D.low_of_N hv⟩
  · exact Or.inl ⟨D.low_of_N hu, D.low_of_L hvP hva⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hu, hvP, hav⟩))
  · exact Or.inl ⟨D.low_of_L huP hua, D.low_of_N hv⟩
  · exact Or.inr (Or.inl ⟨huP, hvP⟩)
  · exact Or.inr (Or.inl ⟨huP, hvP⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨huP, hau, hv⟩))
  · exact Or.inr (Or.inl ⟨huP, hvP⟩)
  · exact Or.inr (Or.inl ⟨huP, hvP⟩)

theorem le₁ {u v : α} (hu : u ∈ (P.downward k a b N g).U) (hv : v ∈ (P.downward k a b N g).U)
    (h : (P.downward k a b N g).r₁ u v) : u ≤ v := by
  rcases D.pair_cases hu hv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv, hav⟩ | ⟨hu, hau, hv⟩
  · have hP := D.pat.le₁ _ (D.low_back_mem hu) _ (D.low_back_mem hv) ((D.r₁_low hu hv).mp h)
    by_contra hlt
    exact absurd hP (not_le.mpr (D.low_back_mono hv hu (not_le.mp hlt)))
  · exact D.pat.le₁ u hu v hv ((D.r₁_PP hu hv).mp h)
  · exact (D.hNa u hu).le.trans hav
  · exact absurd h (D.not_r₁_HN hu hau hv)

theorem sub₂ {u v : α} (hu : u ∈ (P.downward k a b N g).U) (hv : v ∈ (P.downward k a b N g).U)
    (h : (P.downward k a b N g).r₂ u v) : (P.downward k a b N g).r₁ u v := by
  rcases D.pair_cases hu hv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv, hav⟩ | ⟨hu, hau, hv⟩
  · exact (D.r₁_low hu hv).mpr (D.pat.sub₂ _ (D.low_back_mem hu) _ (D.low_back_mem hv)
      ((D.r₂_low hu hv).mp h))
  · exact (D.r₁_PP hu hv).mpr (D.pat.sub₂ u hu v hv ((D.r₂_PP hu hv).mp h))
  · exact absurd h (D.not_r₂_NH hu hv hav)
  · exact absurd h (D.not_r₂_HN hu hau hv)

/-- Ordered triples: all low, all old, or one of the three mixed shapes
(old below `a`, new, old above), (new, new, old above), (new, old above, old above). -/
theorem triple_cases {u v w : α} (hu : u ∈ (P.downward k a b N g).U)
    (hv : v ∈ (P.downward k a b N g).U) (hw : w ∈ (P.downward k a b N g).U)
    (huv : u ≤ v) (hvw : v ≤ w) :
    (InLow N P a u ∧ InLow N P a v ∧ InLow N P a w) ∨ (u ∈ P.U ∧ v ∈ P.U ∧ w ∈ P.U) ∨
    (u ∈ P.U ∧ u < a ∧ v ∈ N ∧ w ∈ P.U ∧ a ≤ w) ∨
    (u ∈ N ∧ v ∈ N ∧ w ∈ P.U ∧ a ≤ w) ∨
    (u ∈ N ∧ v ∈ P.U ∧ a ≤ v ∧ w ∈ P.U ∧ a ≤ w) := by
  have lowLt (z : α) (hz : z ∈ (P.downward k a b N g).U) (hza : z < a) : InLow N P a z := by
    rcases D.region hz with hz | ⟨hzP, _⟩ | ⟨_, hz'⟩
    · exact D.low_of_N hz
    · exact D.low_of_L hzP hza
    · exact absurd hza (not_lt.mpr hz')
  rcases D.region hw with hwN | ⟨hwP, hwa⟩ | ⟨hwP, haw⟩
  · have hwa := D.hNa w hwN
    exact Or.inl ⟨lowLt u hu (huv.trans_lt (hvw.trans_lt hwa)), lowLt v hv (hvw.trans_lt hwa),
      D.low_of_N hwN⟩
  · exact Or.inl ⟨lowLt u hu (huv.trans_lt (hvw.trans_lt hwa)), lowLt v hv (hvw.trans_lt hwa),
      D.low_of_L hwP hwa⟩
  · rcases D.region hu with huN | ⟨huP, hua⟩ | ⟨huP, hau⟩
    · rcases D.region hv with hvN | ⟨hvP, hva⟩ | ⟨hvP, hav⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨huN, hvN, hwP, haw⟩)))
      · exact absurd huv (not_le.mpr (D.hNL u huN v hvP hva))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨huN, hvP, hav, hwP, haw⟩)))
    · rcases D.region hv with hvN | ⟨hvP, hva⟩ | ⟨hvP, hav⟩
      · exact Or.inr (Or.inr (Or.inl ⟨huP, hua, hvN, hwP, haw⟩))
      · exact Or.inr (Or.inl ⟨huP, hvP, hwP⟩)
      · exact Or.inr (Or.inl ⟨huP, hvP, hwP⟩)
    · rcases D.region hv with hvN | ⟨hvP, hva⟩ | ⟨hvP, hav⟩
      · exact absurd (hau.trans huv) (not_le.mpr (D.hNa v hvN))
      · exact Or.inr (Or.inl ⟨huP, hvP, hwP⟩)
      · exact Or.inr (Or.inl ⟨huP, hvP, hwP⟩)

/-- `P.r₂ a b` when reflecting at level two. -/
theorem ab₂ (hk : k = .two) : P.r₂ a b := by
  have := D.hrel
  subst hk
  exact this

/-- Lemmas 9.2 and 9.5, pattern part: the reflected structure is a pattern. -/
theorem isPattern : (P.downward k a b N g).IsPattern := by
  refine ⟨fun u hu v hv h => D.le₁ hu hv h, fun u hu v hv h => D.sub₂ hu hv h, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro u hu
    rcases D.region hu with huN | ⟨huP, _⟩ | ⟨huP, _⟩
    · exact (D.r₁_low (D.low_of_N huN) (D.low_of_N huN)).mpr
        (D.pat.refl₁ _ (D.low_back_mem (D.low_of_N huN)))
    · exact (D.r₁_PP huP huP).mpr (D.pat.refl₁ u huP)
    · exact (D.r₁_PP huP huP).mpr (D.pat.refl₁ u huP)
  · intro u hu
    rcases D.region hu with huN | ⟨huP, _⟩ | ⟨huP, _⟩
    · exact (D.r₂_low (D.low_of_N huN) (D.low_of_N huN)).mpr
        (D.pat.refl₂ _ (D.low_back_mem (D.low_of_N huN)))
    · exact (D.r₂_PP huP huP).mpr (D.pat.refl₂ u huP)
    · exact (D.r₂_PP huP huP).mpr (D.pat.refl₂ u huP)
  · -- transitivity of the first relation
    intro u hu v hv w hw h₁ h₂
    have huv := D.le₁ hu hv h₁
    have hvw := D.le₁ hv hw h₂
    rcases D.triple_cases hu hv hw huv hvw with ⟨lu, lv, lw⟩ | ⟨pu, pv, pw⟩ |
      ⟨pu, hua, nv, pw, haw⟩ | ⟨nu, nv, pw, haw⟩ | ⟨nu, pv, hav, pw, haw⟩
    · exact (D.r₁_low lu lw).mpr (D.pat.trans₁ _ (D.low_back_mem lu) _ (D.low_back_mem lv) _
        (D.low_back_mem lw) ((D.r₁_low lu lv).mp h₁) ((D.r₁_low lv lw).mp h₂))
    · exact (D.r₁_PP pu pw).mpr (D.pat.trans₁ u pu v pv w pw ((D.r₁_PP pu pv).mp h₁)
        ((D.r₁_PP pv pw).mp h₂))
    · have h₁' := (D.r₁_low (D.low_of_L pu hua) (D.low_of_N nv)).mp h₁
      rw [D.back_L pu, D.back_N nv] at h₁'
      obtain ⟨_, _, haw'⟩ := (D.r₁_NH nv pw haw).mp h₂
      have hua' : P.r₁ u a := D.pat.convex₁ u pu a D.ha (g v) (D.g_props nv).1 hua.le
        (D.g_props nv).2.1 h₁'
      exact (D.r₁_PP pu pw).mpr (D.pat.trans₁ u pu a D.ha w pw hua' haw')
    · have h₁' := (D.r₁_low (D.low_of_N nu) (D.low_of_N nv)).mp h₁
      rw [D.back_N nu, D.back_N nv] at h₁'
      obtain ⟨hk, hvb, haw'⟩ := (D.r₁_NH nv pw haw).mp h₂
      exact (D.r₁_NH nu pw haw).mpr ⟨hk, D.pat.trans₁ _ (D.g_props nu).1 _ (D.g_props nv).1 b
        D.hb h₁' hvb, haw'⟩
    · obtain ⟨hk, hub, hav'⟩ := (D.r₁_NH nu pv hav).mp h₁
      exact (D.r₁_NH nu pw haw).mpr ⟨hk, hub,
        D.pat.trans₁ a D.ha v pv w pw hav' ((D.r₁_PP pv pw).mp h₂)⟩
  · -- transitivity of the second relation
    intro u hu v hv w hw h₁ h₂
    have huv := D.le₁ hu hv (D.sub₂ hu hv h₁)
    have hvw := D.le₁ hv hw (D.sub₂ hv hw h₂)
    rcases D.triple_cases hu hv hw huv hvw with ⟨lu, lv, lw⟩ | ⟨pu, pv, pw⟩ |
      ⟨pu, hua, nv, pw, haw⟩ | ⟨nu, nv, pw, haw⟩ | ⟨nu, pv, hav, pw, haw⟩
    · exact (D.r₂_low lu lw).mpr (D.pat.trans₂ _ (D.low_back_mem lu) _ (D.low_back_mem lv) _
        (D.low_back_mem lw) ((D.r₂_low lu lv).mp h₁) ((D.r₂_low lv lw).mp h₂))
    · exact (D.r₂_PP pu pw).mpr (D.pat.trans₂ u pu v pv w pw ((D.r₂_PP pu pv).mp h₁)
        ((D.r₂_PP pv pw).mp h₂))
    · exact absurd h₂ (D.not_r₂_NH nv pw haw)
    · exact absurd h₂ (D.not_r₂_NH nv pw haw)
    · exact absurd h₁ (D.not_r₂_NH nu pv hav)
  · -- convexity of the first relation
    intro u hu v hv w hw huv hvw h
    rcases D.triple_cases hu hv hw huv hvw with ⟨lu, lv, lw⟩ | ⟨pu, pv, pw⟩ |
      ⟨pu, hua, nv, pw, haw⟩ | ⟨nu, nv, pw, haw⟩ | ⟨nu, pv, hav, pw, haw⟩
    · exact (D.r₁_low lu lv).mpr (D.pat.convex₁ _ (D.low_back_mem lu) _ (D.low_back_mem lv) _
        (D.low_back_mem lw) (D.low_back_le lu lv huv) (D.low_back_le lv lw hvw)
        ((D.r₁_low lu lw).mp h))
    · exact (D.r₁_PP pu pv).mpr (D.pat.convex₁ u pu v pv w pw huv hvw ((D.r₁_PP pu pw).mp h))
    · have huw := (D.r₁_PP pu pw).mp h
      have hua' : P.r₁ u a := D.pat.convex₁ u pu a D.ha w pw hua.le haw huw
      have hug : P.r₁ u (g v) := D.pat.trans₁ u pu a D.ha (g v) (D.g_props nv).1 hua'
        (D.a_r₁_g nv)
      have := (D.r₁_low (D.low_of_L pu hua) (D.low_of_N nv)).mpr
      rw [D.back_L pu, D.back_N nv] at this
      exact this hug
    · obtain ⟨_, hub, _⟩ := (D.r₁_NH nu pw haw).mp h
      have hguv : g u ≤ g v := (D.g_le_iff nu nv).mpr huv
      have := (D.r₁_low (D.low_of_N nu) (D.low_of_N nv)).mpr
      rw [D.back_N nu, D.back_N nv] at this
      exact this (D.pat.convex₁ _ (D.g_props nu).1 _ (D.g_props nv).1 b D.hb hguv
        (D.g_props nv).2.2.le hub)
    · obtain ⟨hk, hub, haw'⟩ := (D.r₁_NH nu pw haw).mp h
      exact (D.r₁_NH nu pv hav).mpr ⟨hk, hub, D.pat.convex₁ a D.ha v pv w pw hav hvw haw'⟩
  · -- the second relation respects the first
    intro u hu v hv w hw huv hvw h₂ h₁
    rcases D.triple_cases hu hv hw huv hvw with ⟨lu, lv, lw⟩ | ⟨pu, pv, pw⟩ |
      ⟨pu, hua, nv, pw, haw⟩ | ⟨nu, nv, pw, haw⟩ | ⟨nu, pv, hav, pw, haw⟩
    · exact (D.r₂_low lu lv).mpr (D.pat.respect₂ _ (D.low_back_mem lu) _ (D.low_back_mem lv) _
        (D.low_back_mem lw) (D.low_back_le lu lv huv) (D.low_back_le lv lw hvw)
        ((D.r₂_low lu lw).mp h₂) ((D.r₁_low lv lw).mp h₁))
    · exact (D.r₂_PP pu pv).mpr (D.pat.respect₂ u pu v pv w pw huv hvw ((D.r₂_PP pu pw).mp h₂)
        ((D.r₁_PP pv pw).mp h₁))
    · have huw := (D.r₂_PP pu pw).mp h₂
      obtain ⟨hk, hvb, haw'⟩ := (D.r₁_NH nv pw haw).mp h₁
      have hua' : P.r₂ u a := D.pat.respect₂ u pu a D.ha w pw hua.le haw huw haw'
      have hub : P.r₂ u b := D.pat.trans₂ u pu a D.ha b D.hb hua' (D.ab₂ hk)
      have hug : P.r₂ u (g v) := D.pat.respect₂ u pu (g v) (D.g_props nv).1 b D.hb
        (hua.le.trans (D.g_props nv).2.1) (D.g_props nv).2.2.le hub hvb
      have := (D.r₂_low (D.low_of_L pu hua) (D.low_of_N nv)).mpr
      rw [D.back_L pu, D.back_N nv] at this
      exact this hug
    · exact absurd h₂ (D.not_r₂_NH nu pw haw)
    · exact absurd h₂ (D.not_r₂_NH nu pw haw)

theorem leastGE_old {y : α} (hy : y ∈ P.U) : LeastGE P.U y y := ⟨hy, le_rfl, fun _ _ h => h⟩

theorem leastGE_new {n : α} (hn : n ∈ N) : LeastGE P.U n a := by
  refine ⟨D.ha, (D.hNa n hn).le, fun q hq hnq => ?_⟩
  by_contra hlt
  exact absurd hnq (not_le.mpr (D.hNL n hn q hq (not_le.mp hlt)))

theorem isSub : IsSub P (P.downward k a b N g) :=
  ⟨Finset.subset_union_left, fun x hx y hy => ⟨(D.r₁_PP hx hy).symm, (D.r₂_PP hx hy).symm⟩⟩

theorem N_nonempty : N.Nonempty := by
  obtain ⟨x, hx⟩ := D.hXne
  rw [← D.himage] at hx
  obtain ⟨n, hn, _⟩ := Finset.mem_image.mp hx
  exact ⟨n, hn⟩

theorem mem_N_of_not_old {z : α} (hz : z ∈ (P.downward k a b N g).U) (hzP : z ∉ P.U) :
    z ∈ N := by
  rcases Finset.mem_union.mp hz with h | h
  · exact absurd h hzP
  · exact h

/-- Lemmas 9.2(2) and 9.5(2): an extension of `P` at `a`. -/
theorem extensionAt : ExtensionAt P (P.downward k a b N g) a := by
  refine ⟨D.isSub, D.ha, ?_, fun x hx hxP => ?_⟩
  · obtain ⟨n, hn⟩ := D.N_nonempty
    exact ⟨n, Finset.mem_union_right P.U hn, D.hNP n hn⟩
  · have hxN := D.mem_N_of_not_old hx hxP
    exact ⟨D.ha, D.hNa x hxN, D.hNL x hxN⟩

/-- Lemmas 9.2(2) and 9.5(2): a continuous extension of `P`. -/
theorem continuous : Continuous P (P.downward k a b N g) := by
  refine ⟨D.isSub, fun x hx => ?_, ?_, ?_⟩
  · rcases Finset.mem_union.mp hx with h | h
    · exact ⟨x, h, le_rfl⟩
    · exact ⟨a, D.ha, (D.hNa x h).le⟩
  all_goals
    intro p x y hx hy hp hpy hxy
    rcases D.region hx with hxN | ⟨hxP, hxa⟩ | ⟨hxP, hax⟩
  -- level one
  · rw [hp.unique (D.leastGE_new hxN)] at hpy ⊢
    have hyP : y ∈ P.U ∧ a ≤ y := by
      rcases D.region hy with hyN | ⟨hyP, _⟩ | ⟨hyP, hay⟩
      · exact absurd (hpy.trans (D.hNa y hyN)) (lt_irrefl _)
      · exact ⟨hyP, hpy.le⟩
      · exact ⟨hyP, hay⟩
    obtain ⟨_, _, hay⟩ := (D.r₁_NH hxN hyP.1 hyP.2).mp hxy
    exact ⟨y, D.leastGE_old hyP.1, hay⟩
  · rw [hp.unique (D.leastGE_old hxP)] at hpy ⊢
    rcases Finset.mem_union.mp hy with hyP | hyN
    · exact ⟨y, D.leastGE_old hyP, (D.r₁_PP hxP hyP).mp hxy⟩
    · have hxy' := (D.r₁_low (D.low_of_L hxP hxa) (D.low_of_N hyN)).mp hxy
      rw [D.back_L hxP, D.back_N hyN] at hxy'
      exact ⟨a, D.leastGE_new hyN, D.pat.convex₁ x hxP a D.ha (g y) (D.g_props hyN).1 hxa.le
        (D.g_props hyN).2.1 hxy'⟩
  · rw [hp.unique (D.leastGE_old hxP)] at hpy ⊢
    rcases Finset.mem_union.mp hy with hyP | hyN
    · exact ⟨y, D.leastGE_old hyP, (D.r₁_PP hxP hyP).mp hxy⟩
    · exact absurd hxy (D.not_r₁_HN hxP hax hyN)
  -- level two
  · exfalso
    rw [hp.unique (D.leastGE_new hxN)] at hpy
    rcases D.region hy with hyN | ⟨hyP, _⟩ | ⟨hyP, hay⟩
    · exact absurd (hpy.trans (D.hNa y hyN)) (lt_irrefl _)
    · exact D.not_r₂_NH hxN hyP hpy.le hxy
    · exact D.not_r₂_NH hxN hyP hay hxy
  · rw [hp.unique (D.leastGE_old hxP)] at hpy ⊢
    rcases Finset.mem_union.mp hy with hyP | hyN
    · exact ⟨y, D.leastGE_old hyP, (D.r₂_PP hxP hyP).mp hxy⟩
    · have hxy' := (D.r₂_low (D.low_of_L hxP hxa) (D.low_of_N hyN)).mp hxy
      rw [D.back_L hxP, D.back_N hyN] at hxy'
      exact ⟨a, D.leastGE_new hyN, D.pat.respect₂ x hxP a D.ha (g y) (D.g_props hyN).1 hxa.le
        (D.g_props hyN).2.1 hxy' (D.a_r₁_g hyN)⟩
  · rw [hp.unique (D.leastGE_old hxP)] at hpy ⊢
    rcases Finset.mem_union.mp hy with hyP | hyN
    · exact ⟨y, D.leastGE_old hyP, (D.r₂_PP hxP hyP).mp hxy⟩
    · exact absurd hxy (D.not_r₂_HN hxP hax hyN)

/-- Lemmas 9.3 and 9.6: downward reflection rules are cofinally valid. A covering
of `P` is extended by copying the images of the reflected points below the
image of `a`, with Carlson's copy lemma for `h a ≤ₖ h b` in `R₂`. -/
theorem cofinallyValid : CofinallyValid P (P.downward k a b N g) := by
  refine ⟨D.isSub, fun h hh cut hcut => ?_⟩
  have hR1 : R1 (h a) (h b) := hh.2.1 a D.ha b D.hb D.ab₁
  have hlt : h a < h b := hh.1 a D.ha b D.hb D.hab
  have hpos : 0 < h a := by
    obtain ⟨f, copy⟩ := R1_copy' hR1 {h a} (by simpa using hlt)
    exact lt_of_le_of_lt zero_le (copy.1 (h a) (Finset.mem_singleton_self _))
  have hcuta : cut a < h a := hcut a D.ha hpos
  let L := P.U.filter (· < a)
  let F : Finset Ordinal.{0} := insert (cut a) (L.image h ∪ X.image h)
  have memL {z : α} (hz : z ∈ P.U) (hza : z < a) : h z ∈ F :=
    Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem h (Finset.mem_filter.mpr ⟨hz, hza⟩)))
  have memX {n : α} (hn : n ∈ N) : h (g n) ∈ F :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem h (D.g_mem hn)))
  have memCut : cut a ∈ F := Finset.mem_insert_self _ _
  have hF : ∀ z ∈ F, z < h b := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hcuta.trans hlt
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hxP, hxa⟩ := Finset.mem_filter.mp hx
        exact hh.1 x hxP b D.hb (hxa.trans D.hab)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        exact hh.1 x (D.hX x hx).1 b D.hb (D.hX x hx).2.2
  obtain ⟨f, copy, links⟩ : ∃ f, CoveringCopy R1 R2 F f (h a) ∧
      (k = .two → ∀ z ∈ F, h a ≤ z → R1 z (h b) → R1 (f z) (h a)) := by
    by_cases hk : k = .two
    · obtain ⟨f, copy, links⟩ := R2_copy' (hh.2.2 a D.ha b D.hb (D.ab₂ hk)) F hF
      exact ⟨f, copy, fun _ => links⟩
    · obtain ⟨f, copy⟩ := R1_copy' hR1 F hF
      exact ⟨f, copy, fun h' => absurd h' hk⟩
  let h' : α → Ordinal.{0} := fun z => if z ∈ N then f (h (g z)) else h z
  have h'_old {z : α} (hz : z ∈ P.U) : h' z = h z := by
    simp only [h', if_neg (fun hN => D.hNP z hN hz)]
  have h'_new {z : α} (hz : z ∈ N) : h' z = f (h (g z)) := by
    simp only [h', if_pos hz]
  -- low points: the extended map is the copy map after `h ∘ back`
  have h'_low {z : α} (hz : InLow N P a z) :
      h' z = f (h (back N g z)) ∧ h (back N g z) ∈ F := by
    rcases hz with hz | ⟨hzP, hza⟩
    · rw [h'_new hz, D.back_N hz]
      exact ⟨rfl, memX hz⟩
    · rw [h'_old hzP, D.back_L hzP]
      refine ⟨(copy.2.1 (h z) (memL hzP hza) (hh.1 z hzP a D.ha hza)).symm, memL hzP hza⟩
  have hle_a {y : α} (hy : y ∈ P.U) (hay : a ≤ y) : h a ≤ h y := IsCovering.le_of_le hh D.ha hy hay
  refine ⟨h', ⟨?_, ?_, ?_⟩, fun z hz => h'_old hz, ?_⟩
  · -- strictly increasing
    intro u hu v hv huv
    rcases D.pair_cases hu hv with ⟨lu, lv⟩ | ⟨pu, pv⟩ | ⟨nu, pv, hav⟩ | ⟨pu, hau, nv⟩
    · obtain ⟨eu, mu⟩ := h'_low lu
      obtain ⟨ev, mv⟩ := h'_low lv
      rw [eu, ev]
      exact copy.2.2.1 _ mu _ mv (hh.1 _ (D.low_back_mem lu) _ (D.low_back_mem lv)
        (D.low_back_mono lu lv huv))
    · rw [h'_old pu, h'_old pv]
      exact hh.1 u pu v pv huv
    · rw [h'_new nu, h'_old pv]
      exact (copy.1 _ (memX nu)).trans_le (hle_a pv hav)
    · exact absurd (huv.trans (D.hNa v nv)) (not_lt.mpr hau)
  · -- the first relation
    intro u hu v hv huv
    rcases D.pair_cases hu hv with ⟨lu, lv⟩ | ⟨pu, pv⟩ | ⟨nu, pv, hav⟩ | ⟨pu, hau, nv⟩
    · obtain ⟨eu, mu⟩ := h'_low lu
      obtain ⟨ev, mv⟩ := h'_low lv
      rw [eu, ev]
      exact copy.2.2.2.1 _ mu _ mv (hh.2.1 _ (D.low_back_mem lu) _ (D.low_back_mem lv)
        ((D.r₁_low lu lv).mp huv))
    · rw [h'_old pu, h'_old pv]
      exact hh.2.1 u pu v pv ((D.r₁_PP pu pv).mp huv)
    · obtain ⟨hk, hub, hav'⟩ := (D.r₁_NH nu pv hav).mp huv
      rw [h'_new nu, h'_old pv]
      have hgu := D.g_props nu
      have hz : R1 (f (h (g u))) (h a) :=
        links hk (h (g u)) (memX nu) (IsCovering.le_of_le hh D.ha hgu.1 hgu.2.1)
          (hh.2.1 (g u) hgu.1 b D.hb hub)
      exact R1_trans hz (hh.2.1 a D.ha v pv hav')
    · exact absurd huv (D.not_r₁_HN pu hau nv)
  · -- the second relation
    intro u hu v hv huv
    rcases D.pair_cases hu hv with ⟨lu, lv⟩ | ⟨pu, pv⟩ | ⟨nu, pv, hav⟩ | ⟨pu, hau, nv⟩
    · obtain ⟨eu, mu⟩ := h'_low lu
      obtain ⟨ev, mv⟩ := h'_low lv
      rw [eu, ev]
      exact copy.2.2.2.2 _ mu _ mv (hh.2.2 _ (D.low_back_mem lu) _ (D.low_back_mem lv)
        ((D.r₂_low lu lv).mp huv))
    · rw [h'_old pu, h'_old pv]
      exact hh.2.2 u pu v pv ((D.r₂_PP pu pv).mp huv)
    · exact absurd huv (D.not_r₂_NH nu pv hav)
    · exact absurd huv (D.not_r₂_HN pu hau nv)
  · -- new points land above the cutoff of `a`
    intro a' c hc hjb
    have hcN : c ∈ N := D.mem_N_of_not_old hc hjb.not_mem
    have ha' : a' = a := hjb.unique ⟨D.ha, D.hNa c hcN, D.hNL c hcN⟩
    rw [ha', h'_new hcN]
    have hfix : f (cut a) = cut a := copy.2.1 (cut a) memCut hcuta
    have hgc := D.g_props hcN
    have hlt' : cut a < h (g c) := hcuta.trans_le (IsCovering.le_of_le hh D.ha hgc.1 hgc.2.1)
    have := copy.2.2.1 (cut a) memCut (h (g c)) (memX hcN) hlt'
    rwa [hfix] at this

end DownData

end Str

end Alexander313.Carlson
