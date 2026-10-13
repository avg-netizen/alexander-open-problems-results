import Alexander313.Carlson.Downward
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Existence of downward reflections on rational labels

`DownData` describes a downward reflection after a disjoint, increasing copy
has been placed just below its target. An arbitrary linear order need not
have room for that copy. Rational labels always do: a finite lower block has
a last point, and an affine map embeds the reflected interval into the gap
between that point and the target.

`DownData.exists_rat` supplies the placement from the source pattern and the
set being reflected. `exists_downward_extension_rat` therefore produces an
actual continuous, cofinally valid extension, with exactly one new point per
reflected point. These are existence results for finite patterns; they do not
assert that all patterns are covered or supply a presentation of the core.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

/-- A finite set in `[a, b)` has an increasing copy just below `a` relative to
any finite set of rational labels containing `a`. -/
theorem exists_copy_justBelow_rat (S X : Finset ℚ) {a b : ℚ}
    (ha : a ∈ S) (hab : a < b)
    (hX : ∀ x ∈ X, a ≤ x ∧ x < b) :
    ∃ (N : Finset ℚ) (g : ℚ → ℚ),
      (∀ n ∈ N, JustBelow S a n) ∧ N.image g = X ∧
      (∀ x ∈ N, ∀ y ∈ N, x < y → g x < g y) := by
  classical
  let L := S.filter (· < a)
  have lower_bound : ∃ c : ℚ, c < a ∧ ∀ q ∈ S, q < a → q ≤ c := by
    by_cases hL : L.Nonempty
    · refine ⟨L.max' hL, (Finset.mem_filter.mp (L.max'_mem hL)).2, ?_⟩
      intro q hq hqa
      exact L.le_max' q (Finset.mem_filter.mpr ⟨hq, hqa⟩)
    · refine ⟨a - 1, by linarith, ?_⟩
      intro q hq hqa
      exact (hL ⟨q, Finset.mem_filter.mpr ⟨hq, hqa⟩⟩).elim
  obtain ⟨c, hca, hc⟩ := lower_bound
  have hden : 0 < b - a + 1 := by linarith
  let t : ℚ := (a - c) / (b - a + 1)
  have ht : 0 < t := div_pos (sub_pos.mpr hca) hden
  have htden : t * (b - a + 1) = a - c := by
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  let f : ℚ → ℚ := fun x => c + t * (x - a + 1)
  let g : ℚ → ℚ := fun y => a - 1 + (y - c) / t
  have hgf (x : ℚ) : g (f x) = x := by
    dsimp only [g, f]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (ne_of_gt ht)]
    ring
  have hf (x : ℚ) (hx : x ∈ X) : c < f x ∧ f x < a := by
    obtain ⟨hax, hxb⟩ := hX x hx
    have hpos : 0 < t * (x - a + 1) := mul_pos ht (by linarith)
    have hlt : t * (x - a + 1) < t * (b - a + 1) :=
      mul_lt_mul_of_pos_left (by linarith) ht
    rw [htden] at hlt
    change c < c + t * (x - a + 1) ∧ c + t * (x - a + 1) < a
    constructor <;> linarith
  let N := X.image f
  refine ⟨N, g, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨ha, (hf x hx).2, fun q hq hqa => (hc q hq hqa).trans_lt (hf x hx).1⟩
  · apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hn
      rwa [hgf]
    · intro hx
      exact Finset.mem_image.mpr ⟨f x, Finset.mem_image_of_mem f hx, hgf x⟩
  · intro x _ y _ hxy
    change a - 1 + (x - c) / t < a - 1 + (y - c) / t
    have hdiv : (x - c) / t < (y - c) / t :=
      div_lt_div_of_pos_right (sub_lt_sub_right hxy c) ht
    linarith

namespace DownData

variable {α : Type*} [LinearOrder α]
variable {P : Str α} {k : Lvl} {a b : α} {X N : Finset α} {g : α → α}

/-- The new block has exactly as many points as the reflected set. -/
theorem card_new (D : DownData P k a b X N g) : N.card = X.card := by
  classical
  have hinj : Set.InjOn g N := by
    intro x hx y hy hxy
    exact le_antisymm ((D.g_le_iff hx hy).mp hxy.le) ((D.g_le_iff hy hx).mp hxy.ge)
  calc
    N.card = (N.image g).card := (Finset.card_image_iff.mpr hinj).symm
    _ = X.card := congrArg Finset.card D.himage

/-- Downward reflection adds exactly one new point for each reflected point. -/
theorem card_universe (D : DownData P k a b X N g) :
    (P.downward k a b N g).U.card = P.U.card + X.card := by
  classical
  have hdisj : Disjoint P.U N := Finset.disjoint_left.mpr (fun n hnP hnN => D.hNP n hnN hnP)
  change (P.U ∪ N).card = P.U.card + X.card
  rw [Finset.card_union_of_disjoint hdisj, D.card_new]

/-- A nonempty downward reflection strictly enlarges the universe. -/
theorem card_lt (D : DownData P k a b X N g) :
    P.U.card < (P.downward k a b N g).U.card := by
  rw [D.card_universe]
  have hpos : 0 < X.card := Finset.card_pos.mpr D.hXne
  simpa using Nat.add_lt_add_left hpos P.U.card

/-- On rational labels the source hypotheses suffice to construct all of the
placement data for downward reflection; no copy is assumed in advance. -/
theorem exists_rat {P : Str ℚ} {k : Lvl} {a b : ℚ} {X : Finset ℚ}
    (hP : P.IsPattern) (ha : a ∈ P.U) (hb : b ∈ P.U) (hab : a < b)
    (hrel : P.rel k a b) (hX : ∀ x ∈ X, x ∈ P.U ∧ a ≤ x ∧ x < b)
    (hXne : X.Nonempty) : ∃ (N : Finset ℚ) (g : ℚ → ℚ), DownData P k a b X N g := by
  obtain ⟨N, g, hbelow, himage, hmono⟩ :=
    exists_copy_justBelow_rat P.U X ha hab (fun x hx => (hX x hx).2)
  refine ⟨N, g, hP, ha, hb, hab, hrel, hX, hXne, ?_, ?_, ?_, himage, hmono⟩
  · intro n hn
    exact (hbelow n hn).not_mem
  · intro n hn
    exact (hbelow n hn).2.1
  · intro n hn
    exact (hbelow n hn).2.2

end DownData

/-- A permitted downward reflection on rational labels exists as a pattern,
is a continuous extension at its target, and is cofinally valid. Its universe
has exactly `X.card` more points than the source universe. -/
theorem exists_downward_extension_rat {P : Str ℚ} {k : Lvl} {a b : ℚ} {X : Finset ℚ}
    (hP : P.IsPattern) (ha : a ∈ P.U) (hb : b ∈ P.U) (hab : a < b)
    (hrel : P.rel k a b) (hX : ∀ x ∈ X, x ∈ P.U ∧ a ≤ x ∧ x < b)
    (hXne : X.Nonempty) :
    ∃ Q : Str ℚ, Q.IsPattern ∧ Continuous P Q ∧ ExtensionAt P Q a ∧
      CofinallyValid P Q ∧ Q.U.card = P.U.card + X.card := by
  obtain ⟨N, g, D⟩ := DownData.exists_rat hP ha hb hab hrel hX hXne
  exact ⟨P.downward k a b N g, D.isPattern, D.continuous, D.extensionAt,
    D.cofinallyValid, D.card_universe⟩

/-- Reflecting the singleton `{a}` inserts one point just below `a`. -/
theorem exists_one_point_downward_extension_rat {P : Str ℚ} {k : Lvl} {a b : ℚ}
    (hP : P.IsPattern) (ha : a ∈ P.U) (hb : b ∈ P.U) (hab : a < b)
    (hrel : P.rel k a b) :
    ∃ Q : Str ℚ, Q.IsPattern ∧ Continuous P Q ∧ ExtensionAt P Q a ∧
      CofinallyValid P Q ∧ Q.U.card = P.U.card + 1 := by
  have hX : ∀ x ∈ ({a} : Finset ℚ), x ∈ P.U ∧ a ≤ x ∧ x < b := by
    intro x hx
    have hxa : x = a := Finset.mem_singleton.mp hx
    subst x
    exact ⟨ha, le_rfl, hab⟩
  simpa using exists_downward_extension_rat hP ha hb hab hrel hX (Finset.singleton_nonempty a)

end Str

end Alexander313.Carlson
