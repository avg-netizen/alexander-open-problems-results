import Alexander313.Wilken.HereditaryNativeRelativeHighRewrite

/-!
# The actual original head and its successor tail

The original divided argument supplies its head in its OWN minimum hull.
Its low tail is below the actual collapse, and high principal closure makes
the successor of that tail smaller too. Every same-head call before that
successor is bounded by the original root. These are actual source-hull
facts, not a downward-closure assumption above the first cardinal.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeEndpointRewrite

open SourceFixedPointLimits Iota.AlphaPlus RelativeHighRewrite

theorem root_head_own (τ : Ordinal.{0}) (hτ : 0 < τ) (n : Nat) (hn : 1 < n)
    (A Δ η : Ordinal.{0}) (hA : sourceNotation τ n 1 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A
      (sourceFiniteCollapse τ n 0 A) Δ := by
  have hown := sourceFiniteCollapse_argument_notation τ n 0 (by omega) A hAs hA
  have hsplit : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A
      (sourceFiniteCollapse τ n 0 A) (Δ + η) := by rw [← he]; exact hown
  exact ((source_hull_multiple_add_low_iff τ hτ n 0 (by omega) A
    (sourceFiniteCollapse τ n 0 A) Δ η hΔ hη).mp hsplit).1

theorem root_head_notation (τ : Ordinal.{0}) (hτ : 0 < τ) (n : Nat) (hn : 1 < n)
    (A Δ η : Ordinal.{0}) (hA : sourceNotation τ n 1 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η) : sourceNotation τ n 1 Δ := by
  exact source_hull_next_notation τ n 0 (by omega) hAs.le
    (sourceFiniteCollapse_bounds τ n 0 (by omega) A).2
    (root_head_own τ hτ n hn A Δ η hA hAs hΔ hη he)

/-- The actual high root makes even eta+1 a genuine parameter below it. -/
theorem root_tail_successor_lt (τ : Ordinal.{0}) (hτ : 0 < τ) (n : Nat) (hn : 1 < n)
    (A Δ η : Ordinal.{0}) (hA : sourceNotation τ n 1 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hΔ0 : 0 < Δ) (hη : η < omegaSequence τ 1) (he : A = Δ + η) :
    η + 1 < sourceFiniteCollapse τ n 0 A := by
  have hdn := root_head_notation τ hτ n hn A Δ η hA hAs hΔ hη he
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΔs : Δ < omegaSequence τ 2 := hΔA.trans_lt hAs
  have htail : η < sourceFiniteCollapse τ n 0 A := by
    rw [he]
    exact tail_lt_collapse τ hτ n 0 (by omega) ⟨Δ, hdn⟩ hΔs hΔ η hη
  have hhigh : omegaSequence τ 1 ≤ A :=
    (Ordinal.le_of_dvd hΔ0.ne' hΔ).trans hΔA
  have hbase : τ < sourceFiniteCollapse τ n 0 A := by
    simpa only [omegaSequence_zero] using sourceFiniteCollapse_high_base_lt τ hτ n 0
      (by omega) A hhigh
  have hone : 1 < sourceFiniteCollapse τ n 0 A := (Order.one_le_iff_pos.mpr hτ).trans_lt hbase
  exact (Ordinal.isSuccLimit_of_isPrincipal_add hone
    (sourceFiniteCollapse_add_closed τ n 0 (by omega) A)).add_one_lt htail

/-- All extra source calls before the first successor tail are bounded by
the original root, including the actual root call at sigma=eta. -/
theorem same_head_le_root (τ : Ordinal.{0}) (hτ : 0 < τ) (n : Nat) (hn : 1 < n)
    (A Δ η : Ordinal.{0}) (hA : sourceNotation τ n 1 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hΔ0 : 0 < Δ) (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (σ : Ordinal.{0}) (hσ : σ < η + 1) :
    sourceFiniteCollapse τ n 0 (Δ + σ) ≤ sourceFiniteCollapse τ n 0 A := by
  have hση : σ ≤ η := Order.lt_add_one_iff.mp hσ
  have htail := root_tail_successor_lt τ hτ n hn A Δ η hA hAs hΔ hΔ0 hη he
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A
      (sourceFiniteCollapse τ n 0 A) (Δ + σ) :=
    .add (root_head_own τ hτ n hn A Δ η hA hAs hΔ hη he)
      (.below_parameter (hσ.trans htail))
  have harg : Δ + σ ≤ A := by rw [he]; exact add_le_add_left hση Δ
  rcases harg.eq_or_lt with hsame | hsmall
  · rw [hsame]
  · have hβs := sourceFiniteCollapse_proper_notation τ n 0 (by omega) A hAs hA
    have hnotation := source_hull_next_notation τ n 0 (by omega) hAs.le hβs.le hown
    have hp := sourceFiniteCollapse_proper_notation τ n 0 (by omega) (Δ + σ)
      (hsmall.trans hAs) hnotation
    exact ((finiteCollapse_hull_initial (by omega) A _).mp
      ⟨.local hsmall hown, hp⟩).le

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeEndpointRewrite
