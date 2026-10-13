import Alexander313.Carlson.Tallness
import Alexander313.Carlson.FairOrdinalRealization
import Alexander313.Carlson.RationalPresentation

/-!
# Unconditional fair and minimal ordinal realizations

The coveredness premise of the existing fair/minimal realization theorems
is now discharged for every pure rational pattern. This module also bounds
each realized initial segment below `ω₁`, by comparing its pointwise least
seed labels with an actual countable ordinal covering.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal

theorem exists_fair_ordinalRealization_of_pattern (P : Str ℚ) (hP : P.IsPattern) :
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair ∧
      Nonempty (GeneratingSequence.OrdinalRealization S) :=
  GeneratingSequence.exists_fair_ordinalRealization P hP (every_pattern_covered P hP)

theorem exists_minimal_ordinal_copy_of_pattern (P : Str ℚ) (hP : P.IsPattern) :
    ∃ h : ℚ → Ordinal.{0},
      Str.IsIso P (Str.ofOrdinals (P.U.image h)) h ∧
      ∀ g : ℚ → Ordinal.{0}, Str.CoveringR P g → ∀ x ∈ P.U, h x ≤ g x :=
  GeneratingSequence.exists_minimal_ordinal_copy P hP (every_pattern_covered P hP)

/-- A fair initial-segment realization preserving its given finite seed. -/
structure PatternRealization (P : Str ℚ) where
  sequence : GeneratingSequence ℚ
  seed : sequence.stage 0 = P
  fair : sequence.Fair
  ordinal : GeneratingSequence.OrdinalRealization sequence

theorem exists_patternRealization (P : Str ℚ) (hP : P.IsPattern) :
    Nonempty (PatternRealization P) := by
  obtain ⟨S, hzero, hfair, ⟨R⟩⟩ := exists_fair_ordinalRealization_of_pattern P hP
  exact ⟨⟨S, hzero, hfair, R⟩⟩

def PatternRealization.ofPattern (P : Str ℚ) (hP : P.IsPattern) : PatternRealization P :=
  Classical.choice (exists_patternRealization P hP)

namespace PatternRealization

variable {P : Str ℚ} (A : PatternRealization P)

abbrev bound : Ordinal.{0} := A.ordinal.bound
abbrev label : ℚ → Ordinal.{0} := A.ordinal.label

theorem seed_isIso : Str.IsIso P (Str.ofOrdinals (P.U.image A.label)) A.label := by
  simpa only [GeneratingSequence.OrdinalRealization.stagePattern, A.seed] using
    A.ordinal.stage_isIso 0

theorem seed_covering : P.CoveringR A.label := by
  simpa only [A.seed] using A.ordinal.stage_covering 0

theorem seed_minimal {g : ℚ → Ordinal.{0}} (hg : P.CoveringR g)
    {x : ℚ} (hx : x ∈ P.U) : A.label x ≤ g x := by
  apply A.ordinal.label_le_covering 0
  · simpa only [A.seed] using hg
  · simpa only [A.seed] using hx

theorem seed_label_lt_bound {x : ℚ} (hx : x ∈ P.U) : A.label x < A.bound := by
  apply A.ordinal.label_lt_bound
  apply A.sequence.mem_carrier 0
  simpa only [A.seed] using hx

theorem bound_lt_omega_one (hP : P.IsPattern) : A.bound < ω₁ := by
  classical
  obtain ⟨g, hg, hbelow⟩ := exists_covering_below_omega_one P hP
  let c := P.U.sup g + 1
  have hc : c < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt
    ((Finset.sup_lt_iff (Cardinal.isSuccLimit_omega 1).pos).mpr hbelow)
  have hb : A.bound ≤ c := (A.ordinal.bound_le_iff 0 c).mpr (by
    intro x hx
    have hxP : x ∈ P.U := by simpa only [A.seed] using hx
    exact (A.seed_minimal hg hxP).trans_lt
      ((Finset.le_sup (f := g) hxP).trans_lt (lt_add_one _)))
  exact hb.trans_lt hc

end PatternRealization

end Alexander313.Carlson
