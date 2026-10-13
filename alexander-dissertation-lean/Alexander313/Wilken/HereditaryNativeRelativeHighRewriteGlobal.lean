import Alexander313.Wilken.HereditaryNativeRelativeHighRewrite

/-!
# Actual global high-tail rewriting at the original root

The finite branch kernels are transported to actual globalCollapse by
genuine common source fragments and sorted finite/global fidelity. Every
target argument and every shifted source argument is derived from original
notation and the low tail; no finite fragment or target caller is assumed.
These are semantic kernels for the finite bounded public return.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeHighRewrite

open SourceFixedPointLimits Iota.AlphaPlus

theorem global_relative_tail_eq_of_source_head_above (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (Γ : Ordinal.{0})
    (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (habove : α < globalCollapse τ 0 Γ)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    globalCollapse α 0 (Γ + ρ) = globalCollapse τ 0 (Γ + ρ) := by
  obtain ⟨n, hn, hΓn⟩ := globalNotation_finite_witness τ hτ 1 hΓ
  have hn0 : 0 < n := by omega
  have hαp : 0 < α := hτ.trans_le hle
  have hΓb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hΓn hΓs
  have hhead : α < sourceFiniteCollapse τ n 0 Γ := by
    rwa [globalCollapse_finite_agreement τ hτ n 0 hn0 Γ hΓb] at habove
  have hd := (shiftArgument τ n 0 hn0 ⟨Γ, hΓn⟩ ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓn⟩ hΓs ρ hρ
  have hda := (next_notation_iff τ α hle hlt n hn (Γ + ρ)).mp hd
  have hdsa : Γ + ρ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hds
  have hdb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hd hds
  have hdab := source_finite_notation_sorted_lt_boundary α hαp n 1 1 le_rfl hn hda hdsa
  rw [globalCollapse_finite_agreement α hαp n 0 hn0 _ hdab,
    globalCollapse_finite_agreement τ hτ n 0 hn0 _ hdb]
  exact relative_tail_eq_of_source_head_above τ α hτ hle hlt n hn Γ hΓn hΓs hΓd hhead ρ hρ

theorem global_relative_tail_eq_of_source_head_below (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η Γ : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hAs : A < omegaSequence τ 2)
    (hΔ : omegaSequence τ 1 ∣ Δ) (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : GlobalNotation τ 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓ0 : 0 < Γ) (hΓΔ : Γ < Δ) (hbelow : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 A)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    globalCollapse (globalCollapse τ 0 A) 0 (Γ + ρ) =
      globalCollapse τ 0 (Γ + (globalCollapse τ 0 A + ρ)) := by
  obtain ⟨nA, hnA, hAnA⟩ := globalNotation_finite_witness τ hτ 1 hA
  obtain ⟨nΓ, hnΓ, hΓnΓ⟩ := globalNotation_finite_witness τ hτ 1 hΓ
  let n := max nA nΓ
  have hn : 1 < n := hnA.trans_le (le_max_left _ _)
  have hn0 : 0 < n := by omega
  have hAn := sourceNotation_fragment_mono τ hτ nA 1 n hnA.le (le_max_left _ _) hAnA
  have hΓn := sourceNotation_fragment_mono τ hτ nΓ 1 n hnΓ.le (le_max_right _ _) hΓnΓ
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΓA : Γ < A := hΓΔ.trans_le hΔA
  have hΓs : Γ < omegaSequence τ 2 := hΓA.trans hAs
  have hAb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hAn hAs
  have hΓb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hΓn hΓs
  let α := globalCollapse τ 0 A
  have hα : α = sourceFiniteCollapse τ n 0 A :=
    globalCollapse_finite_agreement τ hτ n 0 hn0 A hAb
  have hhead : sourceFiniteCollapse τ n 0 Γ ≤ sourceFiniteCollapse τ n 0 A := by
    rwa [globalCollapse_finite_agreement τ hτ n 0 hn0 Γ hΓb, hα] at hbelow
  have hle : τ ≤ α := by
    rw [hα]
    simpa only [omegaSequence_zero] using (sourceFiniteCollapse_bounds τ n 0 hn0 A).1
  have hlt : α < omegaSequence τ 1 := by
    rw [hα]
    exact sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hAn
  have hαp : 0 < α := hτ.trans_le hle
  have hd := (shiftArgument τ n 0 hn0 ⟨Γ, hΓn⟩ ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓn⟩ hΓs ρ hρ
  have hda := (next_notation_iff τ α hle hlt n hn (Γ + ρ)).mp hd
  have hdsa : Γ + ρ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hds
  have hdab := source_finite_notation_sorted_lt_boundary α hαp n 1 1 le_rfl hn hda hdsa
  have htail : α + ρ < omegaSequence τ 1 := (omegaSequence_add_closed τ 0) hlt hρ
  have hg := (shiftArgument τ n 0 hn0 ⟨Γ, hΓn⟩ (α + ρ) htail).property
  have hgs := shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓn⟩ hΓs (α + ρ) htail
  have hgb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hg hgs
  change globalCollapse α 0 (Γ + ρ) = globalCollapse τ 0 (Γ + (α + ρ))
  rw [globalCollapse_finite_agreement α hαp n 0 hn0 _ hdab,
    globalCollapse_finite_agreement τ hτ n 0 hn0 _ hgb, hα]
  exact relative_tail_eq_of_source_head_below τ hτ n hn A Δ η Γ hAn hAs hΔ hη he
    hΓn hΓd hΓ0 hΓΔ hhead ρ hρ

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeHighRewrite
