import Alexander313.Wilken.HereditaryNativeRelativeHighRewriteGlobal
import Alexander313.Wilken.HereditaryLastExponentAddition

/-!
# Actual residual suprema in both relative high-tail branches

The entire bounded residual family has a genuine finite witness. This gives
its real principal closure and the strict tail bound. In the shifted branch,
the original higher presentation makes alpha an actual fixed residual.
Splitting the original supremum at alpha then gives the target supremum;
every image after alpha uses the proved high-tail rewrite. No fixed-point,
supremum, elementarity or transport oracle is supplied.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeZeta.Support

open SourceFixedPointLimits Iota.AlphaPlus RelativeHighRewrite

theorem global_collapse_bounds (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hAs : A < omegaSequence τ 2) :
    τ ≤ globalCollapse τ 0 A ∧ globalCollapse τ 0 A < omegaSequence τ 1 := by
  obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness τ hτ 1 hA
  have hn0 : 0 < n := by omega
  have hb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hAn hAs
  rw [globalCollapse_finite_agreement τ hτ n 0 hn0 A hb]
  exact ⟨by simpa only [omegaSequence_zero] using (sourceFiniteCollapse_bounds τ n 0 hn0 A).1,
    sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hAn⟩

theorem global_next_notation (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (Γ : Ordinal.{0})
    (hΓ : GlobalNotation τ 1 Γ) : GlobalNotation α 1 Γ := by
  obtain ⟨n, hn, hΓn⟩ := globalNotation_finite_witness τ hτ 1 hΓ
  exact sourceNotation_to_globalNotation α (hτ.trans_le hle) n 1 hn
    ((next_notation_iff τ α hle hlt n hn Γ).mp hΓn)

theorem global_tail_lt_collapse (τ : Ordinal.{0}) (hτ : 0 < τ)
    (Γ : Ordinal.{0}) (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    ρ < globalCollapse τ 0 (Γ + ρ) := by
  obtain ⟨n, hn, hΓn⟩ := globalNotation_finite_witness τ hτ 1 hΓ
  have hn0 : 0 < n := by omega
  let gn : SourceNotationOrdinal τ n 1 := ⟨Γ, hΓn⟩
  have hs := shiftArgument_sort τ n 0 hn0 gn hΓs ρ hρ
  have hb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn
    (shiftArgument τ n 0 hn0 gn ρ hρ).property hs
  rw [globalCollapse_finite_agreement τ hτ n 0 hn0 _ hb]
  exact tail_lt_collapse τ hτ n 0 hn0 gn hΓs hΓd ρ hρ

theorem global_sup_add_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (Γ : Ordinal.{0}) (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    Ordinal.IsPrincipal (· + ·) (globalResidualImageSup τ 0 Γ ρ) := by
  obtain ⟨n, hn, hΓn⟩ := globalNotation_finite_witness τ hτ 1 hΓ
  have hn0 : 0 < n := by omega
  let gn : SourceNotationOrdinal τ n 1 := ⟨Γ, hΓn⟩
  rw [globalResidualImageSup_finite_agreement τ hτ n 0 hn gn hΓs ρ hρ]
  exact residualImageSup_add_closed τ n 0 hn0 Γ ρ

theorem global_sup_zero (τ Γ : Ordinal.{0}) : globalResidualImageSup τ 0 Γ 0 = 0 :=
  Ordinal.bsup_zero _

/-- The original larger high part supplies alpha's genuine fixed
presentation at the smaller head. -/
theorem source_head_below_fixed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η Γ : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hA0 : GlobalNotation τ 0 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : GlobalNotation τ 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓΔ : Γ < Δ) (hbelow : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 A) :
    globalResidualImageSup τ 0 Γ (globalCollapse τ 0 A) = globalCollapse τ 0 A := by
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΓs : Γ < omegaSequence τ 2 := (hΓΔ.trans_le hΔA).trans hAs
  have hb := global_collapse_bounds τ hτ A hA hAs
  let gg : GlobalNotationOrdinal τ 1 := ⟨Γ, hΓ⟩
  let ag : GlobalNotationOrdinal τ 1 := ⟨A, hA⟩
  have hstar : globalStar τ hτ 0 gg < globalCollapse τ 0 A :=
    (globalStar_lt_globalCollapse τ hτ 0 gg hΓs).trans_le hbelow
  exact global_higherPresentation_fixed τ hτ 0 gg hΓs hΓd _ hb.2
    ⟨ag, Δ, η, hA0, hAs, hΔ, hη, he, hΓΔ, rfl, hstar⟩

/-- For a positive tail, the smaller-head image at zero is already
strictly above alpha. This is a true tail bound in the original source. -/
theorem source_head_below_sup_base_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η Γ : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hAs : A < omegaSequence τ 2)
    (hΔ : omegaSequence τ 1 ∣ Δ) (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : GlobalNotation τ 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓ0 : 0 < Γ) (hΓΔ : Γ < Δ) (hbelow : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 A)
    (ρ : Ordinal.{0}) (hρ0 : 0 < ρ) :
    globalCollapse τ 0 A < globalResidualImageSup (globalCollapse τ 0 A) 0 Γ ρ := by
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΓs : Γ < omegaSequence τ 2 := (hΓΔ.trans_le hΔA).trans hAs
  have hb := global_collapse_bounds τ hτ A hA hAs
  have ht := global_tail_lt_collapse τ hτ Γ hΓ hΓs hΓd _ hb.2
  have hw := global_relative_tail_eq_of_source_head_below τ hτ A Δ η Γ hA hAs hΔ hη he
    hΓ hΓd hΓ0 hΓΔ hbelow 0 (next_cardinal_pos τ hτ 0)
  simp only [add_zero] at hw
  rw [← hw] at ht
  exact ht.trans_le (by
    simpa only [add_zero] using
      (Ordinal.le_bsup (fun σ _ => globalCollapse (globalCollapse τ 0 A) 0 (Γ + σ)) 0 hρ0))

/-- The shifted original supremum equals the target supremum for EVERY
positive low tail. Images before alpha are bounded by its actual fixed
supremum; later images use the real high-tail rewrite. -/
theorem source_head_below_sup_shift (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η Γ : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hA0 : GlobalNotation τ 0 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : GlobalNotation τ 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓ0 : 0 < Γ) (hΓΔ : Γ < Δ) (hbelow : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 A)
    (ρ : Ordinal.{0}) (hρ0 : 0 < ρ) (hρ : ρ < omegaSequence τ 1) :
    globalResidualImageSup τ 0 Γ (globalCollapse τ 0 A + ρ) =
      globalResidualImageSup (globalCollapse τ 0 A) 0 Γ ρ := by
  let α := globalCollapse τ 0 A
  have hf := source_head_below_fixed τ hτ A Δ η Γ hA hA0 hAs hΔ hη he hΓ hΓd hΓΔ hbelow
  have hb := source_head_below_sup_base_lt τ hτ A Δ η Γ hA hAs hΔ hη he
    hΓ hΓd hΓ0 hΓΔ hbelow ρ hρ0
  apply le_antisymm
  · apply Ordinal.bsup_le
    intro σ hσ
    by_cases hσα : σ < α
    · have hl : globalCollapse τ 0 (Γ + σ) ≤ globalResidualImageSup τ 0 Γ α :=
        Ordinal.le_bsup _ σ hσα
      exact (hl.trans_eq hf).trans hb.le
    · have hασ : α ≤ σ := le_of_not_gt hσα
      have hk : σ - α < ρ := Ordinal.sub_lt_of_lt_add hσ hρ0
      have hkΩ := hk.trans hρ
      have hw := global_relative_tail_eq_of_source_head_below τ hτ A Δ η Γ
        hA hAs hΔ hη he hΓ hΓd hΓ0 hΓΔ hbelow (σ - α) hkΩ
      calc
        globalCollapse τ 0 (Γ + σ) = globalCollapse τ 0 (Γ + (α + (σ - α))) := by
          rw [Ordinal.add_sub_cancel_of_le hασ]
        _ = globalCollapse α 0 (Γ + (σ - α)) := hw.symm
        _ ≤ globalResidualImageSup α 0 Γ ρ := Ordinal.le_bsup _ _ hk
  · apply Ordinal.bsup_le
    intro σ hσ
    have hw := global_relative_tail_eq_of_source_head_below τ hτ A Δ η Γ
      hA hAs hΔ hη he hΓ hΓd hΓ0 hΓΔ hbelow σ (hσ.trans hρ)
    exact hw.trans_le (Ordinal.le_bsup _ (α + σ) ((add_lt_add_iff_left α).mpr hσ))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeZeta.Support
