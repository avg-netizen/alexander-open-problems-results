import Alexander313.Wilken.HereditaryNativeRelativeZetaSupport

/-!
# Genuine strict-residual and zeta transport in the high-tail branches

Both statements use the literal Definition 2.42 supremum. The unchanged
branch transports every image directly. In the shifted branch, the actual
original higher presentation settles residual zero; at a positive residual,
the actual supremum equality and its principal closure transport STRICT.
The last-exponent identity then yields the real zeta value. All source
notation, divided high-part and original outer-root conditions are explicit;
no strictness, fixedness, supremum or zeta identity is assumed.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeZeta

open SourceFixedPointLimits Iota.AlphaPlus RelativeHighRewrite Support

/-- The literal mathematical value in Definition 2.42 at a divided head
and low residual. This is not an executing producer or a new input guard. -/
noncomputable def zetaValue (τ Γ ρ : Ordinal.{0}) : Ordinal.{0} :=
  if ρ < globalResidualImageSup τ 0 Γ ρ then Hereditary.SourceZeta.lastExponent ρ else 0

theorem source_head_above_sup (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (Γ : Ordinal.{0})
    (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (habove : α < globalCollapse τ 0 Γ)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    globalResidualImageSup α 0 Γ ρ = globalResidualImageSup τ 0 Γ ρ := by
  unfold globalResidualImageSup
  congr 1
  funext σ hσ
  exact global_relative_tail_eq_of_source_head_above τ α hτ hle hlt Γ
    hΓ hΓs hΓd habove σ (hσ.trans hρ)

theorem source_head_above_strict (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (Γ : Ordinal.{0})
    (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (habove : α < globalCollapse τ 0 Γ)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    (ρ < globalResidualImageSup α 0 Γ ρ) ↔ (ρ < globalResidualImageSup τ 0 Γ ρ) := by
  rw [source_head_above_sup τ α hτ hle hlt Γ hΓ hΓs hΓd habove ρ hρ]

theorem source_head_above_zeta (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (Γ : Ordinal.{0})
    (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (habove : α < globalCollapse τ 0 Γ)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    zetaValue α Γ ρ = zetaValue τ Γ ρ := by
  simp only [zetaValue,
    source_head_above_sup τ α hτ hle hlt Γ hΓ hΓs hΓd habove ρ hρ]

/-- Positive residuals preserve the TRUE strict comparison under insertion
of alpha. The proof uses principal closure of the actual target supremum. -/
theorem source_head_below_strict (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η Γ : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hA0 : GlobalNotation τ 0 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : GlobalNotation τ 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓ0 : 0 < Γ) (hΓΔ : Γ < Δ) (hbelow : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 A)
    (ρ : Ordinal.{0}) (hρ0 : 0 < ρ) (hρ : ρ < omegaSequence τ 1) :
    (globalCollapse τ 0 A + ρ < globalResidualImageSup τ 0 Γ (globalCollapse τ 0 A + ρ)) ↔
      (ρ < globalResidualImageSup (globalCollapse τ 0 A) 0 Γ ρ) := by
  let α := globalCollapse τ 0 A
  have hb := global_collapse_bounds τ hτ A hA hAs
  have hα : 0 < α := hτ.trans_le hb.1
  have hΓα := global_next_notation τ α hτ hb.1 hb.2 Γ hΓ
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΓs : Γ < omegaSequence τ 2 := (hΓΔ.trans_le hΔA).trans hAs
  have hΓsα : Γ < omegaSequence α 2 := by
    rw [← omega_succ τ α hb.1 hb.2 1]
    exact hΓs
  have hρα : ρ < omegaSequence α 1 := by
    rw [← omega_succ τ α hb.1 hb.2 0]
    exact hρ
  have hp := global_sup_add_closed α hα Γ hΓα hΓsα ρ hρα
  have hbase := source_head_below_sup_base_lt τ hτ A Δ η Γ hA hAs hΔ hη he
    hΓ hΓd hΓ0 hΓΔ hbelow ρ hρ0
  rw [source_head_below_sup_shift τ hτ A Δ η Γ hA hA0 hAs hΔ hη he
    hΓ hΓd hΓ0 hΓΔ hbelow ρ hρ0 hρ]
  exact ⟨fun h => (le_add_self : ρ ≤ α + ρ).trans_lt h, fun h => hp hbase h⟩

/-- Both the zero and positive residual cases yield the literal zeta
identity. Zero is settled by the original actual fixed presentation. -/
theorem source_head_below_zeta (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η Γ : Ordinal.{0}) (hA : GlobalNotation τ 1 A) (hA0 : GlobalNotation τ 0 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : GlobalNotation τ 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓ0 : 0 < Γ) (hΓΔ : Γ < Δ) (hbelow : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 A)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    zetaValue τ Γ (globalCollapse τ 0 A + ρ) = zetaValue (globalCollapse τ 0 A) Γ ρ := by
  by_cases hz : ρ = 0
  · subst ρ
    have hf := source_head_below_fixed τ hτ A Δ η Γ hA hA0 hAs hΔ hη he
      hΓ hΓd hΓΔ hbelow
    simp only [zetaValue, add_zero, hf, global_sup_zero, lt_self_iff_false, if_false]
  · have hρ0 : 0 < ρ := pos_iff_ne_zero.mpr hz
    have hs := source_head_below_strict τ hτ A Δ η Γ hA hA0 hAs hΔ hη he
      hΓ hΓd hΓ0 hΓΔ hbelow ρ hρ0 hρ
    unfold zetaValue
    by_cases ht : ρ < globalResidualImageSup (globalCollapse τ 0 A) 0 Γ ρ
    · rw [if_pos (hs.mpr ht), if_pos ht]
      exact Hereditary.LastExponentAddition.lastExponent_add _ ρ hρ0
    · rw [if_neg (fun h => ht (hs.mp h)), if_neg ht]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeZeta
