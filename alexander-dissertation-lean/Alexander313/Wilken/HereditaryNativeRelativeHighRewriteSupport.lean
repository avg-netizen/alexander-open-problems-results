import Alexander313.Wilken.HereditaryNativeIotaAlphaPlusEquality

/-!
# The genuine high-head branch of same-value relative collapse rewriting

The low tail shift is an upper estimate, not an unconditional equality.
When the source collapse of the divided head is already strictly above the
new base, the SAME argument is correct. A tail induction transfers the real
source minimum to the target: smaller heads use the proved shifted bound,
and calls with the same head use genuinely smaller tails. This is one
mathematical branch toward the bounded finite term translator, not the whole
translator. No candidate, relative-collapse equality or comparison oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeHighRewrite

open SourceFixedPointLimits Iota.AlphaPlus RelativeCollapseMonotonicity

theorem tailShift_multiple_add_low (Ω α Γ ρ : Ordinal.{0}) (hΩ : 0 < Ω)
    (hΓ : Ω ∣ Γ) (hρ : ρ < Ω) :
    tailShift Ω α (Γ + ρ) = Γ + (α + ρ) := by
  obtain ⟨d, rfl⟩ := hΓ
  simp only [tailShift, Ordinal.mul_add_div d hΩ.ne' ρ,
    Ordinal.div_eq_zero_of_lt hρ, add_zero,
    Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hρ]

/-- The actual own hull at head+tail contains the head. If the tail is
nonzero, its local head call is therefore strictly below that minimum. -/
theorem source_head_collapse_le_tail (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 1 < n) (Γ ρ : Ordinal.{0})
    (hΓ : sourceNotation τ n 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (hρ : ρ < omegaSequence τ 1) :
    sourceFiniteCollapse τ n 0 Γ ≤ sourceFiniteCollapse τ n 0 (Γ + ρ) := by
  have hn0 : 0 < n := by omega
  have hd := (shiftArgument τ n 0 hn0 ⟨Γ, hΓ⟩ ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓ⟩ hΓs ρ hρ
  have hown := sourceFiniteCollapse_argument_notation τ n 0 hn0 (Γ + ρ) hds hd
  have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 (Γ + ρ)
    (sourceFiniteCollapse τ n 0 (Γ + ρ)) Γ ρ hΓd hρ).mp hown
  by_cases h0 : ρ = 0
  · simp only [h0, add_zero, le_refl]
  · have hlt : Γ < Γ + ρ := by
      simpa only [add_zero] using (Ordinal.isNormal_add_right Γ).strictMono
        (pos_iff_ne_zero.mpr h0)
    exact ((finiteCollapse_hull_initial hn0 (Γ + ρ) _).mp
      ⟨.local hlt hsplit.1, sourceFiniteCollapse_proper_notation τ n 0 hn0 Γ hΓs hΓ⟩).le

/-- An original source head already above alpha needs NO extra alpha tail.
All tail callers and both actual minima are derived in a genuine ordinal
induction. This clause accepts arbitrary admitted high hidden arguments. -/
theorem relative_tail_eq_of_source_head_above (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (Γ : Ordinal.{0}) (hΓ : sourceNotation τ n 1 Γ)
    (hΓs : Γ < omegaSequence τ 2) (hΓd : omegaSequence τ 1 ∣ Γ)
    (habove : α < sourceFiniteCollapse τ n 0 Γ) (ρ : Ordinal.{0})
    (hρ : ρ < omegaSequence τ 1) :
    sourceFiniteCollapse α n 0 (Γ + ρ) = sourceFiniteCollapse τ n 0 (Γ + ρ) := by
  classical
  revert hρ
  refine Ordinal.induction ρ ?_
  intro ρ ih hρ
  have hn0 : 0 < n := by omega
  let δ := Γ + ρ
  let β := sourceFiniteCollapse τ n 0 δ
  have hd := (shiftArgument τ n 0 hn0 ⟨Γ, hΓ⟩ ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓ⟩ hΓs ρ hρ
  have hda := (next_notation_iff τ α hle hlt n hn δ).mp hd
  have hdsa : δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hds
  have hβs : β < omegaSequence τ 1 :=
    sourceFiniteCollapse_proper_notation τ n 0 hn0 δ hds hd
  have hαβ : α < β := habove.trans_le
    (source_head_collapse_le_tail τ hτ n hn Γ ρ hΓ hΓs hΓd hρ)
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 δ β δ :=
    sourceFiniteCollapse_argument_notation τ n 0 hn0 δ hds hd
  have harg := source_minimum_hull_to_target τ α hτ hle hlt n hn
    δ hd hds δ δ hown
  have forward {ξ : Ordinal.{0}}
      (hx : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ξ) :
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 δ β ξ := by
    induction hx with
    | below_base h => exact .below_parameter (h.trans hαβ)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihζ => exact .add ihξ ihζ
    | @higher k ζ hk hkn hs hζ ihζ =>
      rw [← positive_collapse τ α hle hlt n k hk hkn ζ]
      exact .higher hk hkn (by simpa only [omega_succ τ α hle hlt (k + 1)] using hs) ihζ
    | @«local» ζ hζδ hζ ihζ =>
      by_cases hζΓ : ζ < Γ
      · have hζs : ζ < omegaSequence τ 2 := hζΓ.trans hΓs
        have hζn := source_hull_next_notation α n 0 hn0 hdsa.le
          (by simpa only [← omega_succ τ α hle hlt 0] using hβs.le) hζ
        have hb := relative_collapse_le_tailShift τ α hτ hle hlt n hn ζ hζn hζs
        have hmod := Ordinal.mod_lt ζ (next_cardinal_pos τ hτ 0).ne'
        have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 δ β
          (omegaSequence τ 1 * (ζ / omegaSequence τ 1)) (ζ % omegaSequence τ 1)
          ⟨ζ / omegaSequence τ 1, rfl⟩ hmod).mp
          (by simpa only [Ordinal.div_add_mod] using ihζ)
        have hf : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 δ β
            (tailShift (omegaSequence τ 1) α ζ) :=
          .add hsplit.1 (.add (.below_parameter hαβ) hsplit.2)
        have hfΓ := tailShift_lt_multiple (omegaSequence τ 1) α ζ Γ
          (next_cardinal_pos τ hτ 0) (omegaSequence_add_closed τ 0) hlt hΓd hζΓ
        have hfδ : tailShift (omegaSequence τ 1) α ζ < δ := hfΓ.trans_le le_self_add
        have hfn := source_hull_next_notation τ n 0 hn0 hds.le hβs.le hf
        have hfp := sourceFiniteCollapse_proper_notation τ n 0 hn0 _ (hfδ.trans hds) hfn
        exact .below_parameter (hb.trans_lt
          ((finiteCollapse_hull_initial hn0 δ _).mp ⟨.local hfδ hf, hfp⟩))
      · have hΓζ : Γ ≤ ζ := le_of_not_gt hζΓ
        have htail : ζ - Γ < ρ := by
          apply (add_lt_add_iff_left Γ).mp
          rw [Ordinal.add_sub_cancel_of_le hΓζ]
          exact hζδ
        have he : sourceFiniteCollapse α n 0 ζ = sourceFiniteCollapse τ n 0 ζ := by
          rw [← Ordinal.add_sub_cancel_of_le hΓζ]
          exact ih (ζ - Γ) htail (htail.trans hρ)
        rw [he]
        exact .local hζδ ihζ
  apply le_antisymm
  · apply finiteCollapse_minimal hn0
    refine ⟨?_, ?_, harg⟩
    · simpa only [← omega_succ τ α hle hlt 0] using hβs
    · intro ξ hx hs
      exact (finiteCollapse_hull_initial hn0 δ ξ).mp
        ⟨forward hx, by simpa only [omega_succ τ α hle hlt 0] using hs⟩
  · exact finite_collapse_mono_base τ α hτ hle hlt n hn δ hda hds

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeHighRewrite
