import Alexander313.Wilken.HereditaryNativeRelativeHighRewriteSupport

/-!
# The original-root branch of high relative collapse rewriting

When the source collapse of a positive divided head is at most the new
base, its original own hull embeds into the ORIGINAL root hull. This
licenses every extra same-head call with low tail below alpha. Remaining
same-head calls have tail alpha+sigma with sigma genuinely smaller than the
target tail, and an ordinal induction gives their same-value rewrite.
The result is the second actual branch toward the bounded translator.
No shifted-collapse equality, extra hull membership, comparison or admission
oracle is assumed. These semantic kernels do not yet implement a finite
whole-term translator. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeHighRewrite

open SourceFixedPointLimits Iota.AlphaPlus RelativeCollapseMonotonicity

/-- The lower-head branch returns the actual value by adding the original
root alpha to its low tail. The original root and divided-head premises are
explicit mathematical support domains, not an extra purported caller guard. -/
theorem relative_tail_eq_of_source_head_below (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 1 < n) (A Δ η Γ : Ordinal.{0})
    (hA : sourceNotation τ n 1 A) (hAs : A < omegaSequence τ 2)
    (hΔ : omegaSequence τ 1 ∣ Δ) (hη : η < omegaSequence τ 1) (he : A = Δ + η)
    (hΓ : sourceNotation τ n 1 Γ) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΓ0 : 0 < Γ) (hΓΔ : Γ < Δ)
    (hbelow : sourceFiniteCollapse τ n 0 Γ ≤ sourceFiniteCollapse τ n 0 A)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    sourceFiniteCollapse (sourceFiniteCollapse τ n 0 A) n 0 (Γ + ρ) =
      sourceFiniteCollapse τ n 0 (Γ + (sourceFiniteCollapse τ n 0 A + ρ)) := by
  classical
  let α := sourceFiniteCollapse τ n 0 A
  have hn0 : 0 < n := by omega
  have hle : τ ≤ α := by simpa only [omegaSequence_zero] using
    (sourceFiniteCollapse_bounds τ n 0 hn0 A).1
  have hαs : α < omegaSequence τ 1 :=
    sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hA
  have hαp : 0 < α := hτ.trans_le hle
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΓA : Γ < A := hΓΔ.trans_le hΔA
  have hΓs : Γ < omegaSequence τ 2 := hΓA.trans hAs
  have hΓa := (next_notation_iff τ α hle hαs n hn Γ).mp hΓ
  have hΓsa : Γ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hαs 1] using hΓs
  have hΓda : omegaSequence α 1 ∣ Γ := by
    simpa only [← omega_succ τ α hle hαs 0] using hΓd
  have hΓhigh : omegaSequence α 1 ≤ Γ := Ordinal.le_of_dvd hΓ0.ne' hΓda
  have hΓown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A α Γ :=
    hull_mono hΓA.le hbelow
      (sourceFiniteCollapse_argument_notation τ n 0 hn0 Γ hΓs hΓ)
  revert hρ
  refine Ordinal.induction ρ ?_
  intro ρ ih hρ
  let δ := Γ + ρ
  let γ := Γ + (α + ρ)
  let β := sourceFiniteCollapse α n 0 δ
  have hd := (shiftArgument τ n 0 hn0 ⟨Γ, hΓ⟩ ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓ⟩ hΓs ρ hρ
  have hda := (next_notation_iff τ α hle hαs n hn δ).mp hd
  have hdsa : δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hαs 1] using hds
  have hβa : β < omegaSequence α 1 :=
    sourceFiniteCollapse_proper_notation α n 0 hn0 δ hdsa hda
  have hβs : β < omegaSequence τ 1 := by
    simpa only [omega_succ τ α hle hαs 0] using hβa
  have hαβ : α < β := by
    simpa only [omegaSequence_zero] using sourceFiniteCollapse_high_base_lt α hαp n 0 hn0 δ
      (hΓhigh.trans le_self_add)
  have hρa : ρ < omegaSequence α 1 := by
    simpa only [← omega_succ τ α hle hαs 0] using hρ
  have hρβ : ρ < β := tail_lt_collapse α hαp n 0 hn0
    ⟨Γ, hΓa⟩ hΓsa hΓda ρ hρa
  have htail : α + ρ < omegaSequence τ 1 := (omegaSequence_add_closed τ 0) hαs hρ
  have hγs : γ < omegaSequence τ 2 :=
    shiftArgument_sort τ n 0 hn0 ⟨Γ, hΓ⟩ hΓs (α + ρ) htail
  have hΓγ : Γ ≤ γ := le_self_add
  have hΓsource : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β Γ :=
    hull_mono hΓγ (hbelow.trans hαβ.le)
      (sourceFiniteCollapse_argument_notation τ n 0 hn0 Γ hΓs hΓ)
  have harg : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β γ :=
    .add hΓsource (.add (.below_parameter hαβ) (.below_parameter hρβ))
  have forward {ξ : Ordinal.{0}}
      (hx : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β ξ) :
      Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ξ := by
    induction hx with
    | below_base h => exact .below_base (h.trans_le hle)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihζ => exact .add ihξ ihζ
    | @higher k ζ hk hkn hs hζ ihζ =>
      rw [positive_collapse τ α hle hαs n k hk hkn ζ]
      exact .higher hk hkn (by simpa only [← omega_succ τ α hle hαs (k + 1)] using hs) ihζ
    | @«local» ζ hζγ hζ ihζ =>
      by_cases hζΓ : ζ < Γ
      · have hζs : ζ < omegaSequence τ 2 := hζΓ.trans hΓs
        have hζn := source_hull_next_notation α n 0 hn0 hdsa.le hβa.le ihζ
        have hζδ : ζ < δ := hζΓ.trans_le le_self_add
        have hζp := sourceFiniteCollapse_proper_notation α n 0 hn0 ζ
          (hζδ.trans hdsa) hζn
        have hc : sourceFiniteCollapse α n 0 ζ < β :=
          (finiteCollapse_hull_initial hn0 δ _).mp ⟨.local hζδ ihζ, hζp⟩
        exact .below_parameter ((finite_collapse_mono_base τ α hτ hle hαs n hn
          ζ hζn hζs).trans_lt hc)
      · have hΓζ : Γ ≤ ζ := le_of_not_gt hζΓ
        let σ := ζ - Γ
        have hζeq : Γ + σ = ζ := Ordinal.add_sub_cancel_of_le hΓζ
        have hσtail : σ < α + ρ := by
          apply (add_lt_add_iff_left Γ).mp
          rw [hζeq]
          exact hζγ
        have hσs : σ < omegaSequence τ 1 := hσtail.trans htail
        by_cases hσα : σ < α
        · have hζown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A α ζ := by
            rw [← hζeq]
            exact .add hΓown (.below_parameter hσα)
          have hζΔ : ζ < Δ := by
            rw [← hζeq]
            exact multiple_add_low_lt_of_lt (omegaSequence τ 1) Γ Δ σ
              (next_cardinal_pos τ hτ 0) hΓd hΔ hΓΔ hσs
          have hζA : ζ < A := hζΔ.trans_le hΔA
          have hζn := source_hull_next_notation τ n 0 hn0 hAs.le hαs.le hζown
          have hζp := sourceFiniteCollapse_proper_notation τ n 0 hn0 ζ (hζA.trans hAs) hζn
          exact .below_parameter (((finiteCollapse_hull_initial hn0 A _).mp
            ⟨.local hζA hζown, hζp⟩).trans hαβ)
        · have hασ : α ≤ σ := le_of_not_gt hσα
          let ε := σ - α
          have hσε : α + ε = σ := Ordinal.add_sub_cancel_of_le hασ
          have hερ : ε < ρ := by
            apply (add_lt_add_iff_left α).mp
            rw [hσε]
            exact hσtail
          have hεσ : ε ≤ σ := Ordinal.sub_le_self σ α
          have hσa : σ < omegaSequence α 1 := by
            simpa only [← omega_succ τ α hle hαs 0] using hσs
          have hsplit := (source_hull_multiple_add_low_iff α hαp n 0 hn0 δ β
            Γ σ hΓda hσa).mp (by simpa only [hζeq] using ihζ)
          have hεHull : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ε := by
            rcases hεσ.eq_or_lt with he | he
            · simpa only [← he] using hsplit.2
            · exact source_hull_initial_segment α hαp n 0 hn0 δ β hdsa.le hβa
                hsplit.2 hσa he
          have hsmaller : Γ + ε < δ := (Ordinal.isNormal_add_right Γ).strictMono hερ
          have heζ : ζ = Γ + (α + ε) := hζeq.symm.trans (congrArg (Γ + ·) hσε.symm)
          have hrewrite : sourceFiniteCollapse τ n 0 ζ = sourceFiniteCollapse α n 0 (Γ + ε) := by
            rw [heζ]
            exact (ih ε hερ (hερ.trans hρ)).symm
          rw [hrewrite]
          exact .local hsmaller (.add hsplit.1 hεHull)
  apply le_antisymm
  · have hb := relative_collapse_le_tailShift τ α hτ hle hαs n hn δ hda hds
    simpa only [δ, tailShift_multiple_add_low _ α Γ ρ (next_cardinal_pos τ hτ 0) hΓd hρ] using hb
  · apply finiteCollapse_minimal hn0
    refine ⟨hβs, ?_, harg⟩
    intro ξ hx hs
    exact (finiteCollapse_hull_initial hn0 δ ξ).mp
      ⟨forward hx, by simpa only [← omega_succ τ α hle hαs 0] using hs⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeHighRewrite
