import Alexander313.Wilken.HereditaryNativeRelativeEndpointRewrite

/-!
# Actual minima after a genuine low-tail cutoff

A source head whose collapse is at most the new base can be relativized by
inserting its first genuine low-tail crossing. This compares BOTH actual
minima; every prior same-head source call is controlled by the stated
cutoff and every later call recurses on a smaller tail. The original native
selected-support theorem supplies these mathematical cutoff hypotheses
separately. No equality or candidate oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeCutoffRewrite

open SourceFixedPointLimits Iota.AlphaPlus RelativeHighRewrite RelativeCollapseMonotonicity

/-- BOTH actual minima at a genuine low-tail cutoff. The stated cutoff
premises are mathematical hypotheses here; the subsequent native theorem
derives them from its actual finite selected original support. -/
theorem finite_relative_cutoff_tail_eq (τ : Ordinal.{0}) (hτ : 0 < τ)
    (α : Ordinal.{0}) (hle : τ ≤ α) (hαs : α < omegaSequence τ 1)
    (n : Nat) (hn : 1 < n) (Δ κ : Ordinal.{0})
    (hΔn : sourceNotation τ n 1 Δ) (hΔs : Δ < omegaSequence τ 2)
    (hΔ : omegaSequence τ 1 ∣ Δ) (hΔ0 : 0 < Δ)
    (hheadBound : sourceFiniteCollapse τ n 0 Δ ≤ α)
    (hκ : κ ≤ α)
    (hbefore : ∀ σ < κ, sourceFiniteCollapse τ n 0 (Δ + σ) ≤ α)
    (hafter : ∀ ρ < omegaSequence τ 1, α < sourceFiniteCollapse τ n 0 (Δ + (κ + ρ)))
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    sourceFiniteCollapse α n 0 (Δ + ρ) =
      sourceFiniteCollapse τ n 0 (Δ + (κ + ρ)) := by
  classical
  have hn0 : 0 < n := by omega
  have hαp : 0 < α := hτ.trans_le hle
  have hΔown := sourceFiniteCollapse_argument_notation τ n 0 hn0 Δ hΔs hΔn
  have hΔa := (next_notation_iff τ α hle hαs n hn Δ).mp hΔn
  have hΔsa : Δ < omegaSequence α 2 := by simpa only [← omega_succ τ α hle hαs 1] using hΔs
  have hΔda : omegaSequence α 1 ∣ Δ := by simpa only [← omega_succ τ α hle hαs 0] using hΔ
  have hΔhigh : omegaSequence α 1 ≤ Δ := Ordinal.le_of_dvd hΔ0.ne' hΔda
  revert hρ
  refine Ordinal.induction ρ ?_
  intro ρ ih hρ
  let δ := Δ + ρ
  let γ := Δ + (κ + ρ)
  have hd := (shiftArgument τ n 0 hn0 ⟨Δ, hΔn⟩ ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 ⟨Δ, hΔn⟩ hΔs ρ hρ
  have hda := (next_notation_iff τ α hle hαs n hn δ).mp hd
  have hdsa : δ < omegaSequence α 2 := by simpa only [← omega_succ τ α hle hαs 1] using hds
  have hρa : ρ < omegaSequence α 1 := by simpa only [← omega_succ τ α hle hαs 0] using hρ
  have htail : κ + ρ < omegaSequence τ 1 :=
    (omegaSequence_add_closed τ 0) (hκ.trans_lt hαs) hρ
  have hg := (shiftArgument τ n 0 hn0 ⟨Δ, hΔn⟩ (κ + ρ) htail).property
  have hgs := shiftArgument_sort τ n 0 hn0 ⟨Δ, hΔn⟩ hΔs (κ + ρ) htail
  apply le_antisymm
  · let β := sourceFiniteCollapse τ n 0 γ
    have hβs : β < omegaSequence τ 1 := sourceFiniteCollapse_proper_notation τ n 0 hn0 γ hgs hg
    have hβa : β < omegaSequence α 1 := by simpa only [← omega_succ τ α hle hαs 0] using hβs
    have hown := sourceFiniteCollapse_argument_notation τ n 0 hn0 γ hgs hg
    have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 γ β Δ (κ + ρ) hΔ htail).mp hown
    have htailβ : κ + ρ < β := tail_lt_collapse τ hτ n 0 hn0 ⟨Δ, hΔn⟩ hΔs hΔ (κ + ρ) htail
    have hαβ : α < β := hafter ρ hρ
    have hΔtarget := source_minimum_hull_to_target τ α hτ hle hαs n hn
      γ hg hgs δ Δ hsplit.1
    have htailtarget := source_minimum_hull_to_target τ α hτ hle hαs n hn
      γ hg hgs δ (κ + ρ) hsplit.2
    have hρtarget : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ρ := by
      rcases (le_add_self : ρ ≤ κ + ρ).eq_or_lt with hs | hs
      · simpa only [← hs] using htailtarget
      · exact source_hull_initial_segment α hαp n 0 hn0 δ β hdsa.le hβa
          htailtarget (by simpa only [← omega_succ τ α hle hαs 0] using htail) hs
    have harg : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β δ :=
      .add hΔtarget hρtarget
    have forward {ξ : Ordinal.{0}}
        (hx : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ξ) :
        Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β ξ := by
      induction hx with
      | below_base h => exact .below_parameter (h.trans hαβ)
      | below_parameter h => exact .below_parameter h
      | add _ _ ihξ ihζ => exact .add ihξ ihζ
      | @higher k ζ hk hkn hs hζ ihζ =>
        rw [← positive_collapse τ α hle hαs n k hk hkn ζ]
        exact .higher hk hkn (by simpa only [omega_succ τ α hle hαs (k + 1)] using hs) ihζ
      | @«local» ζ hζδ hζ ihζ =>
        by_cases hζΔ : ζ < Δ
        · have hζs : ζ < omegaSequence τ 2 := hζΔ.trans hΔs
          have hζn := source_hull_next_notation α n 0 hn0 hdsa.le hβa.le hζ
          have hb := relative_collapse_le_tailShift τ α hτ hle hαs n hn ζ hζn hζs
          have hmod := Ordinal.mod_lt ζ (next_cardinal_pos τ hτ 0).ne'
          have hparts := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 γ β
            (omegaSequence τ 1 * (ζ / omegaSequence τ 1)) (ζ % omegaSequence τ 1)
            ⟨ζ / omegaSequence τ 1, rfl⟩ hmod).mp
            (by simpa only [Ordinal.div_add_mod] using ihζ)
          have hf : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β
              (tailShift (omegaSequence τ 1) α ζ) :=
            .add hparts.1 (.add (.below_parameter hαβ) hparts.2)
          have hfΔ := tailShift_lt_multiple (omegaSequence τ 1) α ζ Δ
            (next_cardinal_pos τ hτ 0) (omegaSequence_add_closed τ 0) hαs hΔ hζΔ
          have hfγ : tailShift (omegaSequence τ 1) α ζ < γ := hfΔ.trans_le le_self_add
          have hfn := source_hull_next_notation τ n 0 hn0 hgs.le hβs.le hf
          have hfp := sourceFiniteCollapse_proper_notation τ n 0 hn0 _ (hfγ.trans hgs) hfn
          exact .below_parameter (hb.trans_lt
            ((finiteCollapse_hull_initial hn0 γ _).mp ⟨.local hfγ hf, hfp⟩))
        · have hΔζ : Δ ≤ ζ := le_of_not_gt hζΔ
          let σ := ζ - Δ
          have heζ : Δ + σ = ζ := Ordinal.add_sub_cancel_of_le hΔζ
          have hσρ : σ < ρ := by
            apply (add_lt_add_iff_left Δ).mp
            rw [heζ]
            exact hζδ
          have hparts := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 γ β Δ σ hΔ
            (hσρ.trans hρ)).mp (by simpa only [heζ] using ihζ)
          have hshift : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β
              (Δ + (κ + σ)) := .add hparts.1 (.add (.below_parameter (hκ.trans_lt hαβ)) hparts.2)
          have hsmall : Δ + (κ + σ) < γ :=
            (Ordinal.isNormal_add_right Δ).strictMono ((Ordinal.isNormal_add_right κ).strictMono hσρ)
          have hnshift := source_hull_next_notation τ n 0 hn0 hgs.le hβs.le hshift
          have hpshift := sourceFiniteCollapse_proper_notation τ n 0 hn0 _ (hsmall.trans hgs) hnshift
          have hecall : sourceFiniteCollapse α n 0 ζ = sourceFiniteCollapse τ n 0 (Δ + (κ + σ)) := by
            rw [← heζ]
            exact ih σ hσρ (hσρ.trans hρ)
          rw [hecall]
          exact .local hsmall hshift
    apply finiteCollapse_minimal hn0
    refine ⟨hβa, ?_, harg⟩
    intro ξ hx hs
    exact (finiteCollapse_hull_initial hn0 γ ξ).mp
      ⟨forward hx, by simpa only [← omega_succ τ α hle hαs 0] using hs⟩
  · let β := sourceFiniteCollapse α n 0 δ
    have hβa : β < omegaSequence α 1 := sourceFiniteCollapse_proper_notation α n 0 hn0 δ hdsa hda
    have hβs : β < omegaSequence τ 1 := by simpa only [omega_succ τ α hle hαs 0] using hβa
    have hαβ : α < β := by
      simpa only [omegaSequence_zero] using sourceFiniteCollapse_high_base_lt α hαp n 0 hn0 δ
        (hΔhigh.trans le_self_add)
    have hρβ : ρ < β := tail_lt_collapse α hαp n 0 hn0 ⟨Δ, hΔa⟩ hΔsa hΔda ρ hρa
    have hhead : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β Δ :=
      hull_mono (le_self_add : Δ ≤ γ) (hheadBound.trans hαβ.le) hΔown
    have harg : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 γ β γ :=
      .add hhead (.add (.below_parameter (hκ.trans_lt hαβ)) (.below_parameter hρβ))
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
        by_cases hζΔ : ζ < Δ
        · have hζs : ζ < omegaSequence τ 2 := hζΔ.trans hΔs
          have hζn := source_hull_next_notation α n 0 hn0 hdsa.le hβa.le ihζ
          have hζδ : ζ < δ := hζΔ.trans_le le_self_add
          have hζp := sourceFiniteCollapse_proper_notation α n 0 hn0 ζ (hζδ.trans hdsa) hζn
          have hc : sourceFiniteCollapse α n 0 ζ < β :=
            (finiteCollapse_hull_initial hn0 δ _).mp ⟨.local hζδ ihζ, hζp⟩
          exact .below_parameter ((finite_collapse_mono_base τ α hτ hle hαs n hn ζ hζn hζs).trans_lt hc)
        · have hΔζ : Δ ≤ ζ := le_of_not_gt hζΔ
          let σ := ζ - Δ
          have heζ : Δ + σ = ζ := Ordinal.add_sub_cancel_of_le hΔζ
          have hσtail : σ < κ + ρ := by
            apply (add_lt_add_iff_left Δ).mp
            rw [heζ]
            exact hζγ
          have hσs : σ < omegaSequence τ 1 := hσtail.trans htail
          by_cases hσκ : σ < κ
          · have hc := hbefore σ hσκ
            rw [heζ] at hc
            exact .below_parameter (hc.trans_lt hαβ)
          · have hκσ : κ ≤ σ := le_of_not_gt hσκ
            let ε := σ - κ
            have hσε : κ + ε = σ := Ordinal.add_sub_cancel_of_le hκσ
            have hερ : ε < ρ := by
              apply (add_lt_add_iff_left κ).mp
              rw [hσε]
              exact hσtail
            have hεσ : ε ≤ σ := Ordinal.sub_le_self σ κ
            have hσa : σ < omegaSequence α 1 := by simpa only [← omega_succ τ α hle hαs 0] using hσs
            have hparts := (source_hull_multiple_add_low_iff α hαp n 0 hn0 δ β Δ σ hΔda hσa).mp
              (by simpa only [heζ] using ihζ)
            have hεHull : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ε := by
              rcases hεσ.eq_or_lt with hs | hs
              · simpa only [← hs] using hparts.2
              · exact source_hull_initial_segment α hαp n 0 hn0 δ β hdsa.le hβa hparts.2 hσa hs
            have hsmall : Δ + ε < δ := (Ordinal.isNormal_add_right Δ).strictMono hερ
            have hecall : sourceFiniteCollapse τ n 0 ζ = sourceFiniteCollapse α n 0 (Δ + ε) := by
              rw [← heζ, ← hσε]
              exact (ih ε hερ (hερ.trans hρ)).symm
            rw [hecall]
            exact .local hsmall (.add hparts.1 hεHull)
    apply finiteCollapse_minimal hn0
    refine ⟨hβs, ?_, harg⟩
    intro ξ hx hs
    exact (finiteCollapse_hull_initial hn0 δ ξ).mp
      ⟨forward hx, by simpa only [← omega_succ τ α hle hαs 0] using hs⟩

/-- Real same-head strictness for arbitrary LOW ordinal tails. -/
theorem global_same_head_strict (τ : Ordinal.{0}) (hτ : 0 < τ)
    (Γ : GlobalNotationOrdinal τ 1) (hΓs : Γ.val < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ.val) (η ρ : Ordinal.{0})
    (hηρ : η < ρ) (hρ : ρ < omegaSequence τ 1) :
    globalCollapse τ 0 (Γ.val + η) < globalCollapse τ 0 (Γ.val + ρ) := by
  obtain ⟨n, hn, hΓn⟩ := globalNotation_finite_witness τ hτ 1 Γ.property
  have hn0 : 0 < n := by omega
  let gn : SourceNotationOrdinal τ n 1 := ⟨Γ.val, hΓn⟩
  let a := SourceHighPartComparison.residualArgument τ n 0 hn0 gn η (hηρ.trans hρ)
  let b := SourceHighPartComparison.residualArgument τ n 0 hn0 gn ρ hρ
  have has := shiftArgument_sort τ n 0 hn0 gn hΓs η (hηρ.trans hρ)
  have hbs := shiftArgument_sort τ n 0 hn0 gn hΓs ρ hρ
  have hab := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn a.property has
  have hbb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn b.property hbs
  rw [globalCollapse_finite_agreement τ hτ n 0 hn0 _ hab,
    globalCollapse_finite_agreement τ hτ n 0 hn0 _ hbb]
  exact SourceHighPartComparison.same_high_part_strict τ hτ n 0 hn0 gn hΓs hΓd η ρ hηρ hρ

/-- Global agreement uses the genuine finite source fragment of the head.
The all-tail cut premises remain explicit in this mathematical helper. -/
theorem global_relative_cutoff_tail_eq (τ : Ordinal.{0}) (hτ : 0 < τ)
    (α : Ordinal.{0}) (hle : τ ≤ α) (hαs : α < omegaSequence τ 1)
    (Γ : Ordinal.{0}) (hΓ : GlobalNotation τ 1 Γ) (hΓs : Γ < omegaSequence τ 2)
    (hΓd : omegaSequence τ 1 ∣ Γ) (hΓ0 : 0 < Γ)
    (hheadBound : globalCollapse τ 0 Γ ≤ α)
    (κ : Ordinal.{0}) (hκ : κ ≤ α)
    (hbefore : ∀ σ < κ, globalCollapse τ 0 (Γ + σ) ≤ α)
    (hafter : ∀ ρ < omegaSequence τ 1, α < globalCollapse τ 0 (Γ + (κ + ρ)))
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence τ 1) :
    globalCollapse α 0 (Γ + ρ) = globalCollapse τ 0 (Γ + (κ + ρ)) := by
  obtain ⟨n, hn, hΓn⟩ := globalNotation_finite_witness τ hτ 1 hΓ
  have hn0 : 0 < n := by omega
  have hαp : 0 < α := hτ.trans_le hle
  let gn : SourceNotationOrdinal τ n 1 := ⟨Γ, hΓn⟩
  have agree (σ : Ordinal.{0}) (hσ : σ < omegaSequence τ 1) :
      globalCollapse τ 0 (Γ + σ) = sourceFiniteCollapse τ n 0 (Γ + σ) := by
    have harg := shiftArgument τ n 0 hn0 gn σ hσ
    have hs := shiftArgument_sort τ n 0 hn0 gn hΓs σ hσ
    exact globalCollapse_finite_agreement τ hτ n 0 hn0 _
      (source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn harg.property hs)
  have hheadBound' : sourceFiniteCollapse τ n 0 Γ ≤ α := by
    simpa only [add_zero] using (agree 0 (next_cardinal_pos τ hτ 0)).symm.trans_le hheadBound
  have hbefore' : ∀ σ < κ, sourceFiniteCollapse τ n 0 (Γ + σ) ≤ α := by
    intro σ hσ
    rw [← agree σ ((hσ.trans_le hκ).trans hαs)]
    exact hbefore σ hσ
  have hafter' : ∀ σ < omegaSequence τ 1,
      α < sourceFiniteCollapse τ n 0 (Γ + (κ + σ)) := by
    intro σ hσ
    rw [← agree (κ + σ) ((omegaSequence_add_closed τ 0) (hκ.trans_lt hαs) hσ)]
    exact hafter σ hσ
  have hd := (shiftArgument τ n 0 hn0 gn ρ hρ).property
  have hds := shiftArgument_sort τ n 0 hn0 gn hΓs ρ hρ
  have hda := (next_notation_iff τ α hle hαs n hn (Γ + ρ)).mp hd
  have hdsa : Γ + ρ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hαs 1] using hds
  have hdb := source_finite_notation_sorted_lt_boundary α hαp n 1 1 le_rfl hn hda hdsa
  rw [globalCollapse_finite_agreement α hαp n 0 hn0 (Γ + ρ) hdb,
    agree (κ + ρ) ((omegaSequence_add_closed τ 0) (hκ.trans_lt hαs) hρ)]
  exact finite_relative_cutoff_tail_eq τ hτ α hle hαs n hn Γ κ hΓn hΓs hΓd hΓ0
    hheadBound' hκ hbefore' hafter' ρ hρ

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeCutoffRewrite
