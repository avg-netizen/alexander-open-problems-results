import Alexander313.Wilken.HereditaryNativeRelativeCutoffRewriteSupport
import Alexander313.Wilken.HereditaryNativeRelativeSupportCutoff
import Alexander313.Wilken.HereditaryNativeRelativeZetaSupport

/-!
# Genuine selected-support relative collapse rewriting

The actual selected written support S supplies the entire arbitrary-tail
cutoff. If the requested head precedes S's head the first crossing tail is
S; if their heads agree it is the successor of S's original LOW tail.
Actual global comparison and strict same-head comparison derive all prior
bounds and all later crossings. BOTH actual minima then give the relative
collapse equation. No cutoff, hull, representation or equation oracle.
Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeCutoffRewrite

open ThetaCourse SourceFixedPointLimits Iota.AlphaPlus RelativeEndpointRewrite
open RootSupportThreshold

/-- Genuine division preserves a divisible head under EVERY LOW tail. -/
theorem highPart_add_low_of_dvd (Ω Γ σ : Ordinal.{0}) (hΩ : 0 < Ω)
    (hΓ : Ω ∣ Γ) (hσ : σ < Ω) :
    SourceHighPartComparison.highPart Ω (Γ + σ) = Γ := by
  obtain ⟨v, rfl⟩ := hΓ
  unfold SourceHighPartComparison.highPart
  rw [Ordinal.mul_add_div _ hΩ.ne', Ordinal.div_eq_zero_of_lt hσ, add_zero]

/-- A smaller source head with a low tail below S remains strictly below
S, using the real global star comparison including all hidden support. -/
theorem global_smaller_head_tail_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (Γ Λ η : Ordinal.{0}) (hΓ : GlobalNotation τ 1 Γ)
    (hΓs : Γ < omegaSequence τ 2) (hΓd : omegaSequence τ 1 ∣ Γ)
    (hΛ : GlobalNotation τ 1 Λ)
    (hΛs : Λ < omegaSequence τ 2) (hΛd : omegaSequence τ 1 ∣ Λ)
    (hη : η < omegaSequence τ 1) (hΓΛ : Γ < Λ)
    (hhead : globalCollapse τ 0 Γ ≤ globalCollapse τ 0 (Λ + η))
    (σ : Ordinal.{0}) (hσ : σ < globalCollapse τ 0 (Λ + η)) :
    globalCollapse τ 0 (Γ + σ) < globalCollapse τ 0 (Λ + η) := by
  let g : GlobalNotationOrdinal τ 1 := ⟨Γ, hΓ⟩
  let l : GlobalNotationOrdinal τ 1 := ⟨Λ + η, .add hΛ (.parameter hη)⟩
  have hls : l.val < omegaSequence τ 2 :=
    (omegaSequence_add_closed τ 1) hΛs (hη.trans (omegaSequence_step τ 1))
  have hS := (RelativeZeta.Support.global_collapse_bounds τ hτ _ l.property hls).2
  have hσΩ : σ < omegaSequence τ 1 := hσ.trans hS
  let s : GlobalNotationOrdinal τ 1 := ⟨σ, .parameter hσΩ⟩
  have hgs : (globalAddArgument τ 0 g s).val < omegaSequence τ 2 :=
    (omegaSequence_add_closed τ 1) hΓs (hσΩ.trans (omegaSequence_step τ 1))
  apply (globalCollapse_lt_iff_globalStar τ hτ 0 (globalAddArgument τ 0 g s) l hgs hls).mpr
  apply Or.inl
  refine ⟨?_, ?_⟩
  · exact (multiple_add_low_lt_of_lt (omegaSequence τ 1) Γ Λ σ
      (next_cardinal_pos τ hτ 0) hΓd hΛd hΓΛ hσΩ).trans_le le_self_add
  · apply (global_star_add_le τ hτ 0 g s).trans_lt
    exact max_lt ((globalStar_lt_globalCollapse τ hτ 0 g hΓs).trans_le hhead)
      ((global_star_le_argument_of_low τ hτ 0 s hσΩ).trans_lt hσ)

/-- The actual ordinal crossing tail selected by the original finite
support. This definition has no supplied cutoff parameter. -/
noncomputable def selectedTail (q c d : Nat) : Ordinal.{0} :=
  if interpretation q c < nodeHead q d then interpretation q d else
    SourceHighPartComparison.tailPart (omegaSequence (base q) 1)
      (interpretation q (Localization.argumentCode d)) + 1

/-- The actual selected support derives the whole relative collapse
identity on EVERY LOW ordinal tail. The requested code is an admitted
positive divisible head (the scalar consumer constructs this head code).
There is no bound on the whole requested head-plus-tail collapse. -/
theorem selected_relative_tail_eq (q b c d : Nat)
    (hi : RootSupportThreshold.inputCheck q b c = true)
    (hs : selected q b c = some d)
    (hΓd : omegaSequence (base q) 1 ∣ interpretation q c)
    (hΓ0 : 0 < interpretation q c)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence (base q) 1) :
    globalCollapse (interpretation q b) 0 (interpretation q c + ρ) =
      globalCollapse (base q) 0 (interpretation q c + (selectedTail q c d + ρ)) := by
  classical
  have hg := (RootSupportThreshold.inputCheck_exact q b c).mp hi
  have hd := selected_spec q b c d hi hs
  have hinterval := selected_interval q b c d hi hs
  have hΓcheck := ((Comparison.acceptedCode_exact q c).mp
    ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hg.2.1).1).1
  have hq := (HeightBoundary.input_spec q d hinterval.2.1).2.1
  have hτ := base_pos q hq
  let Ω := omegaSequence (base q) 1
  let Γ := interpretation q c
  let β := interpretation q b
  let S := interpretation q d
  have hΩ : 0 < Ω := next_cardinal_pos (base q) hτ 0
  have hβ : base q ≤ β ∧ β < Ω :=
    ⟨RootLowCollapse.root_base_le q b hg.1, RootLowCollapse.root_lt_first q b hg.1⟩
  have hΓ : GlobalNotation (base q) 1 Γ :=
    by simpa only [Arithmetic.raw_value q c hΓcheck] using
      FixedPoint.checked_notation_at q _ (Arithmetic.raw_checked q c hΓcheck) 1
  have hΓs : Γ < omegaSequence (base q) 2 := RootAboveHeadCollapse.argument_sorted q c hg.2.1
  obtain ⟨a, he, ha, hna⟩ := hd.2.1
  let A := denote q a
  let Λ := head q a
  let η := SourceHighPartComparison.tailPart Ω A
  have hAs : A < omegaSequence (base q) 2 := FixedPoint.checked_theta_sort q 0 a ha
  have hA : GlobalNotation (base q) 1 A :=
    FixedPoint.checked_notation_at q a (FixedPoint.checked_theta_argument q 0 a ha) 1
  have hΛd : Ω ∣ Λ := SourceHighPartComparison.highPart_dvd Ω A
  have hη : η < Ω := SourceHighPartComparison.tailPart_lt Ω A hΩ
  have hparts : Λ + η = A := SourceHighPartComparison.highPart_add_tailPart Ω A
  have hΛs : Λ < omegaSequence (base q) 2 :=
    (SourceHighPartComparison.highPart_le Ω A).trans_lt hAs
  have hΛ : GlobalNotation (base q) 1 Λ := by
    obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness (base q) hτ 1 hA
    exact sourceNotation_to_globalNotation (base q) hτ n 1 hn
      (root_head_notation (base q) hτ n hn A Λ η hAn hAs hΛd hη hparts.symm)
  have hS : S = globalCollapse (base q) 0 (Λ + η) := by
    rw [he, interpretation_code]
    change globalCollapse (base q) 0 A = globalCollapse (base q) 0 (Λ + η)
    rw [hparts]
  have hnode : nodeHead q d = Λ := by rw [he, nodeHead_theta]
  have hΓhead : SourceHighPartComparison.highPart Ω Γ = Γ :=
    Ordinal.div_mul_cancel hΩ.ne' hΓd
  have hΓΛ : Γ ≤ Λ := by
    have hh := hd.2.2.1
    rw [hnode, hΓhead] at hh
    exact hh
  have hΛ0 : 0 < Λ := hΓ0.trans_le hΓΛ
  have hθΓS : globalCollapse (base q) 0 Γ ≤ S := by
    have ht := RootEndpointCollapse.thetaCode_sorted_spec q c
      ((RootAboveHeadCollapse.argumentCheck_exact q c).mp hg.2.1).1 hΓs
    exact (ht.2.2).symm.trans_le hd.2.2.2.1
  have hSβ : S ≤ β := hinterval.2.2.2.2.2.1
  have hη1 : η + 1 < S := by
    obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness (base q) hτ 1 hA
    have hn0 : 0 < n := by omega
    have hb := source_finite_notation_sorted_lt_boundary (base q) hτ n 1 1 le_rfl hn hAn hAs
    rw [hS, hparts, globalCollapse_finite_agreement (base q) hτ n 0 hn0 A hb]
    exact root_tail_successor_lt (base q) hτ n hn A Λ η hAn hAs hΛd hΛ0 hη hparts.symm
  let κ := selectedTail q c d
  have hargValue : interpretation q (Localization.argumentCode d) = A := by
    rw [he, Localization.argumentCode_theta, interpretation_code]
  have hκvalue : κ = if Γ < Λ then S else η + 1 := by
    change selectedTail q c d = if interpretation q c < Λ then interpretation q d else η + 1
    simp only [selectedTail, hnode, hargValue]
  have hκ : κ ≤ β := by
    rw [hκvalue]
    split_ifs with hh
    · exact hSβ
    · exact hη1.le.trans hSβ
  have cut (σ : Ordinal.{0}) (hσ : σ < Ω) :
      globalCollapse (base q) 0 (Γ + σ) ≤ β ↔
        globalCollapse (base q) 0 (Γ + σ) ≤ S := by
    apply RelativeSupportCutoff.selected_value_cutoff q b c d hi hs
      ⟨Γ + σ, .add hΓ (.parameter hσ)⟩
      ((omegaSequence_add_closed (base q) 1) hΓs (hσ.trans (omegaSequence_step (base q) 1)))
    rw [highPart_add_low_of_dvd Ω Γ σ hΩ hΓd hσ]
    exact hΓhead.le
  have hbefore : ∀ σ < κ, globalCollapse (base q) 0 (Γ + σ) ≤ β := by
    intro σ hσ
    have hσΩ : σ < Ω := (hσ.trans_le hκ).trans hβ.2
    by_cases hh : Γ < Λ
    · have hσS : σ < S := by simpa only [hκvalue, if_pos hh] using hσ
      exact (global_smaller_head_tail_lt (base q) hτ Γ Λ η hΓ hΓs hΓd hΛ hΛs hΛd hη hh
        (hθΓS.trans_eq hS) σ (hσS.trans_eq hS)).le.trans (hS.symm.trans_le hSβ)
    · have heΓ : Γ = Λ := le_antisymm hΓΛ (le_of_not_gt hh)
      have hση : σ ≤ η := Order.lt_add_one_iff.mp (by
        simpa only [hκvalue, if_neg hh] using hσ)
      have hsmall : globalCollapse (base q) 0 (Γ + σ) ≤ S := by
        rw [heΓ, hS]
        rcases hση.eq_or_lt with heσ | hσlt
        · rw [heσ]
        · exact (global_same_head_strict (base q) hτ ⟨Λ, hΛ⟩ hΛs hΛd σ η hσlt hη).le
      exact hsmall.trans hSβ
  have hafter : ∀ σ < Ω, β < globalCollapse (base q) 0 (Γ + (κ + σ)) := by
    intro σ hσ
    have htail : κ + σ < Ω := (omegaSequence_add_closed (base q) 0) (hκ.trans_lt hβ.2) hσ
    have hSlt : S < globalCollapse (base q) 0 (Γ + (κ + σ)) := by
      by_cases hh : Γ < Λ
      · have hκS : κ = S := by rw [hκvalue, if_pos hh]
        exact (show S ≤ κ + σ from by rw [hκS]; exact le_self_add).trans_lt
          (RelativeZeta.Support.global_tail_lt_collapse (base q) hτ Γ hΓ hΓs hΓd (κ + σ) htail)
      · have heΓ : Γ = Λ := le_antisymm hΓΛ (le_of_not_gt hh)
        have hηtail : η < κ + σ := by
          rw [hκvalue, if_neg hh]
          exact (Order.lt_add_one_iff.mpr le_rfl).trans_le le_self_add
        rw [hS, ← heΓ]
        exact global_same_head_strict (base q) hτ ⟨Γ, hΓ⟩ hΓs hΓd η (κ + σ) hηtail htail
    apply lt_of_not_ge
    intro hc
    exact hSlt.not_ge ((cut (κ + σ) htail).mp hc)
  exact global_relative_cutoff_tail_eq (base q) hτ β hβ.1 hβ.2 Γ hΓ hΓs hΓd hΓ0
    (hθΓS.trans hSβ) κ hκ hbefore hafter ρ hρ

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeCutoffRewrite
