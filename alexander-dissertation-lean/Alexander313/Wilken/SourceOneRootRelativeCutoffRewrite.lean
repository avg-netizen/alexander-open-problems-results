import Alexander313.Wilken.SourceOneRootRelativeSupportCutoff
import Alexander313.Wilken.HereditaryNativeRelativeCutoffRewrite

/-!
# Original source-one selected-support scalar rewrite

The original written support maximum supplies a genuine cutoff for every
ordinal LOW tail. Both actual finite minima derive the relative equation
at source one. All source syntax uses the original hereditary level zero;
the shared ordinal minimum lemma is instantiated at the actual ordinal one.
No native base-one parser, scalar equation or endpoint oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RelativeCutoffRewrite

open ThetaCourse SourceFixedPointLimits RootSupportThreshold
open NativeContext.Iota.AlphaPlus NativeContext.RelativeEndpointRewrite
open NativeContext.RelativeCutoffRewrite

noncomputable def selectedTail (c d : Nat) : Ordinal.{0} :=
  if interpretation 0 c < nodeHead d then interpretation 0 d else
    SourceHighPartComparison.tailPart (omegaSequence 1 1)
      (interpretation 0 (Localization.argumentCode d)) + 1

/-- The actual selected support derives the whole relative collapse
identity on EVERY LOW ordinal tail. The requested code is an admitted
positive divisible head (the scalar consumer constructs this head code).
There is no bound on the whole requested head-plus-tail collapse. -/
theorem selected_relative_tail_eq (b c d : Nat)
    (hi : RootSupportThreshold.inputCheck b c = true)
    (hs : selected b c = some d)
    (hΓd : omegaSequence 1 1 ∣ interpretation 0 c)
    (hΓ0 : 0 < interpretation 0 c)
    (ρ : Ordinal.{0}) (hρ : ρ < omegaSequence 1 1) :
    globalCollapse (interpretation 0 b) 0 (interpretation 0 c + ρ) =
      globalCollapse 1 0 (interpretation 0 c + (selectedTail c d + ρ)) := by
  classical
  have hg := (RootSupportThreshold.inputCheck_exact b c).mp hi
  have hd := selected_spec b c d hi hs
  have hc := (sortedCheck_exact c).mp hg.2.1
  have hΓcheck := ((SourceDecomposition.inputCheck_exact 0 c).mp hc.1).1
  have hτ : (0 : Ordinal.{0}) < 1 := zero_lt_one
  let Ω := omegaSequence 1 1
  let Γ := interpretation 0 c
  let β := interpretation 0 b
  let S := interpretation 0 d
  have hΩ : 0 < Ω := next_cardinal_pos 1 hτ 0
  have hβ : (1 : Ordinal.{0}) ≤ β ∧ β < Ω :=
    ⟨RootScalar.root_base_le b hg.1, root_lt_first b hg.1⟩
  have hΓ : GlobalNotation 1 1 Γ :=
    by simpa only [finiteBase_zero, RootScalar.raw_value c hc.1] using
      SourceFixedPoint.checked_notation_at 0 _ (RootScalar.raw_checked c hc.1) 1
  have hΓs : Γ < omegaSequence 1 2 := by
    rw [← RootScalar.raw_value c hc.1, ← finiteBase_zero]
    exact (denote_lt_iff_outerSort_le 0 _ (RootScalar.raw_checked c hc.1) 2 (by omega)).mpr hc.2
  obtain ⟨a, he, ha, hna⟩ := hd.2.1
  let A := denote 0 a
  let Λ := head a
  let η := SourceHighPartComparison.tailPart Ω A
  have hAs : A < omegaSequence 1 2 := SourceFixedPoint.checked_theta_sort 0 0 a ha
  have hA : GlobalNotation 1 1 A :=
    SourceFixedPoint.checked_notation_at 0 a (SourceFixedPoint.checked_theta_argument 0 0 a ha) 1
  have hΛd : Ω ∣ Λ := SourceHighPartComparison.highPart_dvd Ω A
  have hη : η < Ω := SourceHighPartComparison.tailPart_lt Ω A hΩ
  have hparts : Λ + η = A := SourceHighPartComparison.highPart_add_tailPart Ω A
  have hΛs : Λ < omegaSequence 1 2 :=
    (SourceHighPartComparison.highPart_le Ω A).trans_lt hAs
  have hΛ : GlobalNotation 1 1 Λ := by
    obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness 1 hτ 1 hA
    exact sourceNotation_to_globalNotation 1 hτ n 1 hn
      (root_head_notation 1 hτ n hn A Λ η hAn hAs hΛd hη hparts.symm)
  have hS : S = globalCollapse 1 0 (Λ + η) := by
    rw [he, interpretation_code]
    change globalCollapse 1 0 A = globalCollapse 1 0 (Λ + η)
    rw [hparts]
  have hnode : nodeHead d = Λ := by rw [he, nodeHead_theta]
  have hΓhead : SourceHighPartComparison.highPart Ω Γ = Γ :=
    Ordinal.div_mul_cancel hΩ.ne' hΓd
  have hΓΛ : Γ ≤ Λ := by
    have hh := hd.2.2.1
    rw [hnode, hΓhead] at hh
    exact hh
  have hΛ0 : 0 < Λ := hΓ0.trans_le hΓΛ
  have hθΓS : globalCollapse 1 0 Γ ≤ S := by
    have ht := RootScalar.nodeCode_sorted_spec 0 c hc.1 (by simpa only [Nat.zero_add] using hc.2)
    exact ht.2.symm.trans_le hd.2.2.2.1
  have hSβ : S ≤ β := selected_value_le_root b c d hi hs
  have hη1 : η + 1 < S := by
    obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness 1 hτ 1 hA
    have hn0 : 0 < n := by omega
    have hb := source_finite_notation_sorted_lt_boundary 1 hτ n 1 1 le_rfl hn hAn hAs
    rw [hS, hparts, globalCollapse_finite_agreement 1 hτ n 0 hn0 A hb]
    exact root_tail_successor_lt 1 hτ n hn A Λ η hAn hAs hΛd hΛ0 hη hparts.symm
  let κ := selectedTail c d
  have hargValue : interpretation 0 (Localization.argumentCode d) = A := by
    rw [he, Localization.argumentCode_theta, interpretation_code]
  have hκvalue : κ = if Γ < Λ then S else η + 1 := by
    change selectedTail c d = if interpretation 0 c < Λ then interpretation 0 d else η + 1
    simp only [selectedTail, hnode, hargValue]
  have hκ : κ ≤ β := by
    rw [hκvalue]
    split_ifs with hh
    · exact hSβ
    · exact hη1.le.trans hSβ
  have cut (σ : Ordinal.{0}) (hσ : σ < Ω) :
      globalCollapse 1 0 (Γ + σ) ≤ β ↔
        globalCollapse 1 0 (Γ + σ) ≤ S := by
    apply RelativeSupportCutoff.selected_value_cutoff b c d hi hs
      ⟨Γ + σ, .add hΓ (.parameter hσ)⟩
      ((omegaSequence_add_closed 1 1) hΓs (hσ.trans (omegaSequence_step 1 1)))
    rw [highPart_add_low_of_dvd Ω Γ σ hΩ hΓd hσ]
    exact hΓhead.le
  have hbefore : ∀ σ < κ, globalCollapse 1 0 (Γ + σ) ≤ β := by
    intro σ hσ
    have hσΩ : σ < Ω := (hσ.trans_le hκ).trans hβ.2
    by_cases hh : Γ < Λ
    · have hσS : σ < S := by simpa only [hκvalue, if_pos hh] using hσ
      exact (global_smaller_head_tail_lt 1 hτ Γ Λ η hΓ hΓs hΓd hΛ hΛs hΛd hη hh
        (hθΓS.trans_eq hS) σ (hσS.trans_eq hS)).le.trans (hS.symm.trans_le hSβ)
    · have heΓ : Γ = Λ := le_antisymm hΓΛ (le_of_not_gt hh)
      have hση : σ ≤ η := Order.lt_add_one_iff.mp (by
        simpa only [hκvalue, if_neg hh] using hσ)
      have hsmall : globalCollapse 1 0 (Γ + σ) ≤ S := by
        rw [heΓ, hS]
        rcases hση.eq_or_lt with heσ | hσlt
        · rw [heσ]
        · exact (global_same_head_strict 1 hτ ⟨Λ, hΛ⟩ hΛs hΛd σ η hσlt hη).le
      exact hsmall.trans hSβ
  have hafter : ∀ σ < Ω, β < globalCollapse 1 0 (Γ + (κ + σ)) := by
    intro σ hσ
    have htail : κ + σ < Ω := (omegaSequence_add_closed 1 0) (hκ.trans_lt hβ.2) hσ
    have hSlt : S < globalCollapse 1 0 (Γ + (κ + σ)) := by
      by_cases hh : Γ < Λ
      · have hκS : κ = S := by rw [hκvalue, if_pos hh]
        exact (show S ≤ κ + σ from by rw [hκS]; exact le_self_add).trans_lt
          (NativeContext.RelativeZeta.Support.global_tail_lt_collapse 1 hτ Γ hΓ hΓs hΓd (κ + σ) htail)
      · have heΓ : Γ = Λ := le_antisymm hΓΛ (le_of_not_gt hh)
        have hηtail : η < κ + σ := by
          rw [hκvalue, if_neg hh]
          exact (Order.lt_add_one_iff.mpr le_rfl).trans_le le_self_add
        rw [hS, ← heΓ]
        exact global_same_head_strict 1 hτ ⟨Γ, hΓ⟩ hΓs hΓd η (κ + σ) hηtail htail
    apply lt_of_not_ge
    intro hc
    exact hSlt.not_ge ((cut (κ + σ) htail).mp hc)
  exact global_relative_cutoff_tail_eq 1 hτ β hβ.1 hβ.2 Γ hΓ hΓs hΓd hΓ0
    (hθΓS.trans hSβ) κ hκ hbefore hafter ρ hρ


end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.RelativeCutoffRewrite
