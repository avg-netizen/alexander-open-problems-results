import Alexander313.Wilken.HereditaryNativeRelativeCollapseMonotonicity
import Alexander313.Wilken.HereditaryNativeIotaAlphaPlus

/-!
# The original source alpha-plus is the actual relative high-part collapse

The previously proved upper estimate is made an equality. The reverse
candidate transfers the original successor hull into the target high-part
minimum. Local arguments below Delta use actual base monotonicity. Every
remaining local argument is Delta+rho with rho<=eta<alpha, and is therefore
in the ORIGINAL own hull at A and alpha. Its actual source call is below
alpha, or is alpha itself when the argument is A. No arbitrary downward
closure above Omega1, shifted-collapse identity or translation is assumed.

This proves the endpoint identity restated at w2.txt 985-1000. It does not
construct the general bounded same-value term translator from [55] 6.2/6.3.
Source candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.AlphaPlus

open SourceFixedPointLimits RelativeCollapseMonotonicity

/-- Both actual finite minima coincide at the ORIGINAL high-part endpoint.
The nonzero divided high part is an explicit original high-root condition. -/
theorem relative_highPart_eq_source_successor (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 1 < n) (A Δ η : Ordinal.{0})
    (hA : sourceNotation τ n 1 A) (hAs : A < omegaSequence τ 2)
    (hΔ : omegaSequence τ 1 ∣ Δ) (hΔ0 : 0 < Δ)
    (hη : η < omegaSequence τ 1) (he : A = Δ + η) :
    sourceFiniteCollapse (sourceFiniteCollapse τ n 0 A) n 0 Δ =
      sourceFiniteCollapse τ n 0 (A + 1) := by
  let α := sourceFiniteCollapse τ n 0 A
  let β := sourceFiniteCollapse α n 0 Δ
  have hn0 : 0 < n := by omega
  have hle : τ ≤ α := by simpa only [omegaSequence_zero] using
    (sourceFiniteCollapse_bounds τ n 0 hn0 A).1
  have hαs : α < omegaSequence τ 1 :=
    sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hA
  have hαp : 0 < α := hτ.trans_le hle
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A α A :=
    sourceFiniteCollapse_argument_notation τ n 0 hn0 A hAs hA
  have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 A α
    Δ η hΔ hη).mp (by simpa only [he] using hown)
  have hΔn := source_hull_next_notation τ n 0 hn0 hAs.le hαs.le hsplit.1
  have hΔa := (next_notation_iff τ α hle hαs n hn Δ).mp hΔn
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΔs : Δ < omegaSequence τ 2 := hΔA.trans_lt hAs
  have hΔsa : Δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hαs 1] using hΔs
  have hβa : β < omegaSequence α 1 :=
    sourceFiniteCollapse_proper_notation α n 0 hn0 Δ hΔsa hΔa
  have hβs : β < omegaSequence τ 1 := by
    simpa only [omega_succ τ α hle hαs 0] using hβa
  have hhigh : omegaSequence α 1 ≤ Δ := by
    simpa only [← omega_succ τ α hle hαs 0] using Ordinal.le_of_dvd hΔ0.ne' hΔ
  have hαβ : α < β := by
    simpa only [omegaSequence_zero] using
      sourceFiniteCollapse_high_base_lt α hαp n 0 hn0 Δ hhigh
  have hηα : η < α := by
    simpa only [← he] using tail_lt_collapse τ hτ n 0 hn0
      ⟨Δ, hΔn⟩ hΔs hΔ η hη
  have hSs : A + 1 < omegaSequence τ 2 :=
    (omegaSequence_isSuccLimit τ 1).add_one_lt hAs
  have honeβ : (1 : Ordinal.{0}) < β :=
    (one_le_iff_pos.mpr hαp).trans_lt hαβ
  have harg : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (A + 1) β (A + 1) :=
    .add (hull_mono (lt_add_one A).le hαβ.le hown) (.below_parameter honeβ)
  have forward {ξ : Ordinal.{0}}
      (hx : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (A + 1) β ξ) :
      Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 Δ β ξ := by
    induction hx with
    | below_base h => exact .below_base (h.trans_le hle)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihζ => exact .add ihξ ihζ
    | @higher k ζ hk hkn hs hζ ihζ =>
      rw [positive_collapse τ α hle hαs n k hk hkn ζ]
      exact .higher hk hkn (by simpa only [← omega_succ τ α hle hαs (k + 1)] using hs) ihζ
    | @«local» ζ hζS hζ ihζ =>
      have hζA : ζ ≤ A := lt_add_one_iff.mp hζS
      have hζs : ζ < omegaSequence τ 2 := hζA.trans_lt hAs
      by_cases hζΔ : ζ < Δ
      · have hζn := source_hull_next_notation α n 0 hn0 hΔsa.le hβa.le ihζ
        have hζp := sourceFiniteCollapse_proper_notation α n 0 hn0 ζ
          (hζΔ.trans hΔsa) hζn
        have hcall : sourceFiniteCollapse α n 0 ζ < β :=
          (finiteCollapse_hull_initial hn0 Δ _).mp ⟨.local hζΔ ihζ, hζp⟩
        exact .below_parameter ((finite_collapse_mono_base τ α hτ hle hαs n hn
          ζ hζn hζs).trans_lt hcall)
      · have hΔζ : Δ ≤ ζ := le_of_not_gt hζΔ
        have hρ : ζ - Δ ≤ η := by
          apply (add_le_add_iff_left Δ).mp
          rw [Ordinal.add_sub_cancel_of_le hΔζ, ← he]
          exact hζA
        have hζown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A α ζ := by
          rw [← Ordinal.add_sub_cancel_of_le hΔζ]
          exact .add hsplit.1 (.below_parameter (hρ.trans_lt hηα))
        by_cases hζeq : ζ = A
        · subst ζ
          exact .below_parameter hαβ
        · have hζlt : ζ < A := lt_of_le_of_ne hζA hζeq
          have hζn := source_hull_next_notation τ n 0 hn0 hAs.le hαs.le hζown
          have hζp := sourceFiniteCollapse_proper_notation τ n 0 hn0 ζ hζs hζn
          have hcall : sourceFiniteCollapse τ n 0 ζ < α :=
            (finiteCollapse_hull_initial hn0 A _).mp ⟨.local hζlt hζown, hζp⟩
          exact .below_parameter (hcall.trans hαβ)
  apply le_antisymm
  · exact relative_highPart_le_source_successor τ hτ n hn A Δ η hA hAs hΔ hη he
  · apply finiteCollapse_minimal hn0
    refine ⟨hβs, ?_, harg⟩
    intro ξ hx hξs
    exact (finiteCollapse_hull_initial hn0 Δ ξ).mp
      ⟨forward hx, by simpa only [← omega_succ τ α hle hαs 0] using hξs⟩

/-- Actual finite/global agreement derives the SAME exact endpoint identity
on the original global notation domain, with no fragment bound supplied. -/
theorem global_relative_highPart_eq_source_successor (τ : Ordinal.{0}) (hτ : 0 < τ)
    (A Δ η : Ordinal.{0}) (hA : GlobalNotation τ 1 A)
    (hAs : A < omegaSequence τ 2) (hΔ : omegaSequence τ 1 ∣ Δ)
    (hΔ0 : 0 < Δ) (hη : η < omegaSequence τ 1) (he : A = Δ + η) :
    globalCollapse (globalCollapse τ 0 A) 0 Δ = globalCollapse τ 0 (A + 1) := by
  obtain ⟨n, hn, hAn⟩ := globalNotation_finite_witness τ hτ 1 hA
  have hn0 : 0 < n := by omega
  have hAb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hAn hAs
  let α := globalCollapse τ 0 A
  have hα : α = sourceFiniteCollapse τ n 0 A :=
    globalCollapse_finite_agreement τ hτ n 0 hn0 A hAb
  have hle : τ ≤ α := by rw [hα]; simpa only [omegaSequence_zero] using
    (sourceFiniteCollapse_bounds τ n 0 hn0 A).1
  have hlt : α < omegaSequence τ 1 := by rw [hα]; exact
    sourceFiniteCollapse_proper_notation τ n 0 hn0 A hAs hAn
  have hαp : 0 < α := hτ.trans_le hle
  have hown : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 A α A := by
    rw [hα]; exact sourceFiniteCollapse_argument_notation τ n 0 hn0 A hAs hAn
  have hsplit := (source_hull_multiple_add_low_iff τ hτ n 0 hn0 A α Δ η hΔ hη).mp
    (by simpa only [he] using hown)
  have hΔn := source_hull_next_notation τ n 0 hn0 hAs.le hlt.le hsplit.1
  have hΔa := (next_notation_iff τ α hle hlt n hn Δ).mp hΔn
  have hΔA : Δ ≤ A := by rw [he]; exact le_self_add
  have hΔs : Δ < omegaSequence τ 2 := hΔA.trans_lt hAs
  have hΔsa : Δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hΔs
  have hΔb := source_finite_notation_sorted_lt_boundary α hαp n 1 1 le_rfl hn hΔa hΔsa
  have hSn := (SourceCollapseSuccessors.succArgument τ hτ n 0 hn0 ⟨A, hAn⟩).property
  have hSs := (omegaSequence_isSuccLimit τ 1).add_one_lt hAs
  have hSb := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hSn hSs
  rw [globalCollapse_finite_agreement α hαp n 0 hn0 Δ hΔb,
    globalCollapse_finite_agreement τ hτ n 0 hn0 (A + 1) hSb, hα]
  exact relative_highPart_eq_source_successor τ hτ n hn A Δ η hAn hAs hΔ hΔ0 hη he

/-- For EVERY original checked weak-normal high root, the already admitted
concrete target enclosure has exactly the original Convention 2.28 value.
There is no extra target/value/translation/height guard. -/
theorem delta_enclosure_eq_sourceValue (s a : Nat) (ha : rootCheck s a = true) :
    denote (alphaCode s a) (Enclosure.deltaEnclosureTerm s a) = sourceValue s a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact s a).mp ha
  let q := NativePublicBridge.contextCode s
  have hqp := base_pos q (NativePublicBridge.contextCode_checked s)
  have hc := Lambda.argument_accepted s a ha
  have htarg := BaseTransformation.theta_argument_check q 0 t ht
  have hA : GlobalNotation (base q) 1 (interpretation q (Lambda.argumentCode a)) := by
    apply globalNotation_embeds_next (base q) hqp 0
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      checked_globalNotation q t htarg
  have hAs : interpretation q (Lambda.argumentCode a) < omegaSequence (base q) 2 := by
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort q 0 t ht
  have hroot : interpretation q a = globalCollapse (base q) 0
      (interpretation q (Lambda.argumentCode a)) := by
    simp only [he, Lambda.argumentCode, Localization.argumentCode_theta, interpretation_code]
    rfl
  have hΔ0 : 0 < interpretation q (Lambda.deltaCode a) :=
    lt_of_le_of_ne (zero_le _) (Lambda.delta_nonzero s a ha).symm
  have hb := global_relative_highPart_eq_source_successor (base q) hqp
    (interpretation q (Lambda.argumentCode a)) (interpretation q (Lambda.deltaCode a))
    (interpretation q (Decomposition.lowCode 0 (Lambda.argumentCode a))) hA hAs
    (Decomposition.highPart_dvd q 0 (Lambda.argumentCode a) hc) hΔ0
    (Decomposition.lowPart_bound q 0 (Lambda.argumentCode a) hc)
    (Decomposition.parts_reconstruct q 0 (Lambda.argumentCode a) hc).symm
  rw [(Enclosure.delta_enclosure_spec s a ha).2.2.1, alpha_base s a ha, hroot]
  exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.AlphaPlus
