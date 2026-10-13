import Alexander313.Wilken.HereditaryNativeIotaAlphaPlusSupport

/-!
# Actual zero-family collapse monotonicity in an interval of bases

Positive-cardinal suffixes are identical on tau<=alpha<Omega1(tau).
The OWN alpha minimum hull supplies a genuine source argument: every local
alpha call is below that minimum and therefore an actual source parameter.
An ordinal induction then transfers the source candidate hull to the alpha
hull, bounding each local source call by the genuinely smaller alpha call.
Both inequalities used by minimality are derived from the actual minima.

This provides a comparison kernel for the missing bounded-high SAME-value
return. It proves theta_tau(delta)<=theta_alpha(delta), not equality with a
translated argument. Together with the existing opposite tail-shift bound
it leaves the exact high rewrite and its finite code construction open.
No relative-collapse, candidate, comparison or translation oracle occurs.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeCollapseMonotonicity

open Iota.AlphaPlus

/-- The alpha OWN minimum hull returns to the source at that SAME ceiling.
Every local alpha call is discarded into a genuine parameter below it. -/
theorem target_minimum_hull_to_source (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (δ : Ordinal.{0}) (hd : sourceNotation α n 1 δ)
    (hs : δ < omegaSequence τ 2) (ξ : Ordinal.{0})
    (hξ : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ
      (sourceFiniteCollapse α n 0 δ) ξ) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 δ
      (sourceFiniteCollapse α n 0 δ) ξ := by
  have hn0 : 0 < n := by omega
  have hsa : δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hs
  have hp := sourceFiniteCollapse_proper_notation α n 0 hn0 δ hsa hd
  have hαβ : α ≤ sourceFiniteCollapse α n 0 δ := by
    simpa only [omegaSequence_zero] using (sourceFiniteCollapse_bounds α n 0 hn0 δ).1
  induction hξ with
  | below_base h => exact .below_parameter (h.trans_le hαβ)
  | below_parameter h => exact .below_parameter h
  | add _ _ ihξ ihη => exact .add ihξ ihη
  | @higher k η hk hkn hsort hη ih =>
    rw [← positive_collapse τ α hle hlt n k hk hkn η]
    exact .higher hk hkn (by simpa only [omega_succ τ α hle hlt (k + 1)] using hsort) ih
  | @«local» η hηδ hη ih =>
    have hηs : η < omegaSequence α 2 := hηδ.trans hsa
    have hηn := source_hull_next_notation α n 0 hn0 hsa.le hp.le hη
    have hηp := sourceFiniteCollapse_proper_notation α n 0 hn0 η hηs hηn
    exact .below_parameter ((finiteCollapse_hull_initial hn0 δ _).mp
      ⟨.local hηδ hη, hηp⟩)

/-- A genuine simultaneous ordinal induction in the SAME finite fragment.
The only original domain is actual next-level notation and the actual sort. -/
theorem finite_collapse_mono_base (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (δ : Ordinal.{0}) (hd : sourceNotation α n 1 δ)
    (hs : δ < omegaSequence τ 2) :
    sourceFiniteCollapse τ n 0 δ ≤ sourceFiniteCollapse α n 0 δ := by
  classical
  revert hd hs
  refine Ordinal.induction δ ?_
  intro δ ih hd hs
  have hn0 : 0 < n := by omega
  let β := sourceFiniteCollapse α n 0 δ
  have hsa : δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hs
  have hβa : β < omegaSequence α 1 := sourceFiniteCollapse_proper_notation α n 0 hn0 δ hsa hd
  have hβs : β < omegaSequence τ 1 := by
    simpa only [omega_succ τ α hle hlt 0] using hβa
  have hown : Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β δ :=
    sourceFiniteCollapse_argument_notation α n 0 hn0 δ hsa hd
  have harg := target_minimum_hull_to_source τ α hτ hle hlt n hn δ hd hs δ hown
  have forward {ξ : Ordinal.{0}}
      (hx : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 δ β ξ) :
      Hull (omegaSequence α) (sourceFiniteCollapse α n) n 0 δ β ξ := by
    induction hx with
    | below_base h => exact .below_base (h.trans_le hle)
    | below_parameter h => exact .below_parameter h
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | @higher k η hk hkn hsort hη ihη =>
      rw [positive_collapse τ α hle hlt n k hk hkn η]
      exact .higher hk hkn (by simpa only [← omega_succ τ α hle hlt (k + 1)] using hsort) ihη
    | @«local» η hηδ hη ihη =>
      have hηs : η < omegaSequence τ 2 := hηδ.trans hs
      have hηa : η < omegaSequence α 2 := hηδ.trans hsa
      have hηn := source_hull_next_notation α n 0 hn0 hsa.le hβa.le ihη
      have hηp := sourceFiniteCollapse_proper_notation α n 0 hn0 η hηa hηn
      have hcall : sourceFiniteCollapse α n 0 η < β :=
        (finiteCollapse_hull_initial hn0 δ _).mp ⟨.local hηδ ihη, hηp⟩
      exact .below_parameter ((ih η hηδ hηn hηs).trans_lt hcall)
  apply finiteCollapse_minimal hn0
  refine ⟨hβs, ?_, harg⟩
  intro ξ hx hsort
  exact (finiteCollapse_hull_initial hn0 δ ξ).mp
    ⟨forward hx, by simpa only [← omega_succ τ α hle hlt 0] using hsort⟩

/-- The two genuine finite-minimum comparisons bracket the target value.
This is an interval estimate, explicitly not a same-value rewrite. -/
theorem finite_collapse_bracket (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (n : Nat) (hn : 1 < n)
    (δ : Ordinal.{0}) (hd : sourceNotation α n 1 δ)
    (hs : δ < omegaSequence τ 2) :
    sourceFiniteCollapse τ n 0 δ ≤ sourceFiniteCollapse α n 0 δ ∧
      sourceFiniteCollapse α n 0 δ ≤ sourceFiniteCollapse τ n 0
        (tailShift (omegaSequence τ 1) α δ) :=
  ⟨finite_collapse_mono_base τ α hτ hle hlt n hn δ hd hs,
    relative_collapse_le_tailShift τ α hτ hle hlt n hn δ hd hs⟩

/-- Actual finite/global fidelity obtains BOTH real agreement bounds from
one original target fragment; no global comparison premise is supplied. -/
theorem global_collapse_mono_base (τ α : Ordinal.{0}) (hτ : 0 < τ)
    (hle : τ ≤ α) (hlt : α < omegaSequence τ 1) (δ : Ordinal.{0})
    (hd : GlobalNotation α 1 δ) (hs : δ < omegaSequence τ 2) :
    globalCollapse τ 0 δ ≤ globalCollapse α 0 δ := by
  have hα : 0 < α := hτ.trans_le hle
  obtain ⟨n, hn, hdn⟩ := globalNotation_finite_witness α hα 1 hd
  have hn0 : 0 < n := by omega
  have hdτ := (next_notation_iff τ α hle hlt n hn δ).mpr hdn
  have hsa : δ < omegaSequence α 2 := by
    simpa only [← omega_succ τ α hle hlt 1] using hs
  have hbτ := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl hn hdτ hs
  have hbα := source_finite_notation_sorted_lt_boundary α hα n 1 1 le_rfl hn hdn hsa
  rw [globalCollapse_finite_agreement τ hτ n 0 hn0 δ hbτ,
    globalCollapse_finite_agreement α hα n 0 hn0 δ hbα]
  exact finite_collapse_mono_base τ α hτ hle hlt n hn δ hdn hs

/-- The actual original Iota root supplies BOTH base-interval bounds. Every
original checked target zero-index call supplies its real next-level argument
notation and cardinal sort, including arbitrary hidden positive arguments. -/
theorem root_target_zero_mono (s a : Nat) (ha : Iota.rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (Iota.alphaCode s a) (.theta 0 t) = true) :
    globalCollapse (base (NativePublicBridge.contextCode s)) 0
        (denote (Iota.alphaCode s a) t) ≤ denote (Iota.alphaCode s a) (.theta 0 t) := by
  let τ := base (NativePublicBridge.contextCode s)
  let α := base (Iota.alphaCode s a)
  have hτ := base_pos _ (NativePublicBridge.contextCode_checked s)
  have hle : τ ≤ α := by simpa only [Iota.alpha_base s a ha] using Iota.root_base_le s a ha
  have hlt : α < omegaSequence τ 1 := by
    rw [Iota.alpha_base s a ha]
    exact (HeightBoundary.input_spec _ a (Iota.root_low s a ha)).2.2
  have hc := FixedPoint.checked_theta_argument _ 0 t ht
  have hn : GlobalNotation α 1 (denote (Iota.alphaCode s a) t) :=
    (FixedPoint.sourceOrdinal (Iota.alphaCode s a) 0 t hc).property
  have hs : denote (Iota.alphaCode s a) t < omegaSequence τ 2 := by
    simpa only [omega_succ τ α hle hlt 1] using FixedPoint.checked_theta_sort _ 0 t ht
  exact global_collapse_mono_base τ α hτ hle hlt _ hn hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RelativeCollapseMonotonicity
