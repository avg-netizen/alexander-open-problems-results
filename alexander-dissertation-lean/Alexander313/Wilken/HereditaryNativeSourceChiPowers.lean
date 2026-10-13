import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.HereditaryNativeLowArithmetic
import Alexander313.Wilken.LowOmegaArithmetic

/-!
# Actual last logarithm and omega-power indicator laws

The proof matches Definition 3.3 against the real low-collapse exponent,
including its strictly-above-base epsilon-plus-natural correction. Finite
suffix absorption retains the last indicator; a zero last exponent has
indicator zero. Actual sorted high collapses are epsilons by their genuine
hull theorem. No arithmetic-indicator or spelling-invariance premise is
supplied. Executing arithmetic uses the original same-positive-public
epsilon context and the previously constructed low producers.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Powers

open Comparison (Normal atoms)

private theorem last_append (as bs : List Entry) (hb : bs ≠ []) :
    lastIndicator (as ++ bs) = lastIndicator bs := by
  unfold lastIndicator
  rw [List.reverse_append]
  cases hr : bs.reverse with
  | nil =>
    have he : bs = [] := by simpa using congrArg List.reverse hr
    exact False.elim (hb he)
  | cons b cs => rfl

private theorem normalizeAtoms_nil (q : Nat) (as : List (RelativeTerm Nat)) :
    Normalization.normalizeAtoms q as = [] ↔ as = [] := by
  induction as with
  | nil => simp only [Normalization.normalizeAtoms]
  | cons a as ih =>
    cases ht : Normalization.normalizeAtoms q as with
    | nil => simp only [Normalization.normalizeAtoms, ht, Normalization.prependAtom,
        List.cons_ne_nil, iff_false]
    | cons b bs =>
      cases hc : Comparison.less q a b <;>
        simp only [Normalization.normalizeAtoms, ht, Normalization.prependAtom, hc,
          Bool.cond_true, Bool.cond_false, List.cons_ne_nil, iff_false]

/-- This is literal finite suffix absorption, independent of chi semantics. -/
theorem lastIndicator_normalizeAtoms (q : Nat) (as : List (RelativeTerm Nat)) :
    lastIndicator ((Normalization.normalizeAtoms q as).map (fun a => (a, indicator q a))) =
      lastIndicator (as.map (fun a => (a, indicator q a))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases ht : Normalization.normalizeAtoms q as with
    | nil =>
      have he := (normalizeAtoms_nil q as).mp ht
      subst as
      rfl
    | cons b bs =>
      have hn : as ≠ [] := by
        intro he
        simp only [he, Normalization.normalizeAtoms] at ht
      have hleft : lastIndicator ((a :: b :: bs).map (fun a => (a, indicator q a))) =
          lastIndicator ((b :: bs).map (fun a => (a, indicator q a))) :=
        last_append [(a, indicator q a)] _ (by simp)
      have hright : lastIndicator ((a :: as).map (fun a => (a, indicator q a))) =
          lastIndicator (as.map (fun a => (a, indicator q a))) :=
        last_append [(a, indicator q a)] _ (by simpa using hn)
      cases hc : Comparison.less q a b <;>
        simpa only [Normalization.normalizeAtoms, ht, Normalization.prependAtom, hc,
          Bool.cond_true, Bool.cond_false, hleft, hright] using ih

theorem indicator_endAtom (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t) :
    indicator q (LogEndZero.endAtom t.code) = indicator q t := by
  rw [SourceChi.Arithmetic.indicator_atoms q t ht hn]
  rw [LogEndZero.endAtom, Decomposition.word, ThetaCourse.rawTree_code]
  unfold lastIndicator
  rw [← List.map_reverse]
  cases (atoms t).reverse <;> rfl

/-- The literal zero-last-exponent branch has indicator zero, including zero. -/
theorem indicator_sourceZero (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Normal q t)
    (hz : Hereditary.LogEndZero.SourceZero (denote q t)) : indicator q t = false := by
  have hq := (Bool.and_eq_true.mp ht).1
  rcases hz with hz | hz
  · exact indicator_below_base q t ht hn (by rw [hz]; exact base_pos q hq)
  · have hi : Decomposition.inputCheck q t.code = true :=
      (Decomposition.inputCheck_exact q _).mpr ⟨by simpa only [checkCode_code] using ht,
        by simpa only [ThetaCourse.rawTree_code] using hn⟩
    have he := LogEndZero.endAtom_checked q t.code hi
    rw [← indicator_endAtom q t ht hn]
    apply indicator_below_base q _ he.1 he.2
    rw [LogEndZero.endAtom_value q t.code hi, interpretation_code, hz]
    exact LogEndZero.one_lt_base q hq

theorem indicator_addTerm_positive (q c : Nat) (b : RelativeTerm Nat)
    (hb : check q b = true) (hn : Normal q b) (hp : 0 < denote q b) :
    indicator q (NativeContext.Arithmetic.addTerm q c b.code) = indicator q b := by
  have hnb := Normalization.normalize_checked q b hb
  have hq := (Bool.and_eq_true.mp hb).1
  have hword : atoms (Normalization.normalize q b) ≠ [] := by
    intro he
    have hv := Comparison.atoms_value q _ hq (Normalization.normalize q b)
      (NativeContext.checked_admissible q _ hnb.1) hnb.2.1
    have hz : denote q b = 0 := by
      simpa only [he, List.map_nil, principalSum, hnb.2.2] using hv.symm
    exact (ne_of_gt hp) hz
  unfold NativeContext.Arithmetic.addTerm
  rw [ThetaCourse.rawTree_code]
  change indicator q (Normalization.buildAtoms (Normalization.normalizeAtoms q
    (atoms (Normalization.normalize q (ThetaCourse.rawTree c)) ++
      atoms (Normalization.normalize q b)))) = _
  rw [indicator_buildAtoms, lastIndicator_normalizeAtoms, List.map_append,
    last_append _ _ (by simpa using hword),
    ← SourceChi.Arithmetic.indicator_atoms q _ hnb.1 hnb.2.1]
  exact SourceChi.Arithmetic.indicator_normalize q b hb hn

theorem chiCode_add_positive (q c d : Nat) (hc : checkCode q c = true)
    (hd : SourceChi.inputCheck q d = true) (hp : 0 < interpretation q d) :
    chiCode q (NativeContext.Arithmetic.addCode q c d) = chiCode q d := by
  obtain ⟨hdc, hdn⟩ := (SourceChi.inputCheck_exact q d).mp hd
  obtain ⟨b, rfl, hb⟩ := (checkCode_exact q d).mp hdc
  have hn : Normal q b := by simpa only [ThetaCourse.rawTree_code] using hdn
  have hpb : 0 < denote q b := by simpa only [interpretation_code] using hp
  have hi := (NativeContext.Arithmetic.inputCheck_exact q c b.code).mpr ⟨hc, by
    simpa only [checkCode_code] using hb⟩
  have ho := NativeContext.Arithmetic.addTerm_spec q c b.code hc (by
    simpa only [checkCode_code] using hb)
  have hq := (Bool.and_eq_true.mp hb).1
  rw [NativeContext.Arithmetic.addCode, hi, Bool.cond_true,
    chiCode_correct q _ (Comparison.admitted_checked q _ hq _ ho.1) ho.2.1,
    chiCode_correct q b hb hn]
  exact indicator_addTerm_positive q c b hb hn hpb

theorem canonicalANF_successor (a : Ordinal.{0}) : canonicalANF (a + 1) = canonicalANF a ++ [1] := by
  have hn := canonicalANF_normal a
  apply canonicalANF_eq_of_normal
  · constructor
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hn.1 b hb
      · have he := List.mem_singleton.mp hb
        subst b
        exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one⟩
    · apply List.pairwise_append.mpr
      refine ⟨hn.2, by simp only [List.pairwise_singleton], ?_⟩
      intro b hb c hc
      have he := List.mem_singleton.mp hc
      subst c
      exact Order.one_le_iff_pos.mpr (hn.1 b hb).1
  · rw [principalSum_append]
    simp only [principalSum_canonicalANF, principalSum, add_zero]

theorem endValue_successor (a : Ordinal.{0}) : LogEnd.endValue (a + 1) = 1 := by
  simp only [LogEnd.endValue, LogEnd.componentValue, Bool.cond_true,
    canonicalANF_successor, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.getElem?_cons_zero, Option.getD_some]

theorem global_high_epsilon (τ : Ordinal.{0}) (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ)
    (b : GlobalNotationOrdinal τ 1) (hs : b.val < omegaSequence τ 2)
    (hh : omegaSequence τ 1 ≤ b.val) :
    Ordinal.omega0 ^ globalCollapse τ 0 b.val = globalCollapse τ 0 b.val := by
  have hp := epsilon_or_one_pos hτ
  obtain ⟨n, h1n, hb⟩ := globalNotation_finite_witness τ hp 1 b.property
  have hn : 0 < n := (Nat.zero_le 1).trans_lt h1n
  have hbound := source_finite_notation_sorted_lt_boundary τ hp n 1 1 le_rfl h1n hb hs
  rw [globalCollapse_finite_agreement τ hp n 0 hn b.val hbound]
  exact ((sourceFiniteCollapse_epsilon_above_base_iff τ hτ n 0 hn b.val hs hb).mpr hh).1

theorem theta_epsilon_of_high (q : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hh : omegaSequence (base q) 1 ≤ denote q a) :
    Ordinal.omega0 ^ denote q (.theta 0 a) = denote q (.theta 0 a) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := FixedPoint.checked_theta_argument q 0 a ht
  exact global_high_epsilon (base q) (Or.inr (epsilon_base q hq))
    (FixedPoint.sourceOrdinal q 0 a ha) (FixedPoint.checked_theta_sort q 0 a ht) hh

theorem checked_theta_zero (q : Nat) (a : RelativeTerm Nat) (ha : check q a = true)
    (hs : denote q a < omegaSequence (base q) 2) : check q (.theta 0 a) = true := by
  have hq := (Bool.and_eq_true.mp ha).1
  let n := max a.height 1
  have hn : 0 < n := (Nat.zero_lt_succ 0).trans_le (le_max_right _ _)
  have had := Comparison.checked_admissible q n a ha (le_max_left _ _)
  have hsf : finiteDenote q n a < omegaSequence (base q) 2 := by
    rw [← denote_eq_finite q n hq a had.2]
    exact hs
  exact Comparison.admitted_checked q n hq _ ⟨had.1, .theta (Nat.zero_le 0) hn hsf had.2⟩

def baseTree : RelativeTerm Nat := .theta 0 Normalization.zeroTree

theorem baseTree_checked (q : Nat) (hq : baseCheck q = true) : check q baseTree = true :=
  checked_theta_zero q _ (Normalization.zeroTree_checked q hq) (by
    rw [Normalization.zeroTree_denote]
    exact (base_pos q hq).trans_le ((omegaSequence_strictMono (base q)).monotone (Nat.zero_le 2)))

theorem baseTree_normal (q : Nat) : Normal q baseTree := Normalization.zeroTree_normal q

theorem baseTree_value (q : Nat) (hq : baseCheck q = true) : denote q baseTree = base q := by
  change globalCollapse (base q) 0 (denote q Normalization.zeroTree) = base q
  rw [Normalization.zeroTree_denote, globalCollapse_zero (base q) (base_pos q hq)
    (base_add_closed q hq) 0, omegaSequence_zero]

theorem global_high_base_lt (τ : Ordinal.{0}) (hτ : 0 < τ)
    (b : GlobalNotationOrdinal τ 1) (hs : b.val < omegaSequence τ 2)
    (hh : omegaSequence τ 1 ≤ b.val) : τ < globalCollapse τ 0 b.val := by
  obtain ⟨n, h1n, hb⟩ := globalNotation_finite_witness τ hτ 1 b.property
  have hn : 0 < n := (Nat.zero_le 1).trans_lt h1n
  have hbound := source_finite_notation_sorted_lt_boundary τ hτ n 1 1 le_rfl h1n hb hs
  rw [globalCollapse_finite_agreement τ hτ n 0 hn b.val hbound]
  simpa only [omegaSequence_zero] using sourceFiniteCollapse_high_base_lt τ hτ n 0 hn b.val hh

/-- This derives the fixed residual's epsilon property from the genuine
higher presentation; no epsilon/fixed-point equivalence is assumed. -/
theorem fixed_low_epsilon (q : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hn : Normal q (.theta 0 a))
    (hl : denote q a < omegaSequence (base q) 1) (hp : 0 < denote q a)
    (hf : FixedPoint.SourceFixed q 0 a.code) :
    Ordinal.omega0 ^ denote q a = denote q a ∧ base q < denote q a := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hi := theta_argument_input q 0 a ht hn
  have ha := (theta_argument_parts q 0 a ht hn).1
  have hv := Decomposition.parts_code_value q 0 a.code ha
  have hd : interpretation q (Decomposition.highCode 0 a.code) = 0 := by
    rw [hv.1, interpretation_code, Ordinal.div_eq_zero_of_lt hl, mul_zero]
  have he : interpretation q (Decomposition.lowCode 0 a.code) = denote q a := by
    rw [hv.2, interpretation_code, Ordinal.mod_eq_of_lt hl]
  rcases (FixedPoint.fixed_parts_iff q 0 a.code hi).mp hf with hz | hh
  · exact False.elim ((ne_of_gt hp) (he.symm.trans hz))
  · obtain ⟨b, Γ, ρ, hbm, hbs, hΓ, hρ, hbe, hdΓ, hη, hstar⟩ := hh
    have hΓpos : 0 < Γ := by simpa only [FixedPoint.checkedOrdinal_val, hd] using hdΓ
    obtain ⟨δ, hδ⟩ := hΓ
    have hδpos : 0 < δ := by
      apply pos_iff_ne_zero.mpr
      intro hz
      rw [hδ, hz, mul_zero] at hΓpos
      exact (lt_irrefl 0) hΓpos
    have hΩΓ : omegaSequence (base q) 1 ≤ Γ := by
      rw [hδ]
      simpa only [mul_one] using mul_le_mul' (le_rfl : omegaSequence (base q) 1 ≤ _)
        (Order.one_le_iff_pos.mpr hδpos)
    have hbhigh : omegaSequence (base q) 1 ≤ b.val :=
      hΩΓ.trans (by rw [hbe]; exact le_self_add)
    have hvalue : denote q a = globalCollapse (base q) 0 b.val := he.symm.trans hη
    rw [hvalue]
    exact ⟨global_high_epsilon (base q) (Or.inr (epsilon_base q hq)) b hbs hbhigh,
      global_high_base_lt (base q) (base_pos q hq) b hbs hbhigh⟩

/-- Actual cofinal low images prove the converse needed by the epsilon
offset case. The bounded supremum is the original ordinary supremum. -/
theorem epsilon_low_sup_fixed (τ ε : Ordinal.{0}) (hτ : Ordinal.omega0 ^ τ = τ)
    (hτε : τ < ε) (hε : Ordinal.omega0 ^ ε = ε)
    (hl : ε < omegaSequence τ 1) :
    SourceFixedPointLimits.globalResidualImageSup τ 0 0 ε = ε := by
  have hτpos := epsilon_or_one_pos (Or.inr hτ)
  have hεpos := epsilon_or_one_pos (Or.inr hε)
  have hεp := epsilon_or_one_add_closed (Or.inr hε)
  have hεone : 1 < ε := Ordinal.one_lt_omega0.trans (epsilon_omega_lt hε)
  have hlim := Ordinal.isSuccLimit_of_isPrincipal_add hεone hεp
  apply le_antisymm
  · apply Ordinal.bsup_le
    intro σ hσ
    change globalCollapse τ 0 (0 + σ) ≤ ε
    rw [zero_add, globalCollapse_low_eq_omegaPower τ (Or.inr hτ) σ (hσ.trans hl)]
    have hshift : τ + σ < ε := hεp hτε hσ
    have he : lowOmegaExponent τ σ < ε := by
      exact (lowOmegaExponent_le_shift_succ τ σ).trans_lt (by
        rw [lowOmegaBase_of_epsilon τ hτ]
        exact hlim.add_one_lt hshift)
    exact (omegaPower_strictMono he).le.trans_eq hε
  · by_contra! hs
    have hp := globalCollapse_low_argument_lt τ hτpos 0
      (SourceFixedPointLimits.globalResidualImageSup τ 0 0 ε) (hs.trans hl)
    have hb := Ordinal.le_bsup (fun σ _ => globalCollapse τ 0 (0 + σ))
      (SourceFixedPointLimits.globalResidualImageSup τ 0 0 ε) hs
    have hb' : globalCollapse τ 0 (SourceFixedPointLimits.globalResidualImageSup τ 0 0 ε) ≤
        SourceFixedPointLimits.globalResidualImageSup τ 0 0 ε := by simpa only [zero_add] using hb
    exact hp.not_ge hb'

theorem low_chooseHigh_iff (q : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hn : Normal q (.theta 0 a))
    (hl : denote q a < omegaSequence (base q) 1) :
    chooseHigh q 0 a.code = true ↔
      SourceFixedPointLimits.globalResidualImageSup (base q) 0 0 (denote q a) = denote q a ∨
        Hereditary.LogEndZero.SourceZero (denote q a) := by
  have hv := Decomposition.parts_code_value q 0 a.code (theta_argument_parts q 0 a ht hn).1
  rw [chooseHigh_correct q 0 a ht hn]
  simp only [FixedPoint.SourceFixed, FixedPoint.delta, FixedPoint.residual,
    hv.2, interpretation_code, Ordinal.div_eq_zero_of_lt hl, mul_zero,
    Ordinal.mod_eq_of_lt hl]

theorem indicator_low_theta (q : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hn : Normal q (.theta 0 a))
    (hl : denote q a < omegaSequence (base q) 1) (hp : 0 < denote q a) :
    indicator q (.theta 0 a) = cond (chooseHigh q 0 a.code) false (indicator q a) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := (theta_argument_parts q 0 a ht hn).1
  have hv := Decomposition.parts_code_value q 0 a.code ha
  have hdv : denote q (Decomposition.highPartTerm 0 a.code) = 0 := by
    simpa only [Decomposition.highCode, interpretation_code,
      Ordinal.div_eq_zero_of_lt hl, mul_zero] using hv.1
  have hd := (Decomposition.parts_checked q 0 a.code ha).1
  have hdn := (Decomposition.parts_normal q 0 a.code ha).1
  have hχ := indicator_below_base q _ hd hdn (by rw [hdv]; exact base_pos q hq)
  rw [indicator_theta, baseCase_false q 0 a ht hn (fun _ => hp), Bool.cond_false, hχ]

/-- The actual low exponent has exactly the source theta indicator.
The returned exponent code is any ORIGINAL checked normal representative
of that literal exponent; the final public theorem uses the real producer. -/
theorem chi_low_exponent (q e : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hn : Normal q (.theta 0 a))
    (hl : denote q a < omegaSequence (base q) 1) (hp : 0 < denote q a)
    (he : SourceChi.inputCheck q e = true)
    (hv : interpretation q e = lowOmegaExponent (base q) (denote q a)) :
    chiCode q e = indicator q (.theta 0 a) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hac := FixedPoint.checked_theta_argument q 0 a ht
  have hai := (theta_argument_parts q 0 a ht hn).1
  by_cases hoff : EpsilonFiniteAbove (base q) (denote q a)
  · have hev : interpretation q e = denote q a + 1 :=
      hv.trans (lowOmegaExponent_of_offset _ _ hoff)
    have hen := (SourceChi.inputCheck_exact q e).mp he
    obtain ⟨t, rfl, hct⟩ := (checkCode_exact q e).mp hen.1
    have hnt : Normal q t := by simpa only [ThetaCourse.rawTree_code] using hen.2
    have hzero : indicator q t = false := by
      apply indicator_sourceZero q t hct hnt
      right
      rw [← interpretation_code, hev, endValue_successor]
    have hc : chooseHigh q 0 a.code = true := by
      apply (low_chooseHigh_iff q a ht hn hl).mpr
      obtain ⟨ε, k, hτε, hε, hval⟩ := hoff
      cases k with
      | zero =>
        left
        have haε : denote q a = ε := by simpa only [Nat.cast_zero, add_zero] using hval
        rw [haε]
        exact epsilon_low_sup_fixed (base q) ε (epsilon_base q hq) hτε hε (haε ▸ hl)
      | succ k =>
        right
        right
        rw [hval, Nat.cast_succ, ← add_assoc, endValue_successor]
    rw [chiCode_correct q t hct hnt, hzero, indicator_low_theta q a ht hn hl hp, hc]
    rfl
  · have hv' : interpretation q e = base q + denote q a := by
      rw [hv, lowOmegaExponent_of_not_offset _ _ hoff, lowOmegaBase_of_epsilon _ (epsilon_base q hq)]
    have hbc : checkCode q baseTree.code = true := by
      simpa only [checkCode_code] using baseTree_checked q hq
    have hsum := NativeContext.Arithmetic.addCode_spec q baseTree.code a.code hbc (by
      simpa only [checkCode_code] using hac)
    have hsame : chiCode q e = chiCode q (NativeContext.Arithmetic.addCode q baseTree.code a.code) :=
      Invariance.chiCode_invariant q _ _ he hsum.1 (by
        rw [hsum.2.1, interpretation_code, baseTree_value q hq, interpretation_code]
        exact hv')
    rw [hsame, chiCode_add_positive q baseTree.code a.code hbc hai (by
      simpa only [interpretation_code] using hp), chiCode_correct q a hac hn]
    rw [indicator_low_theta q a ht hn hl hp]
    cases hc : chooseHigh q 0 a.code with
    | false => rfl
    | true =>
      have hcases := (low_chooseHigh_iff q a ht hn hl).mp hc
      rcases hcases with hf | hz
      · have hfixed : FixedPoint.SourceFixed q 0 a.code := by
          simpa only [FixedPoint.SourceFixed, FixedPoint.delta, FixedPoint.residual,
            interpretation_code, Ordinal.div_eq_zero_of_lt hl, mul_zero,
            Ordinal.mod_eq_of_lt hl] using hf
        have heps := fixed_low_epsilon q a ht hn hl hp hfixed
        exact False.elim (hoff ⟨denote q a, 0, heps.2, heps.1, by simp⟩)
      · exact indicator_sourceZero q a hac hn hz

theorem theta_principal (q : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) :
    0 < denote q (.theta 0 a) ∧ Ordinal.IsPrincipal (· + ·) (denote q (.theta 0 a)) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := NativeContext.checked_admissible q (.theta 0 a) ht
  rw [denote_eq_finite q _ hq _ ha.2]
  exact Comparison.theta_pos_principal q _ 0 hq a ha

theorem endValue_principal (α : Ordinal.{0}) (hp : 0 < α)
    (ha : Ordinal.IsPrincipal (· + ·) α) : LogEnd.endValue α = α := by
  simp only [LogEnd.endValue, LogEnd.componentValue, Bool.cond_true,
    canonicalANF_principal hp ha, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.getElem?_cons_zero, Option.getD_some]

theorem not_offset_of_principal_non_epsilon (τ α : Ordinal.{0})
    (hp : 0 < α) (ha : Ordinal.IsPrincipal (· + ·) α)
    (he : Ordinal.omega0 ^ α ≠ α) : ¬ EpsilonFiniteAbove τ α := by
  rintro ⟨ε, n, hτε, hε, hα⟩
  cases n with
  | zero =>
    have hαε : α = ε := by simpa only [Nat.cast_zero, add_zero] using hα
    exact he (by simpa only [hαε] using hε)
  | succ n =>
    have hb : 0 < ε + (n : Ordinal.{0}) :=
      (epsilon_or_one_pos (Or.inr hε)).trans_le le_self_add
    have heq : α = (ε + (n : Ordinal.{0})) + 1 := by
      simpa only [Nat.cast_succ, ← add_assoc] using hα
    have hleft : ε + (n : Ordinal.{0}) < α := by rw [heq]; exact lt_add_one _
    have hone : 1 < α := (Order.one_le_iff_pos.mpr hb).trans_lt hleft
    exact (ne_of_lt (ha hleft hone)) heq.symm

theorem chi_omegaPower (q e : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hn : Normal q (.theta 0 a))
    (hproper : base q < denote q (.theta 0 a))
    (he : SourceChi.inputCheck q e = true)
    (hv : interpretation q e = Ordinal.omega0 ^ denote q (.theta 0 a)) :
    chiCode q e = chiCode q (.theta 0 a : RelativeTerm Nat).code := by
  have hq := (Bool.and_eq_true.mp ht).1
  let t : RelativeTerm Nat := .theta 0 a
  have hti : SourceChi.inputCheck q t.code = true :=
    (SourceChi.inputCheck_exact q _).mpr ⟨by simpa only [checkCode_code] using ht,
      by simpa only [ThetaCourse.rawTree_code] using hn⟩
  by_cases heps : Ordinal.omega0 ^ denote q t = denote q t
  · exact Invariance.chiCode_invariant q e t.code he hti (by
      simpa only [interpretation_code, heps] using hv)
  · have hp := theta_principal q a ht
    have hl : denote q t < omegaSequence (base q) 1 := (FixedPoint.checked_theta_range q 0 a ht).2
    have hθ : check q (.theta 0 t) = true :=
      checked_theta_zero q t ht (hl.trans (omegaSequence_step (base q) 1))
    have hnot := not_offset_of_principal_non_epsilon (base q) (denote q t) hp.1 hp.2 heps
    have hexp : lowOmegaExponent (base q) (denote q t) = denote q t := by
      rw [lowOmegaExponent_of_not_offset _ _ hnot, lowOmegaBase_of_epsilon _ (epsilon_base q hq),
        hp.2.add_eq_right hproper]
    have hval : denote q (.theta 0 t) = Ordinal.omega0 ^ denote q t := by
      change globalCollapse (base q) 0 (denote q t) = _
      rw [globalCollapse_low_eq_omegaPower (base q) (Or.inr (epsilon_base q hq)) _ hl, hexp]
    have hθi : SourceChi.inputCheck q (.theta 0 t : RelativeTerm Nat).code = true :=
      (SourceChi.inputCheck_exact q _).mpr ⟨by simpa only [checkCode_code] using hθ,
        by simpa only [ThetaCourse.rawTree_code, Comparison.Normal] using hn⟩
    have hχ := chi_low_exponent q t.code t hθ hn hl hp.1 hti (by
      rw [interpretation_code, hexp])
    have hc := Invariance.chiCode_invariant q e (.theta 0 t : RelativeTerm Nat).code he hθi
      (by rw [interpretation_code, hval]; exact hv)
    rw [hc, chiCode_correct q _ hθ hn]
    exact hχ.symm

/-- The source logend clause on ORIGINAL proper theta-zero terms. The
literal last-exponent relation is converted to the real low exponent or
to the original epsilon itself, using omega-power injectivity. -/
theorem chi_logend (q e : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hn : Normal q (.theta 0 a))
    (hproper : base q < denote q (.theta 0 a))
    (he : SourceChi.inputCheck q e = true)
    (hv : LogEnd.SourceLogSpec true (denote q (.theta 0 a)) (interpretation q e)) :
    chiCode q e = chiCode q (.theta 0 a : RelativeTerm Nat).code := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hp := theta_principal q a ht
  have hexp : Ordinal.omega0 ^ interpretation q e = denote q (.theta 0 a) := by
    simpa only [LogEnd.SourceLogSpec, if_neg (ne_of_gt hp.1), LogEnd.componentValue,
      Bool.cond_true, canonicalANF_principal hp.1 hp.2, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.getElem?_cons_zero, Option.getD_some] using hv
  have hti : SourceChi.inputCheck q (.theta 0 a : RelativeTerm Nat).code = true :=
    (SourceChi.inputCheck_exact q _).mpr ⟨by simpa only [checkCode_code] using ht,
      by simpa only [ThetaCourse.rawTree_code] using hn⟩
  by_cases hl : denote q a < omegaSequence (base q) 1
  · have harg : 0 < denote q a :=
      pos_iff_ne_zero.mpr ((SourceChi.Arithmetic.proper_theta_zero_iff q a ht hn).mp hproper)
    have heval : interpretation q e = lowOmegaExponent (base q) (denote q a) := by
      apply omegaPower_strictMono.injective
      rw [hexp]
      exact globalCollapse_low_eq_omegaPower (base q) (Or.inr (epsilon_base q hq)) _ hl
    rw [chiCode_correct q _ ht hn]
    exact chi_low_exponent q e a ht hn hl harg he heval
  · have heps := theta_epsilon_of_high q a ht (le_of_not_gt hl)
    have heval : interpretation q e = denote q (.theta 0 a) :=
      omegaPower_strictMono.injective (hexp.trans heps.symm)
    exact Invariance.chiCode_invariant q e _ he hti (by
      simpa only [interpretation_code] using heval)

/-- The proper literal source domain. Its argument is ORIGINAL checked and
weak-normal, the theta call is genuine, and the nonzero proviso is tested. -/
def sourceInput (s a : Nat) : Bool :=
  let q := NativePublicBridge.contextCode s
  SourceChi.inputCheck q a && (checkCode q (SourceChi.Arithmetic.rightCode a) && !FixedPoint.zeroCheck a)

theorem sourceInput_primrec : Primrec₂ sourceInput := by
  have hq := NativePublicBridge.contextCode_primrec.comp Primrec.fst
  have ha := Primrec.snd
  exact (Primrec.and.comp (SourceChi.inputCheck_primrec.comp hq ha)
    (Primrec.and.comp (checkCode_primrec.comp hq (SourceChi.Arithmetic.rightCode_primrec.comp ha))
      (Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp ha)))).to₂

theorem sourceInput_literal (s a : Nat) : sourceInput s a = true ↔
    checkCode (NativePublicBridge.contextCode s) a = true ∧
      Normal (NativePublicBridge.contextCode s) (ThetaCourse.rawTree a) ∧
      check (NativePublicBridge.contextCode s) (.theta 0 (ThetaCourse.rawTree a)) = true ∧
      base (NativePublicBridge.contextCode s) <
        denote (NativePublicBridge.contextCode s) (.theta 0 (ThetaCourse.rawTree a)) := by
  let q := NativePublicBridge.contextCode s
  have hz : lowCheckCode q Normalization.zeroTree.code = true := by
    simp only [lowCheckCode_code, lowCheck, Normalization.zeroTree_checked q
      (NativePublicBridge.contextCode_checked s), Normalization.zeroTree,
      RelativeTerm.outerSort, decide_true, Bool.true_and]
  have he : sourceInput s a = SourceChi.Arithmetic.sourceInput q Normalization.zeroTree.code a := by
    simp only [sourceInput, SourceChi.Arithmetic.sourceInput, hz, Bool.true_and]
  rw [he, SourceChi.Arithmetic.sourceInput_literal]
  simp only [hz, true_and]

theorem sourceInput_low (s a : Nat) (h : sourceInput s a = true) :
    LowArithmetic.lowInput s (SourceChi.Arithmetic.rightCode a) = true ∧
      SourceChi.inputCheck (NativePublicBridge.contextCode s) (SourceChi.Arithmetic.rightCode a) = true := by
  have hl := (sourceInput_literal s a).mp h
  constructor
  · simp only [LowArithmetic.lowInput, SourceChi.Arithmetic.rightCode, lowCheckCode_code,
      lowCheck, hl.2.2.1, RelativeTerm.outerSort, decide_true, Bool.true_and]
  · apply (SourceChi.inputCheck_exact _ _).mpr
    exact ⟨by simpa only [SourceChi.Arithmetic.rightCode, checkCode_code] using hl.2.2.1,
      by simpa only [SourceChi.Arithmetic.rightCode, ThetaCourse.rawTree_code, Comparison.Normal] using hl.2.1⟩

theorem source_lemma_3_5_a_omega (s a : Nat) (h : sourceInput s a = true) :
    chiCode (NativePublicBridge.contextCode s)
      (LowArithmetic.omegaCode s (SourceChi.Arithmetic.rightCode a)) =
        chiCode (NativePublicBridge.contextCode s) (SourceChi.Arithmetic.rightCode a) := by
  have hi := sourceInput_low s a h
  have ho := LowArithmetic.omegaCode_spec s _ hi.1
  have hl := (sourceInput_literal s a).mp h
  exact chi_omegaPower _ _ (ThetaCourse.rawTree a) hl.2.2.1 hl.2.1 hl.2.2.2 ho.2.1
    (by simpa only [SourceChi.Arithmetic.rightCode, interpretation_code] using ho.2.2)

theorem source_lemma_3_5_a_logend (s a e : Nat) (h : sourceInput s a = true)
    (he : e ∈ LowArithmetic.operation 3 s (SourceChi.Arithmetic.rightCode a) 0) :
    chiCode (NativePublicBridge.contextCode s) e =
      chiCode (NativePublicBridge.contextCode s) (SourceChi.Arithmetic.rightCode a) := by
  have ho := LowArithmetic.operation_spec 3 s _ 0 e he
  have hl := (sourceInput_literal s a).mp h
  exact chi_logend _ e (ThetaCourse.rawTree a) hl.2.2.1 hl.2.1 hl.2.2.2 ho.2.2.1 (by
    simpa only [LowArithmetic.ResultSpec, SourceChi.Arithmetic.rightCode, interpretation_code] using ho.2.2.2.2)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi.Powers
