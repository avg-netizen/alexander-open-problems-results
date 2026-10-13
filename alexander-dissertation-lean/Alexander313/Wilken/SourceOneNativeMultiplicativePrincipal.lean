import Alexander313.Wilken.SourceOneNativeLocalizationRootAdapter
import Alexander313.Wilken.HereditaryAddition
import Alexander313.Wilken.HereditaryOmegaPowers
import Alexander313.Wilken.MultiplicativePrincipalArithmetic
import Alexander313.Wilken.SourceOneOmegaQuotientSupport

/-!
# Exact multiplicative-principal recognition in the original source-one grammar

The actual original check-zero normalizer, epsilon-offset parser and source
addition construct the corrected LOW exponent. Its zero case is retained:
the literal source-one base is multiplicative principal. On every other LOW
root the original exponent must be positive additive principal. Genuine HIGH
roots are epsilon. The full guard is original RAW LOW and multiplicative
principal, including one. No Native base-one checker, public logarithm,
representation or exponent oracle is used. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativePrincipal

open ThetaCourse MultiplicativePrincipalArithmetic

/-- The executing original source exponent retains the genuine epsilon
plus finite correction instead of assuming plain omega exponentiation. -/
def correctedCode (c : Nat) : Nat :=
  cond (EpsilonOffsets.aboveBaseCheck 0 (Nat.pair 0 c))
    (Addition.normalizedSumCode 0 c (OmegaPowers.finiteCode 1))
    (Theta.Normalization.normalizeCode 0 c)

theorem correctedCode_primrec : Primrec correctedCode := by
  have hp := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id
  have hg := EpsilonOffsets.aboveBaseCheck_primrec.comp (Primrec.const 0) hp
  have hs := Addition.normalizedSumCode_primrec.comp
    ((Primrec.const 0).pair (Primrec.id.pair (Primrec.const (OmegaPowers.finiteCode 1))))
  exact hg.cond hs
    (Theta.Normalization.Effective.normalizeCode_primrec.comp (Primrec.const 0) Primrec.id)

theorem correctedCode_spec (c : Nat) (hc : lowCheckCode 0 c = true) :
    Theta.acceptedLowCode 0 (correctedCode c) = true ∧
      interpretation 0 (correctedCode c) = lowOmegaExponent 1 (interpretation 0 c) := by
  have hq : unionCheck (Nat.pair 0 c) = true := by simpa only [unionCheck_pair] using hc
  have hoff : EpsilonOffsets.aboveBaseCheck 0 (Nat.pair 0 c) = true ↔
      EpsilonFiniteAbove 1 (interpretation 0 c) := by
    constructor
    · intro hf
      obtain ⟨_, ε, n, hε, hb, he⟩ := (EpsilonOffsets.aboveBaseCheck_exact 0 _).mp hf
      exact ⟨ε, n, by simpa only [finiteBase_zero] using hb, hε,
        by simpa only [unionInterpretation_pair] using he⟩
    · rintro ⟨ε, n, hb, hε, he⟩
      exact (EpsilonOffsets.aboveBaseCheck_exact 0 _).mpr
        ⟨hq, ε, n, hε, by simpa only [finiteBase_zero] using hb,
          by simpa only [unionInterpretation_pair] using he⟩
  cases hf : EpsilonOffsets.aboveBaseCheck 0 (Nat.pair 0 c) with
  | true =>
    have hs := Addition.normalizedSumCode_lowChecked 0 c (OmegaPowers.finiteCode 1)
      hc (OmegaPowers.finiteCode_checked 1)
    simp only [correctedCode, hf, Bool.cond_true]
    exact ⟨hs.1, by rw [hs.2, OmegaPowers.finiteCode_value, Nat.cast_one,
      lowOmegaExponent_of_offset _ _ (hoff.mp hf)]⟩
  | false =>
    have hn := Theta.Normalization.normalizeCode_acceptedLow 0 c hc
    have hnot : ¬ EpsilonFiniteAbove 1 (interpretation 0 c) := by
      intro he
      have hx : false = true := hf.symm.trans (hoff.mpr he)
      cases hx
    simp only [correctedCode, hf, Bool.cond_false]
    exact ⟨hn.1, by rw [hn.2, lowOmegaExponent_of_not_offset _ _ hnot,
      lowOmegaBase_one, zero_add]⟩

def nodeCheck (root : Nat) : Bool :=
  cond (SourceDecomposition.above 0 (rawTree (Localization.argumentCode root))) true
    (OmegaPowers.zeroCheck (Nat.pair 0 (correctedCode (Localization.argumentCode root))) ||
      SourceTrackingRaw.Support.principalCheck (correctedCode (Localization.argumentCode root)))

theorem nodeCheck_primrec : Primrec nodeCheck := by
  have ha := Localization.argumentCode_primrec
  have hh := SourceDecomposition.above_primrec.comp (Primrec.const 0) (rawTree_primrec.comp ha)
  have he := correctedCode_primrec.comp ha
  have hz := OmegaPowers.zeroCheck_primrec.comp (Primrec₂.natPair.comp (Primrec.const 0) he)
  exact hh.cond (Primrec.const true)
    (Primrec.or.comp hz (SourceTrackingRaw.Support.principalCheck_primrec.comp he))

/-- The original LOW exponent-zero boundary is tested explicitly; HIGH
uses the real original epsilon theorem. -/
theorem nodeCheck_exact (root : Nat) (hc : Localization.Node 0 root) :
    nodeCheck root = true ↔ IsMultiplicativePrincipal (interpretation 0 root) := by
  obtain ⟨a, rfl, ht, hn⟩ := hc
  have ha := SourceFixedPoint.checked_theta_argument 0 0 a ht
  have hpnode := OmegaQuotient.theta_principal 0 a ht
  simp only [nodeCheck, Localization.argumentCode_theta, rawTree_code, interpretation_code]
  cases hh : SourceDecomposition.above 0 a with
  | true =>
    have hhigh : 1 < a.outerSort := by
      simpa only [SourceDecomposition.above, Nat.zero_add, decide_eq_true_eq] using hh
    have he := (Epsilon.theta_epsilon_iff 0 0 a ht).mpr (Or.inl (by
      simpa only [Nat.zero_add] using hhigh))
    simp only [hh, Bool.cond_true]
    constructor
    · intro _
      apply (multiplicativePrincipal_iff _).mpr
      refine Or.inr ⟨denote 0 (.theta 0 a), ?_⟩
      calc
        denote 0 (.theta 0 a) = Ordinal.omega0 ^ denote 0 (.theta 0 a) := he.symm
        _ = Ordinal.omega0 ^ (Ordinal.omega0 ^ denote 0 (.theta 0 a)) :=
          congrArg (fun x : Ordinal.{0} => Ordinal.omega0 ^ x) he.symm
    · intro _
      rfl
  | false =>
    have hsort : a.outerSort ≤ 1 := by
      simpa only [SourceDecomposition.above, Nat.zero_add, decide_eq_false_iff_not, not_lt] using hh
    have hlo : lowCheckCode 0 a.code = true := by
      simpa only [lowCheckCode_code, lowCheck, ha, Bool.true_and, decide_eq_true_eq] using hsort
    have hs := correctedCode_spec a.code hlo
    have hl := (Theta.acceptedLowCode_iff 0 _).mp hs.1
    have hv : Ordinal.omega0 ^ interpretation 0 (correctedCode a.code) = denote 0 (.theta 0 a) := by
      rw [hs.2, interpretation_code]
      change Ordinal.omega0 ^ lowOmegaExponent 1 (denote 0 a) =
        globalCollapse (finiteBase 0) 0 (denote 0 a)
      rw [finiteBase_zero]
      exact (globalCollapse_low_eq_omegaPower 1 (Or.inl rfl) _ (by
        simpa only [finiteBase_zero] using
          (denote_lt_iff_outerSort_le 0 a ha 1 (by omega)).mpr hsort)).symm
    simp only [hh, Bool.cond_false, Bool.or_eq_true, OmegaPowers.zeroCheck_exact,
      unionCheck_pair, unionInterpretation_pair, SourceTrackingRaw.Support.principalCheck_exact]
    constructor
    · intro htest
      refine ⟨hpnode.1, hpnode.2, ?_⟩
      rw [← hv]
      apply (omegaPower_multiplicative_iff _).mpr
      rcases htest with ⟨_, hz⟩ | ⟨_, hp, hadd⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hp, hadd⟩
    · intro hm
      have hmul : Ordinal.IsPrincipal (· * ·)
          (Ordinal.omega0 ^ interpretation 0 (correctedCode a.code)) := by
        rw [hv]
        exact hm.2.2
      rcases (omegaPower_multiplicative_iff _).mp hmul with hz | ⟨hp, hadd⟩
      · exact Or.inl ⟨hl.1, hz⟩
      · exact Or.inr ⟨hl.1, hp, hadd⟩

def inputCheck (c : Nat) : Bool := SourceLocalization.RootAdapter.inputCheck c &&
  nodeCheck (SourceLocalization.RootAdapter.rootCode c)

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp SourceLocalization.RootAdapter.inputCheck_primrec
    (nodeCheck_primrec.comp SourceLocalization.RootAdapter.rootCode_primrec)

theorem inputCheck_exact (c : Nat) : inputCheck c = true ↔
    lowCheckCode 0 c = true ∧ 1 ≤ interpretation 0 c ∧
      IsMultiplicativePrincipal (interpretation 0 c) := by
  constructor
  · intro hi
    obtain ⟨hr, hm⟩ := Bool.and_eq_true.mp hi
    have hs := SourceLocalization.RootAdapter.rootCode_spec c hr
    have hc := (SourceLocalization.RootAdapter.inputCheck_exact c).mp hr
    have ht := (nodeCheck_exact _ hs.1).mp hm
    rw [hs.2] at ht
    exact ⟨hc.1, hc.2.1, ht⟩
  · rintro ⟨hl, hb, hm⟩
    have hr := (SourceLocalization.RootAdapter.inputCheck_exact c).mpr ⟨hl, hb, hm.2.1⟩
    have hs := SourceLocalization.RootAdapter.rootCode_spec c hr
    apply Bool.and_eq_true.mpr
    refine ⟨hr, (nodeCheck_exact _ hs.1).mpr ?_⟩
    rw [hs.2]
    exact hm

theorem rootAdapter_input (c : Nat) (hi : inputCheck c = true) :
    SourceLocalization.RootAdapter.inputCheck c = true := (Bool.and_eq_true.mp hi).1

theorem rootInput (c : Nat) (hi : inputCheck c = true) :
    Localization.inputCheck 0 (SourceLocalization.RootAdapter.rootCode c) = true :=
  SourceLocalization.RootAdapter.rootInput c (rootAdapter_input c hi)

theorem rootCode_value (c : Nat) (hi : inputCheck c = true) :
    interpretation 0 (SourceLocalization.RootAdapter.rootCode c) = interpretation 0 c :=
  SourceLocalization.RootAdapter.rootCode_value c (rootAdapter_input c hi)

theorem localization_endpoint_value (c : Nat) (hi : inputCheck c = true) :
    Localization.value 0 (Localization.endpoint
      (Localization.nativePath 0 (SourceLocalization.RootAdapter.rootCode c))) =
      interpretation 0 c :=
  SourceLocalization.RootAdapter.localization_endpoint_value c (rootAdapter_input c hi)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativePrincipal
