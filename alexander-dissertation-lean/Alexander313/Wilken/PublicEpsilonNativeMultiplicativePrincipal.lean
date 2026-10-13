import Alexander313.Wilken.PublicEpsilonNativeLocalizationRootAdapter
import Alexander313.Wilken.HereditaryNativeLogEndSupport
import Alexander313.Wilken.MultiplicativePrincipalArithmetic

/-!
# Actual multiplicative-principal recognition above a coded epsilon base

The original raw LOW input first supplies a genuine Normal theta-zero root
of the SAME value through the actual normalizer and final-atom parser.
The high-argument branch is genuinely epsilon. The LOW-argument branch
constructs its literal corrected omega exponent at the SAME native base;
that exponent is positive and is additive principal exactly when the
original root is multiplicative principal. Every operation is primitive
recursive. No public logarithm search, representation, exponent or caller
oracle is supplied. The exact original domain is RAW LOW at least as large
as the admitted epsilon base, including the base itself. Below-base
recognition and additive-principal tracking assignment are separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativePrincipal

open ThetaCourse MultiplicativePrincipalArithmetic

def nodeCheck (q root : Nat) : Bool :=
  cond (Decomposition.above 0 (rawTree (SourceLocalization.argumentCode root))) true
    (SourceTrackingSequences.Support.principalCheck q
      (LogEnd.Support.correctedCode q (SourceLocalization.argumentCode root)))

theorem nodeCheck_primrec : Primrec₂ nodeCheck := by
  have ha := SourceLocalization.argumentCode_primrec.comp Primrec.snd
  have hh := Decomposition.above_primrec.comp (Primrec.const 0) (rawTree_primrec.comp ha)
  have he := LogEnd.Support.correctedCode_primrec.comp Primrec.fst ha
  exact (hh.cond (Primrec.const true)
    (SourceTrackingSequences.Support.principalCheck_primrec.comp Primrec.fst he)).to₂

/-- Genuine epsilon fixedness implies the full source multiplicative
class, which retains positivity and both closure predicates. -/
theorem epsilon_multiplicative (v : Ordinal.{0}) (he : Ordinal.omega0 ^ v = v) :
    IsMultiplicativePrincipal v := by
  apply (multiplicativePrincipal_iff v).mpr
  refine Or.inr ⟨v, ?_⟩
  calc
    v = Ordinal.omega0 ^ v := he.symm
    _ = Ordinal.omega0 ^ (Ordinal.omega0 ^ v) :=
      congrArg (fun x : Ordinal.{0} => Ordinal.omega0 ^ x) he.symm

/-- Every genuine original Node derives both the corrected-exponent
caller and its positivity. HIGH needs no exponent computation premise. -/
theorem nodeCheck_exact (q root : Nat) (hc : SourceLocalization.Node q root) :
    nodeCheck q root = true ↔ IsMultiplicativePrincipal (interpretation q root) := by
  obtain ⟨a, rfl, ht, hn⟩ := hc
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := FixedPoint.checked_theta_argument q 0 a ht
  simp only [nodeCheck, SourceLocalization.argumentCode_theta, rawTree_code,
    interpretation_code]
  cases hh : Decomposition.above 0 a with
  | true =>
    have he := SourceChi.Powers.theta_epsilon_of_high q a ht
      (by simpa only [Nat.zero_add] using (Decomposition.above_exact q 0 a ha).mp hh)
    simp only [hh, Bool.cond_true]
    constructor
    · intro _
      exact epsilon_multiplicative _ he
    · intro _
      rfl
  | false =>
    have hlo := LogEnd.Support.theta_argument_low q a ht hh
    have hs := LogEnd.Support.correctedCode_spec q a.code hlo
    have hb : base q ≤ interpretation q (LogEnd.Support.correctedCode q a.code) := by
      rw [hs.2.2]
      calc
        base q = lowOmegaBase (base q) :=
          (lowOmegaBase_of_epsilon (base q) (SourceChi.epsilon_base q hq)).symm
        _ ≤ lowOmegaBase (base q) + interpretation q a.code := le_self_add
        _ ≤ lowOmegaExponent (base q) (interpretation q a.code) :=
          lowOmegaExponent_shift_le _ _
    have hp := (base_pos q hq).trans_le hb
    have hv : Ordinal.omega0 ^ interpretation q (LogEnd.Support.correctedCode q a.code) =
        denote q (.theta 0 a) := by
      rw [hs.2.2, interpretation_code]
      exact (globalCollapse_low_eq_omegaPower (base q)
        (Or.inr (SourceChi.epsilon_base q hq)) _
        (by simpa only [interpretation_code] using (HeightBoundary.input_spec q _ hlo).2.2)).symm
    have hprincipal := SourceChi.Powers.theta_principal q a ht
    simp only [hh, Bool.cond_false, SourceTrackingSequences.Support.principalCheck_exact]
    constructor
    · rintro ⟨_, hpos, hadd⟩
      refine ⟨hprincipal.1, hprincipal.2, ?_⟩
      rw [← hv]
      exact (omegaPower_multiplicative_iff _).mpr (Or.inr ⟨hpos, hadd⟩)
    · intro hm
      have hmexp : Ordinal.IsPrincipal (· * ·)
          (Ordinal.omega0 ^ interpretation q (LogEnd.Support.correctedCode q a.code)) := by
        rw [hv]
        exact hm.2.2
      rcases (omegaPower_multiplicative_iff _).mp hmexp with hz | ⟨_, hadd⟩
      · exact False.elim ((ne_of_gt hp) hz)
      · exact ⟨hs.1, hp, hadd⟩

def inputCheck (q c : Nat) : Bool := SourceLocalization.RootAdapter.inputCheck q c &&
  nodeCheck q (SourceLocalization.RootAdapter.rootCode q c)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp SourceLocalization.RootAdapter.inputCheck_primrec
    (nodeCheck_primrec.comp Primrec.fst SourceLocalization.RootAdapter.rootCode_primrec)).to₂

/-- Exact original RAW LOW multiplicative-principal domain of the
relative assignment in Definition3.19, with the base included. -/
theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    lowCheckCode q c = true ∧ base q ≤ interpretation q c ∧
      IsMultiplicativePrincipal (interpretation q c) := by
  constructor
  · intro hi
    obtain ⟨hr, hm⟩ := Bool.and_eq_true.mp hi
    have hs := SourceLocalization.RootAdapter.rootCode_spec q c hr
    have hc := (SourceLocalization.RootAdapter.inputCheck_exact q c).mp hr
    have ht := (nodeCheck_exact q _ hs.1).mp hm
    rw [hs.2] at ht
    exact ⟨hc.1, hc.2.1, ht⟩
  · rintro ⟨hl, hb, hm⟩
    have hr := (SourceLocalization.RootAdapter.inputCheck_exact q c).mpr ⟨hl, hb, hm.2.1⟩
    have hs := SourceLocalization.RootAdapter.rootCode_spec q c hr
    apply Bool.and_eq_true.mpr
    refine ⟨hr, (nodeCheck_exact q _ hs.1).mpr ?_⟩
    rw [hs.2]
    exact hm

theorem rootAdapter_input (q c : Nat) (hi : inputCheck q c = true) :
    SourceLocalization.RootAdapter.inputCheck q c = true := (Bool.and_eq_true.mp hi).1

/-- Actual source localization admission follows from the computed
multiplicative check, without a root-shape or Normal premise. -/
theorem rootInput (q c : Nat) (hi : inputCheck q c = true) :
    SourceLocalization.inputCheck q (SourceLocalization.RootAdapter.rootCode q c) = true :=
  SourceLocalization.RootAdapter.rootInput q c (rootAdapter_input q c hi)

theorem rootCode_value (q c : Nat) (hi : inputCheck q c = true) :
    interpretation q (SourceLocalization.RootAdapter.rootCode q c) = interpretation q c :=
  (SourceLocalization.RootAdapter.rootCode_spec q c (rootAdapter_input q c hi)).2

/-- The actual finite localization retains the ORIGINAL raw input value
at its endpoint; literal root spelling is not part of this statement. -/
theorem localization_endpoint_value (q c : Nat) (hi : inputCheck q c = true) :
    SourceLocalization.value q (SourceLocalization.endpoint
      (SourceLocalization.nativePath q (SourceLocalization.RootAdapter.rootCode q c))) =
      interpretation q c :=
  SourceLocalization.RootAdapter.localization_endpoint_value q c (rootAdapter_input q c hi)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativePrincipal
