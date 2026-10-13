import Alexander313.Wilken.HereditaryNativeOmegaPowerHeightSupport
import Alexander313.Wilken.HereditaryNativeSourceChiPowers
import Alexander313.Wilken.HereditaryOmegaPowers

/-!
# Direct native omega-power callers at every coded epsilon

Below the actual native base, an admitted source tree can contain only
parameter and sum constructors. A literal finite fold aggregates its original
public payloads by genuine public addition; it is not a general translation.
The existing public power of this value remains an admitted atomic payload by
actual epsilon closure. Above the base the native source arithmetic and real
low theta calls provide the remaining branches. No caller, arithmetic formula,
code/value, epsilon or representation oracle is supplied. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers

open ThetaCourse
open Alexander313.HereditaryOrdinalLabels (zeroCode zeroCode_checked zeroCode_value)

def publicParameters (t : RelativeTerm Nat) : Nat :=
  ValueFold.term (fun (_ : Unit) p => p) CanonicalArithmetic.canonicalSum
    (fun (_ : Unit) (_ : Nat) (_ : Nat) => zeroCode) () t

theorem publicParameters_primrec : Primrec publicParameters :=
  (ValueFold.term_primrec (fun (_ : Unit) p => p) CanonicalArithmetic.canonicalSum
    (fun (_ : Unit) (_ : Nat) (_ : Nat) => zeroCode) zeroCode Primrec.snd.to₂
    CanonicalArithmetic.canonicalSum_primrec (Primrec.const zeroCode)).comp (Primrec.const ()) Primrec.id

@[simp] theorem publicParameters_parameter (p : Nat) : publicParameters (.parameter p) = p := rfl
@[simp] theorem publicParameters_sum (a b : RelativeTerm Nat) :
    publicParameters (.sum a b) = CanonicalArithmetic.canonicalSum (publicParameters a) (publicParameters b) := rfl

/-- Admission and actual value below the base force the entire aggregation
fold to remain on original public payloads; all theta cases are impossible. -/
theorem publicParameters_spec (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (hb : denote q t < base q) :
    unionCheck (publicParameters t) = true ∧ unionInterpretation (publicParameters t) = denote q t := by
  revert ht hb
  induction t with
  | parameter p =>
    intro ht hb
    exact ⟨((parameterCheck_exact q p).mp (checked_admissible q _ ht).1).1, rfl⟩
  | sum a b iha ihb =>
    intro ht hb
    have hq := (Bool.and_eq_true.mp ht).1
    have had := checked_admissible q (.sum a b) ht
    cases had.2 with
    | sum haa hbb =>
      have ha := Comparison.admitted_checked q _ hq a ⟨had.1.1, haa⟩
      have hd := Comparison.admitted_checked q _ hq b ⟨had.1.2, hbb⟩
      change denote q a + denote q b < base q at hb
      have hpa := iha ha (le_self_add.trans_lt hb)
      have hpb := ihb hd (le_add_self.trans_lt hb)
      exact ⟨CanonicalArithmetic.canonicalSum_original _ _ hpa.1 hpb.1,
        (CanonicalArithmetic.canonicalSum_value _ _ hpa.1 hpb.1).trans (by rw [hpa.2, hpb.2]; rfl)⟩
  | theta k a ih =>
    intro ht hb
    have hbase : base q ≤ denote q (.theta k a) :=
      (show base q ≤ omegaSequence (base q) k by
        simpa only [omegaSequence_zero] using (omegaSequence_strictMono (base q)).monotone (Nat.zero_le k)).trans
        (FixedPoint.checked_theta_range q k a ht).1
    exact False.elim ((not_lt_of_ge hbase) hb)

/-- Original checked input plus the actual cardinal bound recovers the
original LOW parser, including its real theta-sort restriction. -/
theorem low_of_bound (q c : Nat) (hc : checkCode q c = true)
    (hb : interpretation q c < omegaSequence (base q) 1) : lowCheckCode q c = true := by
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hc
  have hs : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le q t ht 1 (by omega)).mp (by
    simpa only [← he, interpretation_code] using hb)
  rw [← he, lowCheckCode_code]
  exact Bool.and_eq_true.mpr ⟨ht, decide_eq_true_eq.mpr hs⟩

def parameterCode (p : Nat) : Nat := (.parameter p : RelativeTerm Nat).code

theorem parameterCode_primrec : Primrec parameterCode := code_primrec.comp parameter_primrec

theorem parameterCode_spec (q p : Nat) (hp : parameterCheck q p = true) (hq : baseCheck q = true) :
    lowCheckCode q (parameterCode p) = true ∧ Comparison.acceptedCode q (parameterCode p) = true ∧
      interpretation q (parameterCode p) = unionInterpretation p := by
  have had : admissible q 0 (.parameter p) :=
    ⟨hp, .parameter (by simpa only [omegaSequence_zero] using parameter_sound q p hp)⟩
  have ht := Comparison.admitted_checked q 0 hq _ had
  have hc : checkCode q (parameterCode p) = true := by simpa only [parameterCode, checkCode_code] using ht
  refine ⟨?_, (Comparison.acceptedCode_exact q _).mpr ⟨hc, by simp only [parameterCode, rawTree_code, Comparison.Normal]⟩, rfl⟩
  simp only [parameterCode, lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort,
    Nat.zero_le, decide_true, Bool.true_and]

def belowPowerCode (q c : Nat) : Nat :=
  parameterCode (Hereditary.OmegaPowers.powerCode (publicParameters (rawTree c)))

theorem belowPowerCode_primrec : Primrec₂ belowPowerCode :=
  ((parameterCode_primrec.comp (Hereditary.OmegaPowers.powerCode_primrec.comp
    (publicParameters_primrec.comp (rawTree_primrec.comp Primrec.snd))))).to₂

theorem belowPowerCode_spec (q c : Nat) (hc : checkCode q c = true)
    (hb : interpretation q c < base q) :
    lowCheckCode q (belowPowerCode q c) = true ∧ Comparison.acceptedCode q (belowPowerCode q c) = true ∧
      interpretation q (belowPowerCode q c) = Ordinal.omega0 ^ interpretation q c := by
  have hq := (HeightBoundary.input_spec q c (low_of_bound q c hc
    (hb.trans (by simpa only [omegaSequence_zero] using omegaSequence_step (base q) 0)))).2.1
  have hs := publicParameters_spec q (rawTree c) (Arithmetic.raw_checked q c hc) (by
    simpa only [Arithmetic.raw_value q c hc] using hb)
  have hp := Hereditary.OmegaPowers.powerCode_checked _ hs.1
  have hv := Hereditary.OmegaPowers.powerCode_value _ hs.1
  have hv' : unionInterpretation (Hereditary.OmegaPowers.powerCode (publicParameters (rawTree c))) =
      Ordinal.omega0 ^ interpretation q c := by
    simpa only [hs.2, Arithmetic.raw_value q c hc] using hv
  have hbound : unionInterpretation (Hereditary.OmegaPowers.powerCode (publicParameters (rawTree c))) < base q := by
    rw [hv']
    exact (omegaPower_strictMono hb).trans_eq (SourceChi.epsilon_base q hq)
  have hparam := (parameterCheck_exact q _).mpr ⟨Canonical.check_original hp,
    ((baseCheck_exact q).mp hq).1, hbound⟩
  have h := parameterCode_spec q _ hparam hq
  exact ⟨h.1, h.2.1, h.2.2.trans hv'⟩

def thetaCode (c : Nat) : Nat := (.theta 0 (rawTree c) : RelativeTerm Nat).code

theorem thetaCode_primrec : Primrec thetaCode :=
  code_primrec.comp (theta_primrec.comp (Primrec.const 0) rawTree_primrec)

theorem thetaCode_spec (q c : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.acceptedCode q c = true) :
    lowCheckCode q (thetaCode c) = true ∧ Comparison.acceptedCode q (thetaCode c) = true ∧
      interpretation q (thetaCode c) = globalCollapse (base q) 0 (interpretation q c) := by
  have hi := HeightBoundary.input_spec q c hc
  have ht := SourceChi.Powers.checked_theta_zero q (rawTree c) (Arithmetic.raw_checked q c hi.1) (by
    rw [Arithmetic.raw_value q c hi.1]
    exact hi.2.2.trans (omegaSequence_step (base q) 1))
  have hcn : checkCode q (thetaCode c) = true := by simpa only [thetaCode, checkCode_code] using ht
  have hnn : Comparison.Normal q (rawTree (thetaCode c)) := by
    simpa only [thetaCode, rawTree_code, Comparison.Normal] using ((Comparison.acceptedCode_exact q c).mp hn).2
  refine ⟨?_, (Comparison.acceptedCode_exact q _).mpr ⟨hcn, hnn⟩, ?_⟩
  · simp only [thetaCode, lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort,
      Nat.zero_add, le_refl, decide_true, Bool.true_and]
  · change globalCollapse (base q) 0 (denote q (rawTree c)) = _
    rw [Arithmetic.raw_value q c hi.1]

/-- The genuine finite high-collapse epsilon criterion gives an exact native
atom test: a theta-zero value is epsilon precisely at the base or on a high
original argument. No epsilon decision is supplied. -/
theorem theta_epsilon_iff (q : Nat) (a : RelativeTerm Nat) (ht : check q (.theta 0 a) = true) :
    Ordinal.omega0 ^ denote q (.theta 0 a) = denote q (.theta 0 a) ↔
      denote q (.theta 0 a) = base q ∨ omegaSequence (base q) 1 ≤ denote q a := by
  have hq := (Bool.and_eq_true.mp ht).1
  constructor
  · intro he
    by_cases hh : omegaSequence (base q) 1 ≤ denote q a
    · exact Or.inr hh
    · have hl : denote q a < omegaSequence (base q) 1 := lt_of_not_ge hh
      let n := SourceOne.PublicCodes.fragment (.theta 0 a)
      have had := checked_admissible q (.theta 0 a) ht
      have hvalue := denote_eq_finite q n hq (.theta 0 a) had.2
      cases had.2 with
      | theta h0 hn hs haa =>
        have hlow : finiteDenote q n a < omegaSequence (base q) 1 := by
          rw [← denote_eq_finite q n hq a haa]
          exact hl
        have he' : Ordinal.omega0 ^ sourceFiniteCollapse (base q) n 0 (finiteDenote q n a) =
            sourceFiniteCollapse (base q) n 0 (finiteDenote q n a) := by
          simpa only [hvalue, finiteDenote, RelativeTerm.eval] using he
        have hb := sourceFiniteCollapse_low_epsilon_eq_base (base q) n 0 hn _ hlow he'
        exact Or.inl (hvalue.trans (by simpa only [finiteDenote, RelativeTerm.eval, omegaSequence_zero] using hb))
  · rintro (hb | hh)
    · rw [hb]
      exact SourceChi.epsilon_base q hq
    · exact SourceChi.Powers.theta_epsilon_of_high q a ht hh

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers
