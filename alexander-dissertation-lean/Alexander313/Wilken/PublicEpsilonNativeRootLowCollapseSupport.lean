import Alexander313.Wilken.PublicEpsilonNativePowerBaseChange
import Alexander313.Wilken.HereditaryNativeIotaCanonicalHeightSupport

/-!
# Genuine relative-root collapse on every original LOW argument

The original coded-epsilon context and its checked Normal high theta-zero
root supply the actual epsilon beta and the unchanged first cardinal.
The real epsilon-finite parser compares its head with that ORIGINAL root.
Native addition constructs the full corrected exponent, including every
epsilon-finite offset. No selected public-return endpoint, beta code,
collapse, admission or representation oracle is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLowCollapse

open ThetaCourse

abbrev Query := Nat × (Nat × Nat)

def rootCheck (q b : Nat) : Bool :=
  (Comparison.acceptedCode q b && Localization.rootShape b) &&
    decide (1 < (rawTree (Localization.argumentCode b)).outerSort)

theorem rootCheck_primrec : Primrec₂ rootCheck := by
  have hs := Localization.rootShape_primrec.comp Primrec.snd
  have hh := (Primrec.nat_lt.comp (Primrec.const 1)
    (outerSort_primrec.comp (rawTree_primrec.comp
      (Localization.argumentCode_primrec.comp Primrec.snd)))).decide
  exact (Primrec.and.comp
    (Primrec.and.comp Comparison.acceptedCode_primrec hs) hh).to₂

/-- Genuine original Normal high root, with no selected-return endpoint. -/
theorem rootCheck_exact (q b : Nat) : rootCheck q b = true ↔
    ∃ t : RelativeTerm Nat, b = (.theta 0 t).code ∧
      check q (.theta 0 t) = true ∧ Comparison.Normal q t ∧ 1 < t.outerSort := by
  constructor
  · intro h
    obtain ⟨hh, hs⟩ := Bool.and_eq_true.mp h
    obtain ⟨hac, hshape⟩ := Bool.and_eq_true.mp hh
    have hc := (Comparison.acceptedCode_exact q b).mp hac
    obtain ⟨v, he, ht⟩ := (checkCode_exact q b).mp hc.1
    obtain ⟨t, hvt⟩ := (Localization.rootShape_code v).mp
      (by simpa only [← he] using hshape)
    subst v
    refine ⟨t, he.symm, ht, ?_, ?_⟩
    · simpa only [← he, rawTree_code, Comparison.Normal] using hc.2
    · simpa only [← he, Localization.argumentCode_theta, rawTree_code] using
        of_decide_eq_true hs
  · rintro ⟨t, rfl, ht, hn, hh⟩
    have hac : Comparison.acceptedCode q (.theta 0 t : RelativeTerm Nat).code = true :=
      (Comparison.acceptedCode_exact _ _).mpr
        ⟨by simpa only [checkCode_code] using ht,
          by simpa only [rawTree_code, Comparison.Normal] using hn⟩
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hac,
      (Localization.rootShape_code _).mpr ⟨t, rfl⟩⟩,
        by simpa only [Localization.argumentCode_theta, rawTree_code] using decide_eq_true hh⟩

theorem root_original (q b : Nat) (ha : rootCheck q b = true) : checkCode q b = true := by
  obtain ⟨t, rfl, ht, hn, hh⟩ := (rootCheck_exact q b).mp ha
  simpa only [checkCode_code] using ht

theorem source_checked (q b : Nat) (ha : rootCheck q b = true) : baseCheck q = true :=
  (Bool.and_eq_true.mp (Arithmetic.raw_checked q b (root_original q b ha))).1

theorem root_low (q b : Nat) (ha : rootCheck q b = true) : lowCheckCode q b = true := by
  obtain ⟨t, rfl, ht, hn, hh⟩ := (rootCheck_exact q b).mp ha
  simp only [lowCheckCode_code, lowCheck, ht, RelativeTerm.outerSort, decide_true, Bool.true_and]

theorem root_accepted (q b : Nat) (ha : rootCheck q b = true) :
    Comparison.acceptedCode q b = true := (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1

theorem root_base_le (q b : Nat) (ha : rootCheck q b = true) : base q ≤ interpretation q b := by
  obtain ⟨t, rfl, ht, hn, hh⟩ := (rootCheck_exact q b).mp ha
  simpa only [interpretation_code] using BaseTransformation.theta_base_le q 0 t ht

theorem root_lt_first (q b : Nat) (ha : rootCheck q b = true) :
    interpretation q b < omegaSequence (base q) 1 :=
  (HeightBoundary.input_spec q b (root_low q b ha)).2.2

theorem root_epsilon (q b : Nat) (ha : rootCheck q b = true) :
    Ordinal.omega0 ^ interpretation q b = interpretation q b := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact q b).mp ha
  have hc := BaseTransformation.theta_argument_check q 0 t ht
  have hhigh : omegaSequence (base q) 1 ≤ denote q t := by
    apply le_of_not_gt
    intro hl
    exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q t hc 1 (by omega)).mp hl)
  simpa only [he, interpretation_code] using
    (OmegaPowers.theta_epsilon_iff q t ht).mpr (Or.inr hhigh)

theorem root_omega_one (q b : Nat) (ha : rootCheck q b = true) :
    omegaSequence (base q) 1 = omegaSequence (interpretation q b) 1 := by
  have hz := Iota.HeightSupport.levelCardinal_zero_eq_of_interval (base q)
    (interpretation q b) (root_base_le q b ha) (root_lt_first q b ha)
  exact congrArg Cardinal.ord (Iota.HeightSupport.levelCardinal_eq_of_zero_eq _ _ hz 1)

def inputCheck (q b c : Nat) : Bool := rootCheck q b && lowCheckCode q c

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (lowCheckCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem inputCheck_exact (q b c : Nat) : inputCheck q b c = true ↔
    rootCheck q b = true ∧ lowCheckCode q c = true := Bool.and_eq_true

def aboveOffset (q b c : Nat) : Bool := OmegaPowers.Offsets.check q c &&
  Normalization.lessRawCode q b (OmegaPowers.Offsets.headCode q c)

theorem aboveOffset_primrec : Primrec (fun p : Query => aboveOffset p.1 p.2.1 p.2.2) := by
  have ho := OmegaPowers.Offsets.check_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hh := OmegaPowers.Offsets.headCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hl := Normalization.Effective.lessRawCode_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hh))
  exact Primrec.and.comp ho hl

theorem aboveOffset_exact (q b c : Nat) (ha : rootCheck q b = true)
    (hc : lowCheckCode q c = true) :
    aboveOffset q b c = true ↔ EpsilonFiniteAbove (interpretation q b) (interpretation q c) := by
  have hb := root_original q b ha
  constructor
  · intro h
    obtain ⟨ho, hh⟩ := Bool.and_eq_true.mp h
    have hs := OmegaPowers.Offsets.decomposition_spec q c ho
    have he : interpretation q b < interpretation q (OmegaPowers.Offsets.headCode q c) :=
      ((Normalization.lessRawCode_exact q b (OmegaPowers.Offsets.headCode q c)).mp hh).2.2
    exact ⟨interpretation q (OmegaPowers.Offsets.headCode q c), OmegaPowers.Offsets.offset q c,
      he, hs.2.2.2.1, hs.2.2.2.2⟩
  · rintro ⟨ε, n, hεb, hε, hv⟩
    have ho := (OmegaPowers.Offsets.check_exact q c).mpr ⟨hc, ε, n, hε, hv⟩
    have hs := OmegaPowers.Offsets.decomposition_spec q c ho
    have he := (EpsilonOffsets.epsilon_offset_unique hs.2.2.2.1 hε
      (hs.2.2.2.2.symm.trans hv)).1
    refine Bool.and_eq_true.mpr ⟨ho, ?_⟩
    exact (Normalization.lessRawCode_exact q b (OmegaPowers.Offsets.headCode q c)).mpr
      ⟨hb, ((Comparison.acceptedCode_exact q _).mp hs.2.2.1).1, by rw [he]; exact hεb⟩

def exponentCode (q b c : Nat) : Nat := cond (aboveOffset q b c)
  (OmegaPowerHeight.finiteTailCode q c 1) (Arithmetic.addCode q b c)

theorem exponentCode_primrec : Primrec (fun p : Query => exponentCode p.1 p.2.1 p.2.2) := by
  have hs := OmegaPowerHeight.finiteTailCode_primrec.comp
    ((Primrec.fst.pair (Primrec.snd.comp Primrec.snd)).pair (Primrec.const 1))
  exact aboveOffset_primrec.cond hs Arithmetic.addCode_primrec

theorem exponentCode_spec (q b c : Nat) (ha : rootCheck q b = true)
    (hc : lowCheckCode q c = true) :
    lowCheckCode q (exponentCode q b c) = true ∧
      Comparison.acceptedCode q (exponentCode q b c) = true ∧
      interpretation q (exponentCode q b c) = lowOmegaExponent (interpretation q b) (interpretation q c) := by
  cases ho : aboveOffset q b c with
  | true =>
    have hs := OmegaPowerHeight.finiteTailCode_spec q c 1 hc
    refine ⟨by simpa only [exponentCode, ho, Bool.cond_true] using hs.1,
      by simpa only [exponentCode, ho, Bool.cond_true] using hs.2.1, ?_⟩
    simp only [exponentCode, ho, Bool.cond_true]
    rw [hs.2.2.1, lowOmegaExponent_of_offset _ _ ((aboveOffset_exact q b c ha hc).mp ho)]
    simp only [Nat.cast_one]
  | false =>
    have hs := Arithmetic.addCode_spec q b c (root_original q b ha) (Bool.and_eq_true.mp hc).1
    have hl := (OmegaPowerHeight.addCode_low_height q b c (root_low q b ha) hc).1
    have hn : ¬ EpsilonFiniteAbove (interpretation q b) (interpretation q c) := by
      intro h
      have ht := (aboveOffset_exact q b c ha hc).mpr h
      simp only [ho, Bool.false_eq_true] at ht
    refine ⟨by simpa only [exponentCode, ho, Bool.cond_false] using hl,
      by simpa only [exponentCode, ho, Bool.cond_false] using hs.1, ?_⟩
    simp only [exponentCode, ho, Bool.cond_false]
    rw [hs.2.1, lowOmegaExponent_of_not_offset _ _ hn,
      lowOmegaBase_of_epsilon _ (root_epsilon q b ha)]

def collapseCode (q b c : Nat) : Nat := cond (inputCheck q b c)
  (OmegaPowers.powerCode q (exponentCode q b c)) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2) :=
  inputCheck_primrec.cond (OmegaPowers.powerCode_primrec.comp Primrec.fst exponentCode_primrec)
    (Primrec.const 0)

/-- The actual beta-collapse value is returned as a checked Normal LOW
word at the ORIGINAL q, on EVERY original raw LOW argument. -/
theorem collapseCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    lowCheckCode q (collapseCode q b c) = true ∧
      Comparison.acceptedCode q (collapseCode q b c) = true ∧
      interpretation q (collapseCode q b c) =
        globalCollapse (interpretation q b) 0 (interpretation q c) := by
  have hs := (inputCheck_exact q b c).mp hi
  have he := exponentCode_spec q b c hs.1 hs.2
  have hp := OmegaPowers.powerCode_spec q (exponentCode q b c) he.1
  have hl : interpretation q c < omegaSequence (interpretation q b) 1 := by
    rw [← root_omega_one q b hs.1]
    exact (HeightBoundary.input_spec q c hs.2).2.2
  simp only [collapseCode, hi, Bool.cond_true]
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [hp.2.2, he.2.2]
  exact (globalCollapse_low_eq_omegaPower (interpretation q b)
    (Or.inr (root_epsilon q b hs.1)) _ hl).symm

theorem collapseCode_rejected (q b c : Nat) (hi : inputCheck q b c = false) :
    collapseCode q b c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootLowCollapse
