import Alexander313.Wilken.HereditaryNativeOmegaPowers
import Alexander313.Wilken.HereditaryNativeLogEndZero

/-!
# Genuine native last-atom and corrected-exponent callers

The original normalized principal word supplies its positive final atom.
Its original admission, LOW bound and shape are derived from that word.
The actual epsilon-finite parser distinguishes precisely the exceptional
strictly-above-base case in the literal low-collapse exponent. Native
addition constructs both corrected branches, with their actual LOW Normal
outputs. No logarithm, caller, epsilon-offset or normalization oracle is
supplied. Source-only, uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd.Support

open ThetaCourse

def aboveOffset (q c : Nat) : Bool := OmegaPowers.Offsets.check q c && OmegaPowers.headAbove q c

theorem aboveOffset_primrec : Primrec₂ aboveOffset :=
  (Primrec.and.comp OmegaPowers.Offsets.check_primrec OmegaPowers.headAbove_primrec).to₂

theorem aboveOffset_exact (q c : Nat) (hc : lowCheckCode q c = true) :
    aboveOffset q c = true ↔ EpsilonFiniteAbove (base q) (interpretation q c) := by
  have hq := (HeightBoundary.input_spec q c hc).2.1
  have hb := OmegaPowers.Offsets.baseCode_spec q hq
  constructor
  · intro h
    obtain ⟨ho, hh⟩ := Bool.and_eq_true.mp h
    have hs := OmegaPowers.Offsets.decomposition_spec q c ho
    have he : base q < interpretation q (OmegaPowers.Offsets.headCode q c) := by
      simpa only [OmegaPowers.headAbove, ((Comparison.acceptedCode_exact q _).mp hb.1).1,
        ((Comparison.acceptedCode_exact q _).mp hs.2.2.1).1, hb.2, true_and] using
        (Normalization.lessRawCode_exact q OmegaPowers.Offsets.baseCode
          (OmegaPowers.Offsets.headCode q c)).mp hh
    exact ⟨interpretation q (OmegaPowers.Offsets.headCode q c), OmegaPowers.Offsets.offset q c,
      he, hs.2.2.2.1, hs.2.2.2.2⟩
  · rintro ⟨ε, n, hεb, hε, hv⟩
    have ho := (OmegaPowers.Offsets.check_exact q c).mpr ⟨hc, ε, n, hε, hv⟩
    have hs := OmegaPowers.Offsets.decomposition_spec q c ho
    have he := (EpsilonOffsets.epsilon_offset_unique hs.2.2.2.1 hε
      (hs.2.2.2.2.symm.trans hv)).1
    refine Bool.and_eq_true.mpr ⟨ho, ?_⟩
    apply (Normalization.lessRawCode_exact q OmegaPowers.Offsets.baseCode
      (OmegaPowers.Offsets.headCode q c)).mpr
    exact ⟨((Comparison.acceptedCode_exact q _).mp hb.1).1,
      ((Comparison.acceptedCode_exact q _).mp hs.2.2.1).1, by rw [hb.2, he]; exact hεb⟩

def correctedCode (q c : Nat) : Nat := cond (aboveOffset q c)
  (OmegaPowerHeight.finiteTailCode q c 1)
  (Arithmetic.addCode q OmegaPowers.Offsets.baseCode c)

theorem correctedCode_primrec : Primrec₂ correctedCode := by
  have hs := OmegaPowerHeight.finiteTailCode_primrec.comp
    ((Primrec.fst.pair Primrec.snd).pair (Primrec.const 1))
  have hb := Arithmetic.addCode_primrec.comp
    (Primrec.fst.pair ((Primrec.const OmegaPowers.Offsets.baseCode).pair Primrec.snd))
  exact (aboveOffset_primrec.cond hs hb).to₂

/-- The literal corrected low-collapse exponent is constructed at the
same actual coded epsilon on every original raw LOW argument. -/
theorem correctedCode_spec (q c : Nat) (hc : lowCheckCode q c = true) :
    lowCheckCode q (correctedCode q c) = true ∧
      Comparison.acceptedCode q (correctedCode q c) = true ∧
      interpretation q (correctedCode q c) = lowOmegaExponent (base q) (interpretation q c) := by
  have hi := HeightBoundary.input_spec q c hc
  cases ho : aboveOffset q c with
  | true =>
    have hs := OmegaPowerHeight.finiteTailCode_spec q c 1 hc
    refine ⟨by simpa only [correctedCode, ho, Bool.cond_true] using hs.1,
      by simpa only [correctedCode, ho, Bool.cond_true] using hs.2.1, ?_⟩
    simp only [correctedCode, ho, Bool.cond_true]
    rw [hs.2.2.1, lowOmegaExponent_of_offset _ _ ((aboveOffset_exact q c hc).mp ho)]
    simp only [Nat.cast_one]
  | false =>
    have hb := OmegaPowers.Offsets.baseCode_spec q hi.2.1
    have hbl := OmegaPowers.low_of_bound q OmegaPowers.Offsets.baseCode
      ((Comparison.acceptedCode_exact q _).mp hb.1).1 (by
        rw [hb.2]
        simpa only [omegaSequence_zero] using omegaSequence_step (base q) 0)
    have hs := Arithmetic.addCode_spec q OmegaPowers.Offsets.baseCode c
      ((Comparison.acceptedCode_exact q _).mp hb.1).1 hi.1
    have hl := (OmegaPowerHeight.addCode_low_height q OmegaPowers.Offsets.baseCode c hbl hc).1
    have hn : ¬ EpsilonFiniteAbove (base q) (interpretation q c) := by
      intro h
      have ht := (aboveOffset_exact q c hc).mpr h
      simp only [ho, Bool.false_eq_true] at ht
    refine ⟨by simpa only [correctedCode, ho, Bool.cond_false] using hl,
      by simpa only [correctedCode, ho, Bool.cond_false] using hs.1, ?_⟩
    simp only [correctedCode, ho, Bool.cond_false]
    rw [hs.2.1, hb.2, lowOmegaExponent_of_not_offset _ _ hn,
      lowOmegaBase_of_epsilon _ (SourceChi.epsilon_base q hi.2.1)]

theorem endAtom_mem (q c : Nat) (hc : Decomposition.inputCheck q c = true)
    (hz : interpretation q c ≠ 0) : LogEndZero.endAtom c ∈ Decomposition.word c := by
  have hn : Decomposition.word c ≠ [] := by
    intro hw
    exact hz ((FixedPoint.zeroCheck_exact q c hc).mp (by
      simp only [FixedPoint.zeroCheck, hw, List.length_nil, beq_self_eq_true]))
  cases hr : (Decomposition.word c).reverse with
  | nil =>
    have hw : Decomposition.word c = [] := by
      have he := congrArg List.reverse hr
      simpa only [List.reverse_reverse, List.reverse_nil] using he
    exact False.elim (hn hw)
  | cons a as =>
    have ha : a ∈ (Decomposition.word c).reverse := by rw [hr]; exact List.mem_cons_self
    have hm : a ∈ Decomposition.word c := by simpa only [List.mem_reverse] using ha
    simpa only [LogEndZero.endAtom, hr, List.getElem?_cons_zero, Option.getD_some] using hm

/-- Every nonzero original LOW Normal word supplies its genuine final
positive principal atom, including all original admission and LOW guards. -/
theorem endCode_spec (q c : Nat) (hc : lowCheckCode q c = true)
    (hn : Decomposition.inputCheck q c = true) (hz : interpretation q c ≠ 0) :
    lowCheckCode q (LogEndZero.endCode c) = true ∧
      Comparison.acceptedCode q (LogEndZero.endCode c) = true ∧
      0 < interpretation q (LogEndZero.endCode c) ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q (LogEndZero.endCode c)) ∧
      interpretation q (LogEndZero.endCode c) ≤ interpretation q c ∧
      ((∃ p, rawTree (LogEndZero.endCode c) = .parameter p) ∨
        ∃ k a, rawTree (LogEndZero.endCode c) = .theta k a) := by
  have hm := endAtom_mem q c hn hz
  have hs := (Decomposition.word_spec q c hn).1 _ hm
  have hv : denote q (LogEndZero.endAtom c) ∈ canonicalANF (interpretation q c) := by
    rw [← (Decomposition.word_spec q c hn).2]
    exact List.mem_map.mpr ⟨_, hm, rfl⟩
  have hb := canonicalANF_mem_le hv
  have he := LogEndZero.endCode_accepted q c hn
  refine ⟨OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp he).1 ?_,
    he, ?_, ?_, ?_, ?_⟩
  · simpa only [LogEndZero.endCode, interpretation_code] using
      hb.trans_lt (HeightBoundary.input_spec q c hc).2.2
  · simpa only [LogEndZero.endCode, interpretation_code] using hs.2.2.1
  · simpa only [LogEndZero.endCode, interpretation_code] using hs.2.2.2
  · simpa only [LogEndZero.endCode, interpretation_code] using hb
  · simpa only [LogEndZero.endCode, rawTree_code, Decomposition.word] using
      Comparison.atoms_shape (rawTree c) (LogEndZero.endAtom c) hm

theorem theta_low_index (q k : Nat) (a : RelativeTerm Nat)
    (hc : lowCheckCode q (.theta k a).code = true) : k = 0 := by
  have hi := HeightBoundary.input_spec q _ hc
  have ht : check q (.theta k a) = true := by
    simpa only [checkCode_code] using hi.1
  have hs : k + 1 ≤ 1 := by
    have h := (denote_lt_iff_outerSort_le q (.theta k a) ht 1 (by omega)).mp (by
      simpa only [interpretation_code] using hi.2.2)
    simpa only [RelativeTerm.outerSort] using h
  omega

theorem theta_argument_low (q : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta 0 a) = true) (hh : Decomposition.above 0 a = false) :
    lowCheckCode q a.code = true := by
  have ha := FixedPoint.checked_theta_argument q 0 a ht
  apply OmegaPowers.low_of_bound q a.code (by simpa only [checkCode_code] using ha)
  rw [interpretation_code]
  apply lt_of_not_ge
  intro hb
  have h := (Decomposition.above_exact q 0 a ha).mpr (by simpa only [Nat.zero_add] using hb)
  simp only [hh, Bool.false_eq_true] at h

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEnd.Support
