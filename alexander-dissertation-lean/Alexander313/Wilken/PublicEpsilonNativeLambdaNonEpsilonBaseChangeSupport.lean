import Alexander313.Wilken.PublicEpsilonNativeDirectZetaBaseChange
import Alexander313.Wilken.HereditaryNativeLambdaBranches

/-!
# Recognizing the original proper non-epsilon lambda domain

At every actual coded epsilon the admitted Normal theta-zero root is
proper exactly when its real argument is nonzero. On that proper domain,
the actual root is non-epsilon exactly when its argument has LOW outer
sort. The genuine Boolean tests are literal syntax tests, so the original
chosen-presentation Par cutoff derives both target properness and target
non-epsilon status along with target admission. No semantic branch guard
or target properness/non-epsilon oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.NonEpsilonBaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

def inputCheck (q c : Nat) : Bool := DirectZeta.inputCheck q c &&
  (!FixedPoint.zeroCheck (DirectZeta.argumentCode c) &&
    decide ((rawTree (DirectZeta.argumentCode c)).outerSort ≤ 1))

theorem inputCheck_primrec : Primrec₂ inputCheck := by
  have ha := DirectZeta.argumentCode_primrec.comp Primrec.snd
  have hz := Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp ha)
  have hs := (Primrec.nat_le.comp (outerSort_primrec.comp (rawTree_primrec.comp ha))
    (Primrec.const 1)).decide
  exact (Primrec.and.comp DirectZeta.inputCheck_primrec
    (Primrec.and.comp hz hs)).to₂

theorem proper_iff_nonzero_check (q c : Nat) (hc : DirectZeta.inputCheck q c = true) :
    base q < interpretation q c ↔ FixedPoint.zeroCheck (DirectZeta.argumentCode c) = false := by
  obtain ⟨a, he, ht, hn⟩ := (DirectZeta.inputCheck_exact q c).mp hc
  have hi := DirectZeta.argument_input q c hc
  have hp : base q < interpretation q c ↔ denote q a ≠ 0 := by
    simpa only [he, interpretation_code] using SourceChi.Arithmetic.proper_theta_zero_iff q a ht hn
  have hz : FixedPoint.zeroCheck (DirectZeta.argumentCode c) = true ↔ denote q a = 0 := by
    simpa only [DirectZeta.argumentCode, he, Localization.argumentCode_theta,
      interpretation_code] using FixedPoint.zeroCheck_exact q _ hi
  constructor
  · intro h
    cases hf : FixedPoint.zeroCheck (DirectZeta.argumentCode c) with
    | false => rfl
    | true => exact False.elim ((hp.mp h) (hz.mp hf))
  · intro h
    apply hp.mpr
    intro hv
    have hf := hz.mpr hv
    simp only [h, Bool.false_eq_true] at hf

/-- Properness excludes the actual epsilon-base exception. All remaining
epsilon roots have genuinely high arguments by the real collapse theorem. -/
theorem non_epsilon_iff_low_argument (q c : Nat)
    (hc : DirectZeta.inputCheck q c = true) (hp : base q < interpretation q c) :
    (Ordinal.omega0 ^ interpretation q c ≠ interpretation q c) ↔
      (rawTree (DirectZeta.argumentCode c)).outerSort ≤ 1 := by
  obtain ⟨a, he, ht, hn⟩ := (DirectZeta.inputCheck_exact q c).mp hc
  have ha := FixedPoint.checked_theta_argument q 0 a ht
  have hp' : base q < denote q (.theta 0 a) := by simpa only [he, interpretation_code] using hp
  have heps := OmegaPowers.theta_epsilon_iff q a ht
  simp only [DirectZeta.argumentCode, he, Localization.argumentCode_theta, rawTree_code,
    interpretation_code]
  constructor
  · intro hne
    apply le_of_not_gt
    intro hh
    have hhigh : omegaSequence (base q) 1 ≤ denote q a := by
      apply le_of_not_gt
      intro hl
      exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q a ha 1 (by omega)).mp hl)
    exact hne (heps.mpr (Or.inr hhigh))
  · intro hl hε
    rcases heps.mp hε with hz | hh
    · exact (ne_of_gt hp') hz
    · exact hh.not_gt ((denote_lt_iff_outerSort_le q a ha 1 (by omega)).mpr hl)

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    DirectZeta.inputCheck q c = true ∧ base q < interpretation q c ∧
      Ordinal.omega0 ^ interpretation q c ≠ interpretation q c := by
  constructor
  · intro h
    obtain ⟨hc, hb⟩ := Bool.and_eq_true.mp h
    obtain ⟨hz, hs⟩ := Bool.and_eq_true.mp hb
    have hp := (proper_iff_nonzero_check q c hc).mpr
      (by simpa only [Bool.not_eq_true'] using hz)
    exact ⟨hc, hp, (non_epsilon_iff_low_argument q c hc hp).mpr (of_decide_eq_true hs)⟩
  · rintro ⟨hc, hp, hε⟩
    exact Bool.and_eq_true.mpr ⟨hc, Bool.and_eq_true.mpr
      ⟨by simpa only [Bool.not_eq_true'] using (proper_iff_nonzero_check q c hc).mp hp,
        decide_eq_true ((non_epsilon_iff_low_argument q c hc hp).mp hε)⟩⟩

theorem inputCheck_context (q v c : Nat) (hcq : checkCode q c = true)
    (hcv : checkCode v c = true) : inputCheck q c = inputCheck v c := by
  simp only [inputCheck, DirectZeta.BaseChange.inputCheck_context q v c hcq hcv]

/-- Target properness and non-epsilon status are conclusions from the
original parameter cutoff and the actual unchanged syntax tests. -/
theorem target_input (q v c : Nat) (hc : inputCheck q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) : inputCheck v c = true := by
  have hd := (inputCheck_exact q c).mp hc
  have hvd := DirectZeta.BaseChange.target_input q v c hd.1 hv hp
  have hqc := ((Comparison.acceptedCode_exact q c).mp (Bool.and_eq_true.mp hd.1).1).1
  have hvc := ((Comparison.acceptedCode_exact v c).mp (Bool.and_eq_true.mp hvd).1).1
  rw [← inputCheck_context q v c hqc hvc]
  exact hc

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.NonEpsilonBaseChange
