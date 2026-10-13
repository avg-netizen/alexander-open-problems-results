import Alexander313.Wilken.PublicEpsilonNativeUnboundedLambdaSourceBaseChange
import Alexander313.Wilken.PublicEpsilonNativeLambdaNonEpsilonBaseChange

/-!
# Exhaustive original proper-root lambda branches at every coded epsilon

The original Normal theta-zero caller is proper exactly when its actual
argument zero test is false. The real collapse epsilon theorem, including
the complete LOW epsilon-finite correction, says a proper root is epsilon
exactly when its argument has high outer sort. The epsilon-base exception
is excluded by the actual properness guard. Both executing branch callers
and their target contexts are derived; no semantic branch flag is supplied.
Source-only, uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceBranches

open ThetaCourse
open BaseTransformation (ParBounded)

def inputCheck (q root : Nat) : Bool := DirectZeta.inputCheck q root &&
  !FixedPoint.zeroCheck (DirectZeta.argumentCode root)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp DirectZeta.inputCheck_primrec
    (Primrec.not.comp (FixedPoint.zeroCheck_primrec.comp
      (DirectZeta.argumentCode_primrec.comp Primrec.snd)))).to₂

theorem inputCheck_exact (q root : Nat) : inputCheck q root = true ↔
    DirectZeta.inputCheck q root = true ∧ base q < interpretation q root := by
  constructor
  · intro ha
    obtain ⟨hd, hz⟩ := Bool.and_eq_true.mp ha
    exact ⟨hd, (NonEpsilonBaseChange.proper_iff_nonzero_check q root hd).mpr
      (by simpa only [Bool.not_eq_true'] using hz)⟩
  · rintro ⟨hd, hp⟩
    exact Bool.and_eq_true.mpr ⟨hd, by simpa only [Bool.not_eq_true'] using
      (NonEpsilonBaseChange.proper_iff_nonzero_check q root hd).mp hp⟩

theorem inputCheck_literal (q root : Nat) : inputCheck q root = true ↔
    ∃ t : RelativeTerm Nat, root = (.theta 0 t).code ∧ check q (.theta 0 t) = true ∧
      Comparison.Normal q (.theta 0 t) ∧ base q < denote q (.theta 0 t) := by
  constructor
  · intro ha
    have hs := (inputCheck_exact q root).mp ha
    obtain ⟨t, he, ht, hn⟩ := (DirectZeta.inputCheck_exact q root).mp hs.1
    exact ⟨t, he, ht, hn, by simpa only [he, interpretation_code] using hs.2⟩
  · rintro ⟨t, he, ht, hn, hp⟩
    exact (inputCheck_exact q root).mpr
      ⟨(DirectZeta.inputCheck_exact q root).mpr ⟨t, he, ht, hn⟩,
        by simpa only [he, interpretation_code] using hp⟩

theorem input_original (q root : Nat) (ha : inputCheck q root = true) :
    checkCode q root = true :=
  ((Comparison.acceptedCode_exact q root).mp
    (Bool.and_eq_true.mp ((inputCheck_exact q root).mp ha).1).1).1

def high (root : Nat) : Bool :=
  decide (1 < (rawTree (DirectZeta.argumentCode root)).outerSort)

theorem high_primrec : Primrec high :=
  (Primrec.nat_lt.comp (Primrec.const 1)
    (outerSort_primrec.comp (rawTree_primrec.comp DirectZeta.argumentCode_primrec))).decide

theorem high_input (q root : Nat) (ha : inputCheck q root = true)
    (hh : high root = true) : PublicEpsilonUnboundedIota.LambdaSource.inputCheck q root = true := by
  obtain ⟨t, he, ht, hn, hp⟩ := (inputCheck_literal q root).mp ha
  have hs : 1 < (rawTree (DirectZeta.argumentCode root)).outerSort := of_decide_eq_true hh
  exact (PublicEpsilonUnboundedIota.rootCheck_exact q root).mpr
    ⟨t, he, ht, by simpa only [Comparison.Normal] using hn,
      by simpa only [DirectZeta.argumentCode, he,
        Localization.argumentCode_theta, rawTree_code] using hs⟩

theorem low_input (q root : Nat) (ha : inputCheck q root = true)
    (hh : high root = false) : NonEpsilonBaseChange.inputCheck q root = true := by
  have hs := (inputCheck_exact q root).mp ha
  have hn : ¬ 1 < (rawTree (DirectZeta.argumentCode root)).outerSort := of_decide_eq_false hh
  exact (NonEpsilonBaseChange.inputCheck_exact q root).mpr
    ⟨hs.1, hs.2, (NonEpsilonBaseChange.non_epsilon_iff_low_argument q root hs.1 hs.2).mpr
      (le_of_not_gt hn)⟩

/-- The actual properness proviso removes the epsilon-base LOW exception.
All remaining epsilon and non-epsilon cases, including finite corrections,
are classified by the original collapse theorem, not by an assumed flag. -/
theorem high_iff_epsilon (q root : Nat) (ha : inputCheck q root = true) :
    high root = true ↔ Ordinal.omega0 ^ interpretation q root = interpretation q root := by
  constructor
  · intro hh
    exact PublicEpsilonUnboundedIota.root_epsilon q root (high_input q root ha hh)
  · intro he
    cases hh : high root with
    | true => rfl
    | false => exact False.elim
        (((NonEpsilonBaseChange.inputCheck_exact q root).mp (low_input q root ha hh)).2.2 he)

theorem branches_exhaustive (q root : Nat) (ha : inputCheck q root = true) :
    (high root = true ∧ PublicEpsilonUnboundedIota.LambdaSource.inputCheck q root = true) ∨
      (high root = false ∧ NonEpsilonBaseChange.inputCheck q root = true) := by
  cases hh : high root with
  | true => exact Or.inl ⟨rfl, high_input q root ha hh⟩
  | false => exact Or.inr ⟨rfl, low_input q root ha hh⟩

theorem inputCheck_context (q v root : Nat) (hq : checkCode q root = true)
    (hv : checkCode v root = true) : inputCheck q root = inputCheck v root := by
  simp only [inputCheck, DirectZeta.BaseChange.inputCheck_context q v root hq hv]

/-- The unchanged original syntax tests derive target properness and the
same epsilon branch from the chosen original root cutoff. -/
theorem target_input (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) : inputCheck v root = true := by
  have hd := (inputCheck_exact q root).mp ha
  have ht := DirectZeta.BaseChange.target_input q v root hd.1 hv hp
  have hvc := ((Comparison.acceptedCode_exact v root).mp (Bool.and_eq_true.mp ht).1).1
  rw [← inputCheck_context q v root (input_original q root ha) hvc]
  exact ha

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.SourceBranches
