import Alexander313.Wilken.HereditaryNativeFixedPoint
import Alexander313.Wilken.SuccessorEpsilonBases

/-!
# Genuine original native epsilon callers for the source indicator

The originally coded native base is a literal epsilon, by the actual base
checker. Original admission supplies all recursive children and theta
argument sorts. The actual cardinal ranges and collapse injection identify
every base-valued theta as theta-zero with a genuinely zero argument.
No chi, normalizer, comparison or source-fidelity oracle is supplied.
All proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi

theorem epsilon_base (q : Nat) (hq : baseCheck q = true) :
    Ordinal.omega0 ^ base q = base q := ((baseCheck_exact q).mp hq).2

theorem base_add_closed (q : Nat) (hq : baseCheck q = true) :
    Ordinal.IsPrincipal (· + ·) (base q) := epsilon_or_one_add_closed (Or.inr (epsilon_base q hq))

theorem sum_children (q : Nat) (a b : RelativeTerm Nat)
    (ht : check q (.sum a b) = true) (hn : Comparison.Normal q (.sum a b)) :
    check q a = true ∧ Comparison.Normal q a ∧ check q b = true ∧ Comparison.Normal q b ∧
      SourceNormalSum (denote q (.sum a b)) (denote q a) (denote q b) := by
  have hq := (Bool.and_eq_true.mp ht).1
  have ha := NativeContext.checked_admissible q (.sum a b) ht
  cases ha.2 with
  | sum haa hbb =>
    exact ⟨Comparison.admitted_checked q _ hq a ⟨ha.1.1, haa⟩, hn.1,
      Comparison.admitted_checked q _ hq b ⟨ha.1.2, hbb⟩, hn.2.1, hn.2.2⟩

theorem theta_argument_input (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a)) :
    FixedPoint.inputCheck q m a.code = true := by
  apply (FixedPoint.inputCheck_exact q m a.code).mpr
  exact ⟨by simpa only [checkCode_code] using FixedPoint.checked_theta_argument q m a ht,
    by simpa only [ThetaCourse.rawTree_code] using hn,
    by simpa only [interpretation_code] using FixedPoint.checked_theta_sort q m a ht⟩

theorem theta_argument_parts (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hn : Comparison.Normal q (.theta m a)) :
    Decomposition.inputCheck q a.code = true ∧
      Decomposition.inputCheck q (Decomposition.highCode m a.code) = true ∧
      Decomposition.inputCheck q (Decomposition.lowCode m a.code) = true := by
  have hai : Decomposition.inputCheck q a.code = true :=
    (Decomposition.inputCheck_exact q a.code).mpr
      ⟨by simpa only [checkCode_code] using FixedPoint.checked_theta_argument q m a ht,
        by simpa only [ThetaCourse.rawTree_code] using hn⟩
  exact ⟨hai, Decomposition.parts_accepted q m a.code hai⟩

/-- Recognition of the explicit chi(base)=1 clause is by actual native
value; it does not require a preferred zero spelling. -/
theorem theta_base_argument_zero (q m : Nat) (a : RelativeTerm Nat)
    (ht : check q (.theta m a) = true) (hv : denote q (.theta m a) = base q) :
    m = 0 ∧ denote q a = 0 := by
  have hq := (Bool.and_eq_true.mp ht).1
  have hrange := FixedPoint.checked_theta_range q m a ht
  have hm : m = 0 := by
    by_contra h
    have hp : 0 < m := Nat.pos_of_ne_zero h
    have hs := (omegaSequence_strictMono (base q)) hp
    rw [omegaSequence_zero] at hs
    exact hs.not_ge (hrange.1.trans_eq hv)
  subst m
  have ha := FixedPoint.checked_theta_argument q 0 a ht
  have hzcheck := Normalization.zeroTree_checked q hq
  let alpha := FixedPoint.sourceOrdinal q 0 a ha
  let z := FixedPoint.sourceOrdinal q 0 Normalization.zeroTree hzcheck
  have hz : z.val = 0 := Normalization.zeroTree_denote q
  have hsorta : alpha.val < omegaSequence (base q) 2 := FixedPoint.checked_theta_sort q 0 a ht
  have hsortz : z.val < omegaSequence (base q) 2 := by
    rw [hz]
    exact (base_pos q hq).trans_le
      ((omegaSequence_strictMono (base q)).monotone (Nat.zero_le 2))
  have he : globalCollapse (base q) 0 alpha.val = globalCollapse (base q) 0 z.val := by
    rw [hz, globalCollapse_zero (base q) (base_pos q hq) (base_add_closed q hq) 0,
      omegaSequence_zero]
    exact hv
  have heq := (globalCollapse_eq_iff (base q) (base_pos q hq) 0 alpha z hsorta hsortz).mp he
  exact ⟨rfl, heq.trans hz⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceChi
