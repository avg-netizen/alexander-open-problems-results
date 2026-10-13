import Alexander313.Wilken.HereditarySourceFixedPoint
import Alexander313.Wilken.SuccessorEpsilonBases

/-!
# Genuine public epsilon callers for the source indicator

Definition 3.3 has an epsilon base. Public positive levels supply that
condition from the constructed finite bases. The original admission gives
every recursive child and theta caller. A theta value equal to the base is
necessarily theta-zero with an actual zero argument, by the real cardinal
range and source collapse injection. No indicator or spelling oracle enters.
All proofs are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceChi

theorem epsilon_base (r : Nat) (hr : 0 < r) :
    Ordinal.omega0 ^ finiteBase r = finiteBase r := by
  cases r with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ r => exact finiteBase_succ_omegaPower_eq_self r

theorem sum_children (r : Nat) (a b : RelativeTerm Nat)
    (ht : check r (.sum a b) = true) (hn : Theta.Normal r (.sum a b)) :
    check r a = true ∧ Theta.Normal r a ∧ check r b = true ∧ Theta.Normal r b ∧
      SourceNormalSum (denote r (.sum a b)) (denote r a) (denote r b) := by
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible r (.sum a b)).mp ht
  cases ha.2 with
  | sum haa hbb =>
    have hs := (Theta.normal_sum r a b).mp hn
    exact ⟨Theta.admitted_checked ⟨ha.1.1, haa⟩, hs.1,
      Theta.admitted_checked ⟨ha.1.2, hbb⟩, hs.2.1, hs.2.2⟩

theorem theta_argument_input (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a)) :
    SourceFixedPoint.inputCheck r m a.code = true := by
  apply (SourceFixedPoint.inputCheck_exact r m a.code).mpr
  exact ⟨by simpa only [checkCode_code] using SourceFixedPoint.checked_theta_argument r m a ht,
    by simpa only [ThetaCourse.rawTree_code] using (Theta.normal_theta r m a).mp hn,
    by simpa only [interpretation_code] using SourceFixedPoint.checked_theta_sort r m a ht⟩

theorem theta_argument_parts (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hn : Theta.Normal r (.theta m a)) :
    SourceDecomposition.inputCheck r a.code = true ∧
      SourceDecomposition.inputCheck r (SourceDecomposition.highCode r m a.code) = true ∧
      SourceDecomposition.inputCheck r (SourceDecomposition.lowCode r m a.code) = true := by
  have hai : SourceDecomposition.inputCheck r a.code = true :=
    (SourceDecomposition.inputCheck_exact r a.code).mpr
      ⟨by simpa only [checkCode_code] using SourceFixedPoint.checked_theta_argument r m a ht,
        by simpa only [ThetaCourse.rawTree_code] using (Theta.normal_theta r m a).mp hn⟩
  exact ⟨hai, SourceDecomposition.parts_accepted r m a.code hai⟩

/-- The explicit chi(base)=1 clause is recognized by actual value, even
when an admitted zero argument has another weak-normal spelling. -/
theorem theta_base_argument_zero (r m : Nat) (a : RelativeTerm Nat)
    (ht : check r (.theta m a) = true) (hv : denote r (.theta m a) = finiteBase r) :
    m = 0 ∧ denote r a = 0 := by
  have hrange := SourceFixedPoint.checked_theta_range r m a ht
  have hm : m = 0 := by
    by_contra h
    have hp : 0 < m := Nat.pos_of_ne_zero h
    have hs := (omegaSequence_strictMono (finiteBase r)) hp
    rw [omegaSequence_zero] at hs
    exact hs.not_ge (hrange.1.trans_eq hv)
  subst m
  have ha := SourceFixedPoint.checked_theta_argument r 0 a ht
  have hzcheck : check r (zeroTree r) = true := (Bool.and_eq_true.mp (zeroTree_lowCheck r)).1
  let alpha := SourceFixedPoint.sourceOrdinal r 0 a ha
  let z := SourceFixedPoint.sourceOrdinal r 0 (zeroTree r) hzcheck
  have hz : z.val = 0 := zeroTree_denote r
  have hsorta : alpha.val < omegaSequence (finiteBase r) 2 :=
    SourceFixedPoint.checked_theta_sort r 0 a ht
  have hsortz : z.val < omegaSequence (finiteBase r) 2 := by
    rw [hz]
    exact (finiteBase_pos r).trans_le
      ((omegaSequence_strictMono (finiteBase r)).monotone (Nat.zero_le 2))
  have he : globalCollapse (finiteBase r) 0 alpha.val = globalCollapse (finiteBase r) 0 z.val := by
    rw [hz, globalCollapse_zero (finiteBase r) (finiteBase_pos r) (finiteBase_add_closed r) 0,
      omegaSequence_zero]
    exact hv
  have heq := (globalCollapse_eq_iff (finiteBase r) (finiteBase_pos r) 0 alpha z hsorta hsortz).mp he
  exact ⟨rfl, heq.trans hz⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceChi
