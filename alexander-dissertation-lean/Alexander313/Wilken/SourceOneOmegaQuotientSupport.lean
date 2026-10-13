import Alexander313.Wilken.SourceOneNativeIotaOrder
import Alexander313.Wilken.HereditaryNativeOmegaQuotientSupport
import Alexander313.Wilken.HereditaryOmegaPowers
import Alexander313.Wilken.HereditarySourceFixedPointSupport
import Alexander313.Wilken.HereditarySourceZetaTransport
import Alexander313.Wilken.HereditaryDifference

/-!
# Actual original base-one quotient callers

Original checks at public level zero, original hereditary Normality and
original thetaAtoms are used throughout. The source base one is never
submitted to the native positive-epsilon parser. Full original restriction
survives real source normalization and the selected suffix of the original
difference algorithm. Actual public omega power followed by the genuine
bounded original return constructs every LOW power caller at level zero.
The ordinal theta-one quotient laws genuinely include tau=1. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.OmegaQuotient

open OrderSupport
open NativeContext.OmegaQuotient (theta_one_below_threshold theta_one_shifted_quotient
  theta_one_above_threshold principal_above_second_absorbs epsilon_above_absorbs)

theorem zero_restricted (a : Nat) : Restricted a (zeroTree 0) := by
  intro u hu
  simp only [zeroTree, fullList, RelativeTerm.PrincipalSupport.principalList,
    List.not_mem_nil] at hu

theorem buildRev_restricted (a : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted a t) : Restricted a (Theta.Normalization.buildRev 0 as) := by
  revert hr
  induction as with
  | nil => intro _; exact zero_restricted a
  | cons t as ih =>
    intro hr
    exact (restricted_sum a _ _).mpr
      ⟨ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)), hr t List.mem_cons_self⟩

theorem buildAtoms_restricted (a : Nat) (as : List (RelativeTerm Nat))
    (hr : ∀ t ∈ as, Restricted a t) : Restricted a (Theta.Normalization.buildAtoms 0 as) :=
  buildRev_restricted a as.reverse (fun t ht => hr t (List.mem_reverse.mp ht))

theorem normalize_spec (t : RelativeTerm Nat) (ht : check 0 t = true) :
    check 0 (Theta.Normalization.normalize 0 t) = true ∧
      Theta.Normal 0 (Theta.Normalization.normalize 0 t) ∧
      denote 0 (Theta.Normalization.normalize 0 t) = denote 0 t := by
  have hs := Theta.Normalization.normalize_spec 0 (SourceOne.PublicCodes.fragment t) t
    ((finiteCheck_iff 0 _ t).mp ht)
  exact ⟨Theta.admitted_checked hs.1, hs.2.1, hs.2.2⟩

/-- The original source normalizer changes no theta-zero value, and its
binary sums select genuine normalized original atoms. -/
theorem normalize_restricted (a : Nat) (t : RelativeTerm Nat)
    (ht : check 0 t = true) (hr : Restricted a t) :
    Restricted a (Theta.Normalization.normalize 0 t) := by
  revert ht hr
  induction t with
  | parameter p =>
    intro ht hr
    exact zero_restricted a
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    rw [Theta.Normalization.normalize_sum]
    apply buildAtoms_restricted
    intro v hv
    have hm := Theta.Normalization.normalizeAtoms_mem 0 v _ hv
    rcases List.mem_append.mp hm with hm | hm
    · exact restricted_atoms a _ v (iht hc.1 hs.1) hm
    · exact restricted_atoms a _ v (ihu hc.2 hs.2) hm
  | theta k t ih =>
    intro ht hr
    have hc := argument_checked k t ht
    rw [Theta.Normalization.normalize_theta]
    cases k with
    | zero =>
      have hs := (restricted_theta_zero a t).mp hr
      apply (restricted_theta_zero a _).mpr
      refine ⟨?_, ih hc hs.2⟩
      change globalCollapse (finiteBase 0) 0 (denote 0 (Theta.Normalization.normalize 0 t)) < _
      rw [(normalize_spec t hc).2.2]
      exact hs.1
    | succ k =>
      exact (restricted_theta_succ a k _).mpr
        (ih hc ((restricted_theta_succ a k t).mp hr))

/-- The real original Difference.tree is built from a selected suffix of
the original normalized right ANF, including every hidden theta argument. -/
theorem subtract_restricted (a c d : Nat) (hd : checkCode 0 d = true)
    (hr : Restricted a (ThetaCourse.rawTree d)) : Restricted a (Difference.tree 0 c d) := by
  unfold Difference.tree
  apply buildAtoms_restricted
  intro t ht
  have hm := Difference.removeCommon_mem (Theta.equal 0)
    (Principal.normalizedAtoms 0 c) (Principal.normalizedAtoms 0 d) t ht
  obtain ⟨u, he, hu⟩ := (checkCode_iff 0 d).mp hd
  have hr' : Restricted a u := by simpa only [← he, ThetaCourse.rawTree_code] using hr
  have hn := normalize_restricted a u hu hr'
  have hv : Principal.normalizedTree 0 d = Theta.Normalization.normalize 0 u := by
    simp only [Principal.normalizedTree, ← he, Theta.Normalization.normalizeCode_code,
      ThetaCourse.rawTree_code]
  change t ∈ Theta.atoms 0 (Principal.normalizedTree 0 d) at hm
  rw [hv] at hm
  exact restricted_atoms a _ t hn hm

/-- Actual finite full-support domination for EVERY original Normal LOW
tree, including its hidden high arguments. This is the original source
dictionary, distinct from native public-payload checks. -/
theorem fullList_value_le_low (t u : RelativeTerm Nat) (ht : check 0 t = true)
    (hn : Theta.Normal 0 t) (hl : t.outerSort ≤ 1) (hu : u ∈ fullList t) :
    denote 0 u ≤ denote 0 t := by
  revert ht hn hl hu
  induction t with
  | parameter p =>
    intro ht hn hl hu
    simp only [fullList, RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hu
  | sum t v iht ihv =>
    intro ht hn hl hu
    have hc := sum_checks t v ht
    rcases List.mem_append.mp hu with hu | hu
    · exact (iht hc.1 hn.1 ((le_max_left _ _).trans hl) hu).trans le_self_add
    · exact (ihv hc.2 hn.2.1 ((le_max_right _ _).trans hl) hu).trans le_add_self
  | theta k t ih =>
    intro ht hn hl hu
    have hk : k = 0 := by simp only [outerSort] at hl; omega
    subst k
    let n := SourceOne.PublicCodes.fragment (.theta 0 t)
    have had := (finiteCheck_iff 0 n (.theta 0 t)).mp ht
    have haa := Theta.admitted_theta_argument had
    have hnt : Theta.Normal 0 t := hn
    have hua := RelativeTerm.PrincipalSupport.principalList_admissible had.2 0 hu
    have h := RelativeTerm.PrincipalSupport.principalList_theta_value_le
      (finiteBase 0) (finiteBase_pos 0) (parameters 0) n 0 t u had.2 (hnt.finite haa) hu
    rw [← denote_eq_finite 0 n u hua, ← denote_eq_finite 0 n (.theta 0 t) had.2] at h
    exact h

/-- Literal public power and genuine bounded return to ORIGINAL level zero.
The return bound is derived below, not supplied by a caller oracle. -/
def lowPowerCode (c : Nat) : Nat :=
  SourceZeta.Transport.returnCode 0 (OmegaPowers.powerCode (Nat.pair 0 c))

theorem lowPowerCode_primrec : Primrec lowPowerCode :=
  SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0)
    (OmegaPowers.powerCode_primrec.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))

theorem lowPowerCode_spec (c : Nat) (hc : lowCheckCode 0 c = true) :
    Theta.acceptedLowCode 0 (lowPowerCode c) = true ∧
      interpretation 0 (lowPowerCode c) = Ordinal.omega0 ^ interpretation 0 c := by
  have hq : unionCheck (Nat.pair 0 c) = true := by simpa only [unionCheck_pair] using hc
  have hb : interpretation 0 c < finiteBase 1 :=
    (lt_nextBase_iff_code 0 _).mpr ⟨c, hc, rfl⟩
  have hp := OmegaPowers.powerCode_value _ hq
  have hbound : unionInterpretation (OmegaPowers.powerCode (Nat.pair 0 c)) < finiteBase 1 := by
    rw [hp, unionInterpretation_pair]
    exact (omegaPower_strictMono hb).trans_eq (finiteBase_succ_omegaPower_eq_self 0)
  have hr := SourceZeta.Transport.returnCode_spec 0 _ (OmegaPowers.powerCode_checked _ hq) hbound
  exact ⟨hr.1, hr.2.trans (by simpa only [unionInterpretation_pair] using hp)⟩

def baseTerm : RelativeTerm Nat := .theta 1 (zeroTree 0)

def unitTerm : RelativeTerm Nat := .theta 0 (zeroTree 0)

def thresholdTerm : RelativeTerm Nat := .theta 1 unitTerm

theorem theta_checked (k : Nat) (t : RelativeTerm Nat) (ht : check 0 t = true)
    (hs : t.outerSort ≤ k + 2) : check 0 (.theta k t) = true := by
  simp only [Uniform.check_theta, ht, hs, decide_true, Bool.true_and]

theorem baseTerm_spec : check 0 baseTerm = true ∧ Theta.Normal 0 baseTerm ∧
    denote 0 baseTerm = omegaSequence (finiteBase 0) 1 := by
  refine ⟨theta_checked 1 _ (Bool.and_eq_true.mp (zeroTree_lowCheck 0)).1 (by decide),
    Theta.Normalization.zeroTree_normal 0, ?_⟩
  change globalCollapse (finiteBase 0) 1 (denote 0 (zeroTree 0)) = _
  rw [zeroTree_denote]
  exact globalCollapse_zero (finiteBase 0) (finiteBase_pos 0) (finiteBase_add_closed 0) 1

theorem unitTerm_spec : check 0 unitTerm = true ∧ Theta.Normal 0 unitTerm ∧ denote 0 unitTerm = 1 := by
  refine ⟨theta_checked 0 _ (Bool.and_eq_true.mp (zeroTree_lowCheck 0)).1 (by decide),
    Theta.Normalization.zeroTree_normal 0, ?_⟩
  change globalCollapse (finiteBase 0) 0 (denote 0 (zeroTree 0)) = _
  rw [zeroTree_denote, globalCollapse_zero (finiteBase 0) (finiteBase_pos 0)
    (finiteBase_add_closed 0) 0, omegaSequence_zero, finiteBase_zero]

theorem thresholdTerm_spec : check 0 thresholdTerm = true ∧ Theta.Normal 0 thresholdTerm ∧
    denote 0 thresholdTerm = omegaSequence (finiteBase 0) 1 * Ordinal.omega0 := by
  refine ⟨theta_checked 1 _ unitTerm_spec.1 (by
    simp only [unitTerm, RelativeTerm.outerSort]; omega), unitTerm_spec.2.1, ?_⟩
  change globalCollapse (finiteBase 0) 1 (denote 0 unitTerm) = _
  rw [unitTerm_spec.2.2]
  exact NativeContext.OmegaQuotient.theta_one_unit (finiteBase 0) (Or.inl finiteBase_zero)

theorem theta_principal (k : Nat) (t : RelativeTerm Nat) (ht : check 0 (.theta k t) = true) :
    0 < denote 0 (.theta k t) ∧ Ordinal.IsPrincipal (· + ·) (denote 0 (.theta k t)) := by
  let n := SourceOne.PublicCodes.fragment (.theta k t)
  have ha := (finiteCheck_iff 0 n (.theta k t)).mp ht
  have hp := Theta.theta_pos_principal 0 n k t ha
  rw [← denote_eq_finite 0 n (.theta k t) ha.2] at hp
  exact hp

/-- The actual original theta-one high input has a genuine epsilon value
strictly above Omega-one. The finite/global family theorem derives absorption. -/
theorem theta_one_high_absorbs (t : RelativeTerm Nat) (ht : check 0 (.theta 1 t) = true)
    (hh : omegaSequence (finiteBase 0) 2 ≤ denote 0 t) :
    omegaSequence (finiteBase 0) 1 * denote 0 (.theta 1 t) = denote 0 (.theta 1 t) := by
  let n := SourceOne.PublicCodes.fragment (.theta 1 t)
  have ha := (finiteCheck_iff 0 n (.theta 1 t)).mp ht
  have haa := Theta.admitted_theta_argument ha
  have hn : 1 < n := by
    cases ha.2 with
    | theta h0k hkn hsort ha => exact hkn
  have hh' : omegaSequence (finiteBase 0) 2 ≤ finiteDenote 0 n t := by
    rw [← denote_eq_finite 0 n t haa.2]
    exact hh
  have hp : sourceFiniteCollapse (finiteBase 0) n 1 (finiteDenote 0 n t) <
      omegaSequence (finiteBase 0) 2 := by
    rw [← denote_eq_finite 0 n (.theta 1 t) ha.2]
    exact (SourceFixedPoint.checked_theta_range 0 1 t ht).2
  have he := sourceFiniteCollapse_high_omegaPower_eq_self (finiteBase 0) (finiteBase_pos 0)
    n 1 hn (finiteDenote 0 n t) hh' hp
  have hb := sourceFiniteCollapse_high_base_lt (finiteBase 0) (finiteBase_pos 0)
    n 1 hn (finiteDenote 0 n t) hh'
  rw [denote_eq_finite 0 n (.theta 1 t) ha.2]
  exact epsilon_above_absorbs _ _ (omegaSequence_succ_omegaPower_eq_self (finiteBase 0) 0) he hb

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.OmegaQuotient
