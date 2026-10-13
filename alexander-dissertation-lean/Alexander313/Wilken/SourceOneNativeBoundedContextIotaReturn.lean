import Alexander313.Wilken.SourceOneNativeBoundedContextIotaReturnSupport

/-!
# Actual source-one iota compatibility with bounded SAME-value return

The genuine returned original theta-zero root and beta identity are derived
in support. The finite return follows the actual source-one normalized sum,
low stops, and retained positive indices. Normal source sums come from the
original input's real source-normal condition and returned SAME values;
proved two-way order compares them with actual normalized sums. No sum,
normalizer, return, source-star or iota compatibility oracle is supplied.
Original checked Normal restricted inputs only. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn

private theorem normalizedSum_transform (r c d : Nat) (hr : rootCheck r = true)
    (hc : Theta.acceptedCode 0 c = true) (hd : Theta.acceptedCode 0 d = true)
    (hrc : Restricted r (ThetaCourse.rawTree c)) (hrd : Restricted r (ThetaCourse.rawTree d))
    (hsn : Theta.Normal 0 (.sum (ThetaCourse.rawTree c) (ThetaCourse.rawTree d))) :
    NativeContext.denote (alphaCode r)
        (transform r (ThetaCourse.rawTree (Addition.normalizedSumCode 0 c d))) =
      NativeContext.denote (alphaCode r) (transform r (ThetaCourse.rawTree c)) +
        NativeContext.denote (alphaCode r) (transform r (ThetaCourse.rawTree d)) := by
  have hct := SourceDecomposition.input_tree 0 c hc
  have hdt := SourceDecomposition.input_tree 0 d hd
  have hcc := ((Theta.acceptedCode_iff 0 c).mp hc).1
  have hdc := ((Theta.acceptedCode_iff 0 d).mp hd).1
  have hs := Addition.normalizedSumCode_checked 0 c d hcc hdc
  have hst := SourceDecomposition.input_tree 0 _ hs.1
  have hsr : Restricted r (ThetaCourse.rawTree (Addition.normalizedSumCode 0 c d)) :=
    normalizedSumCode_fullBelow c d (interpretation 0 r) hcc hdc hrc hrd
  have hsum : check 0 (.sum (ThetaCourse.rawTree c) (ThetaCourse.rawTree d)) = true := by
    simpa only [Uniform.check_sum, hct.1, hdt.1, Bool.true_and]
  have hsumr := (restricted_sum r _ _).mpr ⟨hrc, hrd⟩
  have hv : denote 0 (ThetaCourse.rawTree (Addition.normalizedSumCode 0 c d)) =
      denote 0 (.sum (ThetaCourse.rawTree c) (ThetaCourse.rawTree d)) := by
    rw [← SourceDecomposition.input_value 0 _ hs.1, hs.2,
      SourceDecomposition.input_value 0 c hc, SourceDecomposition.input_value 0 d hd]
    rfl
  have he := (transform_eq_iff r hr _ _ hst.1 hsum hst.2 hsn hsr hsumr).mpr hv
  exact he.trans (OrderSupport.transform_add r hr _ _ hct.1 hdt.1)

private theorem returnedTerm_theta_succ (a k : Nat) (t : RelativeTerm Nat) :
    returnedTerm a (.theta (k + 1) t) = .theta (k + 1) (returnedTerm a t) := by
  have hk : (k + 1 == 0) = false := by simp
  simp only [returnedTerm, BoundedPublicReturn.sourceTermCode_theta,
    BoundedPublicReturn.thetaCode, hk, Bool.cond_false,
    BoundedPublicReturn.nodeCode, ThetaCourse.rawTree_code]

private theorem transform_return_below (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t)
    (hv : NativeContext.denote (alphaCode a) t < NativeContext.interpretation (alphaCode a) b) :
    NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (transform (returnedRoot a b) (returnedTerm a t)) =
      NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (NativeContext.PublicEpsilonIota.transform (alphaCode a) b t) := by
  have hs := returnedTerm_spec a b ha hb t ht hn hr
  have hbr : denote 0 (returnedTerm a t) < interpretation 0 (returnedRoot a b) := by
    rw [hs.2.2, (returnedRoot_spec a b ha hb).2.2]
    exact hv
  have ho := transform_below_value (returnedRoot a b) (returnedRoot_iota_caller a b ha hb)
    _ hs.1 hbr
  rw [returnedRoot_alphaCode a b ha hb] at ho
  have hi := NativeContext.PublicEpsilonIota.transform_parameter_value (alphaCode a) b hb t ht hv
  exact ho.trans (hs.2.2.trans hi.2.symm)

/-- Both genuine iota maps agree after the actual finite SAME-value return
from the intermediate ORIGINAL q dictionary to ORIGINAL source one. -/
theorem transform_return_value (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t) :
    NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (transform (returnedRoot a b) (returnedTerm a t)) =
      NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
        (NativeContext.PublicEpsilonIota.transform (alphaCode a) b t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hp := NativeContext.checked_parameters (alphaCode a) (.parameter p) ht p
      (by simp [RelativeTerm.parameters])
    exact transform_return_below a b ha hb (.parameter p) ht hn hr
      (hp.2.trans_le (NativeContext.PublicEpsilonIota.root_base_le (alphaCode a) b hb))
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := NativeContext.BaseTransformation.sum_checks (alphaCode a) t u ht
    have hs := (NativeContext.PublicEpsilonIota.restricted_sum (alphaCode a) b t u).mp hr
    have hct := sourceTermCode_spec a b ha hb t hc.1 hn.1 hs.1
    have hcu := sourceTermCode_spec a b ha hb u hc.2 hn.2.1 hs.2
    have hvt := returnedTerm_spec a b ha hb t hc.1 hn.1 hs.1
    have hvu := returnedTerm_spec a b ha hb u hc.2 hn.2.1 hs.2
    have hsn : Theta.Normal 0 (.sum (returnedTerm a t) (returnedTerm a u)) := by
      refine Theta.Normal.sum hvt.2.1 hvu.2.1 ?_
      change SourceNormalSum (denote 0 (returnedTerm a t) + denote 0 (returnedTerm a u))
        (denote 0 (returnedTerm a t)) (denote 0 (returnedTerm a u))
      rw [hvt.2.2, hvu.2.2]
      exact hn.2.2
    have ho := normalizedSum_transform (returnedRoot a b) _ _
      (returnedRoot_iota_caller a b ha hb) hct.1 hcu.1
      (returnedTerm_restricted a b ha hb t hc.1 hn.1 hs.1)
      (returnedTerm_restricted a b ha hb u hc.2 hn.2.1 hs.2) hsn
    rw [returnedRoot_alphaCode a b ha hb] at ho
    change NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
      (transform (returnedRoot a b) (ThetaCourse.rawTree
        (BoundedPublicReturn.sourceTermCode a (.sum t u)))) = _
    rw [BoundedPublicReturn.sourceTermCode_sum, ho,
      NativeContext.PublicEpsilonIota.OrderSupport.transform_add (alphaCode a) b hb t u hc.1 hc.2,
      iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2]
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      exact transform_return_below a b ha hb (.theta 0 t) ht hn hr
        ((NativeContext.PublicEpsilonIota.restricted_theta_zero (alphaCode a) b t).mp hr).1
    | succ k =>
      have hc := NativeContext.BaseTransformation.theta_argument_check (alphaCode a) (k + 1) t ht
      have hs := (NativeContext.PublicEpsilonIota.restricted_theta_succ (alphaCode a) b k t).mp hr
      have hrt := returnedTerm_restricted a b ha hb (.theta (k + 1) t) ht hn hr
      have hct := (returnedTerm_spec a b ha hb (.theta (k + 1) t) ht hn hr).1
      rw [returnedTerm_theta_succ] at hct hrt ⊢
      rw [OrderSupport.transform_theta_succ (returnedRoot a b) k
          (returnedRoot_iota_caller a b ha hb) _ hct hrt,
        NativeContext.PublicEpsilonIota.OrderSupport.transform_theta_succ (alphaCode a) b k hb t ht hr]
      change globalCollapse (NativeContext.base (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)) k
        (NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
          (transform (returnedRoot a b) (returnedTerm a t))) =
        globalCollapse (NativeContext.base (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)) k
          (NativeContext.denote (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b)
            (NativeContext.PublicEpsilonIota.transform (alphaCode a) b t))
      rw [ih hc hn hs]

/-- Admission and the full ORIGINAL source-star guard of the actual
returned source-one tree follow from the original intermediate domain. -/
theorem returnedTerm_iota_caller (a b : Nat) (ha : rootCheck a = true)
    (hb : NativeContext.PublicEpsilonIota.rootCheck (alphaCode a) b = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hr : NativeContext.PublicEpsilonIota.Restricted (alphaCode a) b t) :
    inputCheck (returnedRoot a b) (returnedTerm a t).code = true := by
  have hs := returnedTerm_spec a b ha hb t ht hn hr
  have hroot := returnedRoot_iota_caller a b ha hb
  have hcut := returnedTerm_restricted a b ha hb t ht hn hr
  exact (inputCheck_exact _ _).mpr ⟨hroot, returnedTerm a t, rfl, hs.1, hs.2.1,
    (restricted_iff_sourceStar _ hroot _ hs.1 hs.2.1).mp hcut⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn
