import Alexander313.Wilken.PublicEpsilonNativeContextTranslation
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaAddition
import Alexander313.Wilken.HereditaryNativeBoundedContextIotaReturnSupport

/-!
# Genuine semantic SAME-value return to the original coded context

Every parameter of the actual alpha context lies below the ORIGINAL
checked alpha root and hence inside the ORIGINAL q LOW boundary. Actual
coverage and normalization give finite Normal representatives; classical
choice is used only for this semantic witness, with no computability claim.
Actual q addition and the complete zero scalar, together with the genuine
positive cardinal suffix, construct the finite return of every checked
alpha tree. No assigned recoder, output, admission or equality premise.
This is the semantic return needed to compare the genuine mu producers.
Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.ReturnSupport

open ThetaCourse
open PublicEpsilonUnboundedIota (betaCode betaCode_baseCheck beta_base)

private theorem parameter_exists (q alpha p : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hp : parameterCheck (betaCode q alpha) p = true) :
    ∃ c, lowCheckCode q c = true ∧ Comparison.acceptedCode q c = true ∧
      interpretation q c = parameters p := by
  have hbound : parameters p < globalBoundary (base q) 0 := by
    have h := parameter_sound (betaCode q alpha) p hp
    rw [beta_base q alpha ha] at h
    exact h.trans (checked_low_bound q alpha (RootLowCollapse.root_low q alpha ha))
  obtain ⟨c, hc, hv⟩ := (lt_boundary_iff_code q (RootLowCollapse.source_checked q alpha ha) _).mp hbound
  have hn := Normalization.normalizeCode_accepted q c (Bool.and_eq_true.mp hc).1
  exact ⟨Normalization.normalizeCode q c, LogEnd.normalized_low q c hc, hn.1, hn.2.trans hv⟩

def parameterGuard (q alpha p : Nat) : Bool :=
  RootLowCollapse.rootCheck q alpha && parameterCheck (betaCode q alpha) p

noncomputable def parameterCode (q alpha p : Nat) : Nat :=
  if hi : parameterGuard q alpha p = true then
    Classical.choose (parameter_exists q alpha p (Bool.and_eq_true.mp hi).1 (Bool.and_eq_true.mp hi).2)
  else 0

theorem parameterCode_spec (q alpha p : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hp : parameterCheck (betaCode q alpha) p = true) :
    lowCheckCode q (parameterCode q alpha p) = true ∧
      Comparison.acceptedCode q (parameterCode q alpha p) = true ∧
      interpretation q (parameterCode q alpha p) = parameters p := by
  have hi : parameterGuard q alpha p = true := Bool.and_eq_true.mpr ⟨ha, hp⟩
  rw [parameterCode, dif_pos hi]
  exact Classical.choose_spec (parameter_exists q alpha p (Bool.and_eq_true.mp hi).1 (Bool.and_eq_true.mp hi).2)

/-- The actual source sorts are derived from SAME values and the genuine
cardinal suffix; no sort or scalar caller is supplied. -/
theorem returned_sort (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (out k : Nat) (ho : Comparison.acceptedCode q out = true)
    (hv : interpretation q out = denote (betaCode q alpha) t)
    (hk : 0 < k) (hs : t.outerSort ≤ k) : (rawTree out).outerSort ≤ k := by
  have hc := ((Comparison.acceptedCode_exact q out).mp ho).1
  apply (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q out hc) k hk).mp
  rw [Arithmetic.raw_value q out hc, hv,
    RootPositiveCollapse.root_omegaSequence_pos q alpha k ha hk, ← beta_base q alpha ha]
  exact (denote_lt_iff_outerSort_le _ t ht k hk).mpr hs

noncomputable def returnedCode (q alpha : Nat) : RelativeTerm Nat → Nat
  | .parameter p => parameterCode q alpha p
  | .sum t u => Arithmetic.addCode q (returnedCode q alpha t) (returnedCode q alpha u)
  | .theta k t => cond (k == 0)
      (RootCompleteScalarCollapse.collapseCode q alpha 0 (returnedCode q alpha t))
      (RootPositiveCollapse.nodeCode k (returnedCode q alpha t))

noncomputable def returnedTerm (q alpha : Nat) (t : RelativeTerm Nat) : RelativeTerm Nat :=
  rawTree (returnedCode q alpha t)

/-- Every actually admitted alpha-context tree has a constructed finite
Normal SAME-value original-q return, with no Normal premise on that tree. -/
theorem returnedCode_spec (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true) :
    Comparison.acceptedCode q (returnedCode q alpha t) = true ∧
      interpretation q (returnedCode q alpha t) = denote (betaCode q alpha) t := by
  induction t with
  | parameter p =>
    have hp := (checked_admissible _ (.parameter p) ht).1
    have hs := parameterCode_spec q alpha p ha hp
    exact ⟨hs.2.1, hs.2.2⟩
  | sum t u iht ihu =>
    have hc := BaseTransformation.sum_checks _ t u ht
    have hst := iht hc.1
    have hsu := ihu hc.2
    have hs := Arithmetic.addCode_spec q _ _
      ((Comparison.acceptedCode_exact _ _).mp hst.1).1
      ((Comparison.acceptedCode_exact _ _).mp hsu.1).1
    refine ⟨hs.1, ?_⟩
    change interpretation q (Arithmetic.addCode q _ _) = _
    rw [hs.2.1, hst.2, hsu.2]
    rfl
  | theta k t ih =>
    have htc := BaseTransformation.theta_argument_check _ k t ht
    have hs := ih htc
    have hsort : t.outerSort ≤ k + 2 :=
      (denote_lt_iff_outerSort_le _ t htc (k + 2) (by omega)).mp
        (FixedPoint.checked_theta_sort _ k t ht)
    have hout := returned_sort q alpha ha t htc _ (k + 2) hs.1 hs.2 (by omega) hsort
    cases k with
    | zero =>
      have hi := (RootCompleteScalarCollapse.inputCheck_exact q alpha 0 _).mpr ⟨ha, hs.1, hout⟩
      have hc := RootCompleteScalarCollapse.collapseCode_spec q alpha 0 _ hi
      refine ⟨by simpa only [returnedCode, beq_self_eq_true, Bool.cond_true] using hc.1, ?_⟩
      simp only [returnedCode, beq_self_eq_true, Bool.cond_true]
      rw [hc.2, hs.2, ← beta_base q alpha ha]
      rfl
    | succ k =>
      have hi := (RootPositiveCollapse.inputCheck_exact q alpha (k + 1) _).mpr
        ⟨ha, hs.1, Nat.succ_pos k, hout⟩
      have hc := RootPositiveCollapse.collapseCode_spec q alpha (k + 1) _ hi
      rw [RootPositiveCollapse.collapseCode_eq q alpha (k + 1) _ hi] at hc
      have hk : (k + 1 == 0) = false := by simp
      refine ⟨by simpa only [returnedCode, hk, Bool.cond_false] using hc.1, ?_⟩
      simp only [returnedCode, hk, Bool.cond_false]
      rw [hc.2, hs.2, ← beta_base q alpha ha]
      rfl

theorem returnedTerm_spec (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true) :
    check q (returnedTerm q alpha t) = true ∧ Comparison.Normal q (returnedTerm q alpha t) ∧
      denote q (returnedTerm q alpha t) = denote (betaCode q alpha) t := by
  have hs := returnedCode_spec q alpha ha t ht
  have hc := (Comparison.acceptedCode_exact q _).mp hs.1
  exact ⟨Arithmetic.raw_checked q _ hc.1, hc.2,
    (Arithmetic.raw_value q _ hc.1).trans hs.2⟩

theorem returnedCode_low (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (hl : t.outerSort ≤ 1) : lowCheckCode q (returnedCode q alpha t) = true := by
  have hs := returnedCode_spec q alpha ha t ht
  have hc := ((Comparison.acceptedCode_exact q _).mp hs.1).1
  apply OmegaPowers.low_of_bound q _ hc
  rw [hs.2, RootPositiveCollapse.root_omegaSequence_pos q alpha 1 ha (by omega),
    ← beta_base q alpha ha]
  exact (denote_lt_iff_outerSort_le _ t ht 1 (by omega)).mpr hl

/-- Every LOW return has its FULL hidden zero support below any genuine
larger value. This cut derives from the actual Normal return. -/
theorem returnedTerm_low_fullBelow (q alpha : Nat) (ha : RootLowCollapse.rootCheck q alpha = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (hl : t.outerSort ≤ 1) (xi : Ordinal.{0}) (hb : denote (betaCode q alpha) t < xi) :
    BoundedContextIota.ReturnSupport.FullBelow q xi (returnedTerm q alpha t) := by
  have hs := returnedCode_spec q alpha ha t ht
  exact BoundedContextIota.ReturnSupport.lowCode_fullBelow q _ xi
    (returnedCode_low q alpha ha t ht hl) hs.1 (hs.2.trans_lt hb)


/-- Positive indices are retained literally by the semantic source return. -/
theorem returnedTerm_theta_succ (q alpha k : Nat) (t : RelativeTerm Nat) :
    returnedTerm q alpha (.theta (k + 1) t) = .theta (k + 1) (returnedTerm q alpha t) := by
  have hk : (k + 1 == 0) = false := by simp
  simp only [returnedTerm, returnedCode, hk, Bool.cond_false,
    RootPositiveCollapse.nodeCode, rawTree_code]

/-- Every original restricted alpha-context expression returns with the
FULL hidden source cut at that SAME beta value. -/
theorem returnedTerm_restricted (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (hn : Comparison.Normal (betaCode q alpha) t)
    (hr : PublicEpsilonUnboundedIota.Restricted (betaCode q alpha) beta t) :
    BoundedContextIota.ReturnSupport.FullBelow q (interpretation (betaCode q alpha) beta)
      (returnedTerm q alpha t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hp := checked_parameters _ (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact returnedTerm_low_fullBelow q alpha ha (.parameter p) ht (by simp [RelativeTerm.outerSort])
      _ (hp.2.trans_le (RootLowCollapse.root_base_le _ _ hb))
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (PublicEpsilonUnboundedIota.restricted_sum _ _ t u).mp hr
    have hst := returnedCode_spec q alpha ha t hc.1
    have hsu := returnedCode_spec q alpha ha u hc.2
    exact BoundedContextIota.ReturnSupport.addCode_fullBelow q _ _ _
      ((Comparison.acceptedCode_exact _ _).mp hst.1).1
      ((Comparison.acceptedCode_exact _ _).mp hsu.1).1
      (iht hc.1 hn.1 hs.1) (ihu hc.2 hn.2.1 hs.2)
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      exact returnedTerm_low_fullBelow q alpha ha (.theta 0 t) ht le_rfl _
        ((PublicEpsilonUnboundedIota.restricted_theta_zero _ _ t).mp hr).1
    | succ k =>
      rw [returnedTerm_theta_succ]
      exact (BoundedContextIota.ReturnSupport.fullBelow_theta_succ q _ k _).mpr
        (ih (BaseTransformation.theta_argument_check _ (k + 1) t ht) hn
          ((PublicEpsilonUnboundedIota.restricted_theta_succ _ _ k t).mp hr))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.ReturnSupport
