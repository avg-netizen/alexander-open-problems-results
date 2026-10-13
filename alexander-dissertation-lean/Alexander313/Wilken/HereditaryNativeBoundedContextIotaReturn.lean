import Alexander313.Wilken.HereditaryNativeBoundedContextIotaReturnSupport
import Alexander313.Wilken.HereditaryNativeBoundedContextSourceReturnSupport
import Alexander313.Wilken.HereditaryNativeIotaAddition

/-!
# Actual iota commutes with the genuine bounded SAME-value source return

The intermediate root supplies its actual returned original root, its high
caller and the SAME canonical target base. The original full beta cut gives
the returned source restriction. The proof then follows the real finite
return: low stops preserve their value, positive indices retain the recursive
argument, and actual addition is compared with the proved normal restricted
source sum. No normalization, root, admission or commutation oracle is used.
All statements concern the original checked Normal restricted domain.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.SourceReturn

open NativePublicBridge (contextCode)

/-- The actual addition code has the additive iota image. Both normal
presentations are constructed, and their equality follows from real order. -/
theorem addCode_transform (s r c d : Nat) (hr : Iota.rootCheck s r = true)
    (hc : Comparison.acceptedCode (contextCode s) c = true)
    (hd : Comparison.acceptedCode (contextCode s) d = true)
    (hrc : Iota.Restricted s r (ThetaCourse.rawTree c))
    (hrd : Iota.Restricted s r (ThetaCourse.rawTree d)) :
    denote (Iota.alphaCode s r)
        (Iota.transform s r (ThetaCourse.rawTree (Arithmetic.addCode (contextCode s) c d))) =
      denote (Iota.alphaCode s r) (Iota.transform s r (ThetaCourse.rawTree c)) +
        denote (Iota.alphaCode s r) (Iota.transform s r (ThetaCourse.rawTree d)) := by
  have hcc := (Comparison.acceptedCode_exact _ _).mp hc
  have hdc := (Comparison.acceptedCode_exact _ _).mp hd
  have hct := Decomposition.input_tree (contextCode s) c hc
  have hdt := Decomposition.input_tree (contextCode s) d hd
  have hs := Arithmetic.addCode_spec (contextCode s) c d hcc.1 hdc.1
  have hst := Decomposition.input_tree (contextCode s) _ hs.1
  have hsr : Iota.Restricted s r
      (ThetaCourse.rawTree (Arithmetic.addCode (contextCode s) c d)) :=
    ReturnSupport.addCode_fullBelow (contextCode s) c d
      (interpretation (contextCode s) r) hcc.1 hdc.1 hrc hrd
  have hn := Iota.Addition.sourceSum_spec s r hr _ _
    hct.1 hdt.1 hct.2 hdt.2 hrc hrd
  have hv : denote (contextCode s)
      (ThetaCourse.rawTree (Arithmetic.addCode (contextCode s) c d)) =
      denote (contextCode s) (Iota.Addition.sourceSum (contextCode s)
        (ThetaCourse.rawTree c) (ThetaCourse.rawTree d)) := by
    rw [Arithmetic.raw_value (contextCode s) _
      ((Comparison.acceptedCode_exact _ _).mp hs.1).1, hs.2.1,
      hn.2.2.2.1, Arithmetic.raw_value (contextCode s) c hcc.1,
      Arithmetic.raw_value (contextCode s) d hdc.1]
  have he := (Iota.transform_eq_iff s r hr _ _ hst.1 hn.1
    hst.2 hn.2.1 hsr hn.2.2.1).mpr hv
  exact he.trans hn.2.2.2.2

/-- The original input restriction supplies the actual returned-root
source-star domain, including all hidden zero-index calls. -/
theorem returnedTerm_restricted (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t) :
    Iota.Restricted s (returnedRoot s a root) (returnedTerm s a t) :=
  ReturnSupport.sourceTermCode_iota_restricted s a root (returnedRoot s a root) ha
    (returnedRoot_spec s a root ha).2.2 t ht hn hr

private theorem returnedTerm_theta_succ (s a k : Nat) (t : RelativeTerm Nat) :
    returnedTerm s a (.theta (k + 1) t) = .theta (k + 1) (returnedTerm s a t) := by
  have hk : (k + 1 == 0) = false := by simp
  simp only [returnedTerm, BoundedPublicReturn.sourceTermCode_theta,
    BoundedPublicReturn.thetaCode, hk, Bool.cond_false,
    BoundedPublicReturn.nodeCode, ThetaCourse.rawTree_code]

private theorem transform_return_below (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t)
    (hb : denote (sourceCode s a) t < interpretation (sourceCode s a) root) :
    denote (betaCode s a root) (Iota.transform s (returnedRoot s a root) (returnedTerm s a t)) =
      denote (betaCode s a root) (transform s a root t) := by
  have hs := returnedTerm_spec s a root ha t ht hn hr
  have hbr : denote (contextCode s) (returnedTerm s a t) <
      interpretation (contextCode s) (returnedRoot s a root) := by
    rw [hs.2.2, (returnedRoot_spec s a root ha).2.2]
    exact hb
  have ho := Iota.transform_parameter_value s (returnedRoot s a root)
    (returnedRoot_iota_caller s a root ha) _ hs.1 hbr
  rw [returnedRoot_alphaCode s a root ha] at ho
  have hi := transform_parameter_value s a root ha t ht hb
  exact ho.2.trans (hs.2.2.trans hi.2.symm)

/-- Genuine semantic commutation of BOTH actual iota transforms with the
actual finite SAME-value return, on the original restricted Normal domain. -/
theorem transform_return_value (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t) :
    denote (betaCode s a root) (Iota.transform s (returnedRoot s a root) (returnedTerm s a t)) =
      denote (betaCode s a root) (transform s a root t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hp := checked_parameters (sourceCode s a) (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact transform_return_below s a root ha (.parameter p) ht hn hr
      (hp.2.trans_le (root_base_le s a root ha))
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks (sourceCode s a) t u ht
    have hs := (restricted_sum s a root t u).mp hr
    have hct := sourceTermCode_spec s a root ha t hc.1 hn.1 hs.1
    have hcu := sourceTermCode_spec s a root ha u hc.2 hn.2.1 hs.2
    have ho := addCode_transform s (returnedRoot s a root) _ _
      (returnedRoot_iota_caller s a root ha) hct.1 hcu.1
      (returnedTerm_restricted s a root ha t hc.1 hn.1 hs.1)
      (returnedTerm_restricted s a root ha u hc.2 hn.2.1 hs.2)
    rw [returnedRoot_alphaCode s a root ha] at ho
    change denote (betaCode s a root)
      (Iota.transform s (returnedRoot s a root)
        (ThetaCourse.rawTree (BoundedPublicReturn.sourceTermCode s a (.sum t u)))) = _
    rw [BoundedPublicReturn.sourceTermCode_sum, ho,
      OrderSupport.transform_add s a root ha t u hc.1 hc.2,
      iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2]
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      exact transform_return_below s a root ha (.theta 0 t) ht hn hr
        ((restricted_theta_zero s a root t).mp hr).1
    | succ k =>
      have hc := BaseTransformation.theta_argument_check (sourceCode s a) (k + 1) t ht
      have hs := (restricted_theta_succ s a root k t).mp hr
      have hrt := returnedTerm_restricted s a root ha (.theta (k + 1) t) ht hn hr
      have hct := (returnedTerm_spec s a root ha (.theta (k + 1) t) ht hn hr).1
      rw [returnedTerm_theta_succ] at hct hrt ⊢
      rw [Iota.transform_theta_succ s (returnedRoot s a root) k
          (returnedRoot_iota_caller s a root ha) _ hct hrt,
        OrderSupport.transform_theta_succ s a root k ha t ht hr]
      change globalCollapse (base (betaCode s a root)) k
        (denote (betaCode s a root) (Iota.transform s (returnedRoot s a root) (returnedTerm s a t))) =
          globalCollapse (base (betaCode s a root)) k
            (denote (betaCode s a root) (transform s a root t))
      rw [ih hc hn hs]

/-- The actual returned finite tree has the original iota caller; no
returned source-star or admission premise is added to the input. -/
theorem returnedTerm_iota_caller (s a root : Nat) (ha : rootCheck s a root = true)
    (t : RelativeTerm Nat) (ht : check (sourceCode s a) t = true)
    (hn : Comparison.Normal (sourceCode s a) t) (hr : Restricted s a root t) :
    Iota.inputCheck s (returnedRoot s a root) (returnedTerm s a t).code = true := by
  have hs := returnedTerm_spec s a root ha t ht hn hr
  have hroot := returnedRoot_iota_caller s a root ha
  have hcut := returnedTerm_restricted s a root ha t ht hn hr
  exact (Iota.inputCheck_exact _ _ _).mpr ⟨hroot, returnedTerm s a t, rfl, hs.1, hs.2.1,
    (Iota.restricted_iff_sourceStar _ _ hroot _ hs.1 hs.2.1).mp hcut⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.SourceReturn
