import Alexander313.Wilken.PublicEpsilonNativeContextReturnSupport

/-!
# Genuine iota commutation through the semantic context return

The returned original source root is constructed by the real last-atom
parser from the genuine finite SAME-value return. Its high-root admission
and literal canonical beta spelling are derived. Actual normalized q
addition is compared with the genuine normal restricted source sum using
full original iota order. This yields semantic iota commutation on EVERY
original Normal beta-restricted alpha-context tree. No root, normalization,
restriction or transform equality is assumed. The return uses classical
finite parameter witnesses only; no executing reverse producer is claimed.
Full mu fidelity still needs the actual returned-root coefficient theorem.
Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.Return

open ThetaCourse
open PublicEpsilonUnboundedIota
open ReturnSupport (returnedCode returnedTerm returnedCode_spec returnedTerm_spec)

noncomputable def returnedRoot (q alpha beta : Nat) : Nat :=
  Support.rootAtomCode q (returnedCode q alpha (rawTree beta))

/-- The actual parsed source return has genuine high-root admission and
the SAME original alpha-context beta value; no root caller is provided. -/
theorem returnedRoot_spec (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true) :
    RootLowCollapse.rootCheck q (returnedRoot q alpha beta) = true ∧
      interpretation q (returnedRoot q alpha beta) = interpretation (betaCode q alpha) beta := by
  have hbc := RootLowCollapse.root_original (betaCode q alpha) beta hb
  have hs := returnedCode_spec q alpha ha (rawTree beta)
    (Arithmetic.raw_checked _ _ hbc)
  have hv : interpretation q (returnedCode q alpha (rawTree beta)) =
      interpretation (betaCode q alpha) beta := hs.2.trans (Arithmetic.raw_value _ _ hbc)
  have hl : lowCheckCode q (returnedCode q alpha (rawTree beta)) = true := by
    apply OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp hs.1).1
    rw [hv, RootPositiveCollapse.root_omegaSequence_pos q alpha 1 ha (by omega),
      ← beta_base q alpha ha]
    exact RootLowCollapse.root_lt_first _ _ hb
  have hp : base q < interpretation q (returnedCode q alpha (rawTree beta)) := by
    rw [hv]
    exact (root_base_lt q alpha ha).trans (by
      rw [← beta_base q alpha ha]
      exact root_base_lt _ _ hb)
  have he : Ordinal.omega0 ^ interpretation q (returnedCode q alpha (rawTree beta)) =
      interpretation q (returnedCode q alpha (rawTree beta)) := by
    rw [hv]
    exact RootLowCollapse.root_epsilon _ _ hb
  have hr := Support.rootAtomCode_spec q _ hl hp he
  exact ⟨hr.1, hr.2.trans hv⟩

theorem returnedRoot_betaCode (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true) :
    betaCode q (returnedRoot q alpha beta) = betaCode (betaCode q alpha) beta := by
  have hr := returnedRoot_spec q alpha beta ha hb
  exact UniformPublicReturn.publicCode_value_invariant q (betaCode q alpha) _ beta
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low q _ hr.1))
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low _ _ hb)) hr.2

theorem returnedTerm_restricted (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (hn : Comparison.Normal (betaCode q alpha) t) (hcut : Restricted (betaCode q alpha) beta t) :
    Restricted q (returnedRoot q alpha beta) (returnedTerm q alpha t) := by
  change ∀ u ∈ fullList (returnedTerm q alpha t), denote q u < interpretation q _
  rw [(returnedRoot_spec q alpha beta ha hb).2]
  exact ReturnSupport.returnedTerm_restricted q alpha beta ha hb t ht hn hcut

/-- Genuine ordinal addition in the source and its iota image. Actual
normalization is compared with the real normal restricted sum, not assumed
to commute with iota. -/
theorem addCode_transform (q beta c d : Nat) (hb : rootCheck q beta = true)
    (hc : Comparison.acceptedCode q c = true) (hd : Comparison.acceptedCode q d = true)
    (hrc : Restricted q beta (rawTree c)) (hrd : Restricted q beta (rawTree d)) :
    denote (betaCode q beta) (transform q beta (rawTree (Arithmetic.addCode q c d))) =
      denote (betaCode q beta) (transform q beta (rawTree c)) +
        denote (betaCode q beta) (transform q beta (rawTree d)) := by
  have hcc := (Comparison.acceptedCode_exact q c).mp hc
  have hdc := (Comparison.acceptedCode_exact q d).mp hd
  have hct := Decomposition.input_tree q c hc
  have hdt := Decomposition.input_tree q d hd
  have hs := Arithmetic.addCode_spec q c d hcc.1 hdc.1
  have hst := Decomposition.input_tree q _ hs.1
  have hsr : Restricted q beta (rawTree (Arithmetic.addCode q c d)) :=
    BoundedContextIota.ReturnSupport.addCode_fullBelow q c d (interpretation q beta)
      hcc.1 hdc.1 hrc hrd
  have hn := Addition.sourceSum_spec q beta hb _ _ hct.1 hdt.1 hct.2 hdt.2 hrc hrd
  have hv : denote q (rawTree (Arithmetic.addCode q c d)) =
      denote q (Addition.sourceSum q (rawTree c) (rawTree d)) := by
    rw [Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp hs.1).1,
      hs.2.1, hn.2.2.2.1, Arithmetic.raw_value q c hcc.1, Arithmetic.raw_value q d hdc.1]
  exact ((transform_eq_iff q beta hb _ _ hst.1 hn.1 hst.2 hn.2.1 hsr hn.2.2.1).mpr hv).trans
    hn.2.2.2.2

private theorem transform_return_below (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (hbelow : denote (betaCode q alpha) t < interpretation (betaCode q alpha) beta) :
    denote (betaCode (betaCode q alpha) beta)
        (transform q (returnedRoot q alpha beta) (returnedTerm q alpha t)) =
      denote (betaCode (betaCode q alpha) beta) (transform (betaCode q alpha) beta t) := by
  have hs := returnedTerm_spec q alpha ha t ht
  have hr := returnedRoot_spec q alpha beta ha hb
  have hv : denote q (returnedTerm q alpha t) < interpretation q (returnedRoot q alpha beta) := by
    rw [hs.2.2, hr.2]
    exact hbelow
  have ho := transform_parameter_value q _ hr.1 _ hs.1 hv
  rw [returnedRoot_betaCode q alpha beta ha hb] at ho
  exact ho.2.trans (hs.2.2.trans (transform_parameter_value _ beta hb t ht hbelow).2.symm)

/-- Both genuine iota transforms commute semantically with the actual
finite SAME-value return, on the entire original Normal restricted domain. -/
theorem transform_return_value (q alpha beta : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true)
    (hb : RootLowCollapse.rootCheck (betaCode q alpha) beta = true)
    (t : RelativeTerm Nat) (ht : check (betaCode q alpha) t = true)
    (hn : Comparison.Normal (betaCode q alpha) t) (hcut : Restricted (betaCode q alpha) beta t) :
    denote (betaCode (betaCode q alpha) beta)
        (transform q (returnedRoot q alpha beta) (returnedTerm q alpha t)) =
      denote (betaCode (betaCode q alpha) beta) (transform (betaCode q alpha) beta t) := by
  revert ht hn hcut
  induction t with
  | parameter p =>
    intro ht hn hcut
    have hp := checked_parameters _ (.parameter p) ht p (by simp [RelativeTerm.parameters])
    exact transform_return_below q alpha beta ha hb (.parameter p) ht
      (hp.2.trans_le (root_base_le _ _ hb))
  | sum t u iht ihu =>
    intro ht hn hcut
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum _ beta t u).mp hcut
    have hct := returnedCode_spec q alpha ha t hc.1
    have hcu := returnedCode_spec q alpha ha u hc.2
    have ho := addCode_transform q (returnedRoot q alpha beta) _ _
      (returnedRoot_spec q alpha beta ha hb).1 hct.1 hcu.1
      (returnedTerm_restricted q alpha beta ha hb t hc.1 hn.1 hs.1)
      (returnedTerm_restricted q alpha beta ha hb u hc.2 hn.2.1 hs.2)
    rw [returnedRoot_betaCode q alpha beta ha hb] at ho
    change denote (betaCode (betaCode q alpha) beta)
      (transform q (returnedRoot q alpha beta)
        (rawTree (Arithmetic.addCode q (returnedCode q alpha t) (returnedCode q alpha u)))) = _
    rw [ho, OrderSupport.transform_add _ beta hb t u hc.1 hc.2,
      iht hc.1 hn.1 hs.1, ihu hc.2 hn.2.1 hs.2]
  | theta k t ih =>
    intro ht hn hcut
    cases k with
    | zero =>
      exact transform_return_below q alpha beta ha hb (.theta 0 t) ht
        ((restricted_theta_zero _ beta t).mp hcut).1
    | succ k =>
      have hc := BaseTransformation.theta_argument_check _ (k + 1) t ht
      have hs := (restricted_theta_succ _ beta k t).mp hcut
      have hrt := returnedTerm_restricted q alpha beta ha hb (.theta (k + 1) t) ht hn hcut
      have hct := (returnedTerm_spec q alpha ha (.theta (k + 1) t) ht).1
      rw [ReturnSupport.returnedTerm_theta_succ] at hct hrt ⊢
      rw [OrderSupport.transform_theta_succ q (returnedRoot q alpha beta) k
          (returnedRoot_spec q alpha beta ha hb).1 _ hct hrt,
        OrderSupport.transform_theta_succ _ beta k hb t ht hcut]
      rw [returnedRoot_betaCode q alpha beta ha hb]
      change globalCollapse (base (betaCode (betaCode q alpha) beta)) k
        (denote (betaCode (betaCode q alpha) beta)
          (transform q (returnedRoot q alpha beta) (returnedTerm q alpha t))) =
        globalCollapse (base (betaCode (betaCode q alpha) beta)) k
          (denote (betaCode (betaCode q alpha) beta) (transform (betaCode q alpha) beta t))
      rw [ih hc hn hs]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ContextTranslation.Return
