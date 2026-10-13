import Alexander313.Wilken.PublicEpsilonNativeOmegaQuotientBaseChangeSupport

/-!
# Original chosen-Par transport of the actual Omega-one coefficient

Original source admission and the chosen-presentation Par cutoff construct
the smaller-context argument caller. The actual full ANF quotient produces
the SAME coefficient word and finite unit count; its full hidden smaller
payload cutoff is proved from the genuine target operations. Thus the real
coefficient pi caller and numerical equation are derived. The separate
generic target-root endpoint is retained explicitly where its guarded
producer is invoked. No target iota Par claim or mu3.9 oracle is assumed.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.OmegaQuotient.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)
open BoundedContextIota.OmegaQuotient (limitTerm finiteOffset)

theorem argument_target_accepted (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hp : ParBounded q v (rawTree root)) :
    Decomposition.inputCheck v (argumentCode root) = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (PublicEpsilonIota.rootCheck_exact q root).mp ha
  have htarget := OmegaPowers.BaseChange.target_low q v root (PublicEpsilonIota.root_low q root ha) hv hp
  have hvt : check v (.theta 0 t) = true := by
    simpa only [he, checkCode_code] using (Bool.and_eq_true.mp htarget).1
  have hcq := BaseTransformation.theta_argument_check q 0 t ht
  have hcv := BaseTransformation.theta_argument_check v 0 t hvt
  apply (Decomposition.inputCheck_exact v _).mpr
  exact ⟨by simpa only [argumentCode, he, Localization.argumentCode_theta, checkCode_code] using hcv,
    by simpa only [argumentCode, he, Localization.argumentCode_theta, rawTree_code] using
      (BaseTransformation.normal_context q v t hcq hcv).mp hn⟩

/-- The coefficient branch kernel uses no generic target endpoint or
target root oracle: its original argument is actually checked there. -/
theorem coefficient_literal_context (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hp : ParBounded q v (rawTree root)) :
    coefficientCode q root = (limitTerm v (argumentCode root)).code ∧
      coefficientOffset q root = finiteOffset v (argumentCode root) := by
  have hcq := Support.argument_accepted q root ha
  have hcv := argument_target_accepted q v root ha hv hp
  rw [coefficientCode_literal q root ha, coefficientOffset_literal q root ha,
    limitTerm_context q v _ hcq hcv, finiteOffset_context q v _ hcq hcv]
  exact ⟨rfl, rfl⟩

theorem coefficient_payloads (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hp : ParBounded q v (rawTree root)) :
    Payloads v (rawTree (coefficientCode q root)) := by
  rw [(coefficient_literal_context q v root ha hv hp).1, rawTree_code]
  exact limitTerm_payloads v _ (argument_target_accepted q v root ha hv hp)

theorem coefficient_parBounded (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (coefficientCode q root)) := by
  have hcheck := ((Comparison.acceptedCode_exact q _).mp (coefficientCode_accepted q root ha)).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q _ hcheck) hv).mpr
    (coefficient_payloads q v root ha hv hp)

theorem coefficient_pi_caller (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hl : base v < base q) (hp : ParBounded q v (rawTree root)) :
    BaseTransformation.inputCheck q v (coefficientCode q root) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp (coefficientCode_accepted q root ha)).1,
      hv, hl, coefficient_parBounded q v root ha hv hp⟩

/-- The generic target guard is derived from original Par admission and
the honest selected target endpoint. This endpoint is not inferred from
the unrelated original source endpoint. -/
theorem target_root (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hcanonical : Canonical.check v = true)
    (hp : ParBounded q v (rawTree root))
    (hb : interpretation v root < PublicEpsilonSourceDictionary.Return.endpoint v) :
    PublicEpsilonIota.rootCheck v root = true := by
  obtain ⟨_, ⟨t, he, ht, hn, hh⟩, _⟩ := (PublicEpsilonIota.rootCheck_exact q root).mp ha
  have htarget := OmegaPowers.BaseChange.target_low q v root (PublicEpsilonIota.root_low q root ha) hv hp
  have hvt : check v (.theta 0 t) = true := by
    simpa only [he, checkCode_code] using (Bool.and_eq_true.mp htarget).1
  have hcq := BaseTransformation.theta_argument_check q 0 t ht
  have hcv := BaseTransformation.theta_argument_check v 0 t hvt
  have hd := (PublicEpsilonSourceDictionary.inputCheck_exact v).mpr
    ⟨hcanonical, by simpa only [base] using ((baseCheck_exact v).mp hv).2⟩
  exact (PublicEpsilonIota.rootCheck_exact v root).mpr
    ⟨hd, ⟨t, he, hvt, (BaseTransformation.normal_context q v t hcq hcv).mp hn, hh⟩, hb⟩

/-- Both actual guarded coefficient producers agree literally once the
real selected target endpoint has supplied its genuinely derived caller. -/
theorem coefficientCode_change (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hcanonical : Canonical.check v = true)
    (hp : ParBounded q v (rawTree root))
    (hb : interpretation v root < PublicEpsilonSourceDictionary.Return.endpoint v) :
    coefficientCode q root = coefficientCode v root ∧
      coefficientOffset q root = coefficientOffset v root := by
  have hs := coefficient_literal_context q v root ha hv hp
  have hroot := target_root q v root ha hv hcanonical hp hb
  rw [coefficientCode_literal v root hroot, coefficientOffset_literal v root hroot]
  exact hs

theorem piCode_coefficientCode (q v root : Nat)
    (ha : PublicEpsilonIota.rootCheck q root = true) (hv : baseCheck v = true)
    (hcanonical : Canonical.check v = true)
    (hl : base v < base q) (hp : ParBounded q v (rawTree root))
    (hb : interpretation v root < PublicEpsilonSourceDictionary.Return.endpoint v) :
    BaseTransformation.piCode q v (coefficientCode q root) = coefficientCode v root := by
  rw [BaseTransformation.piCode_eq q v _ (coefficient_pi_caller q v root ha hv hl hp)]
  exact (coefficientCode_change q v root ha hv hcanonical hp hb).1

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.OmegaQuotient.BaseChange
