import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuParameterSuccessor
import Alexander313.Wilken.HereditaryLowContextSuccessor

/-!
# Actual two-context presentations of a below-base mu parameter

The original mu guard and its below-root value branch construct the real
active-beta parameter code. A genuine original finite source theta term
of that value has an E1 base strictly below beta. For epsilon mu there is
also the concrete self-context theta_mu(0), with the actual E1 contexts
mu < beta. These are explicit parameter resolutions of the form described
by Definition3.39, independent of numerical canonical-code levels.

For non-epsilon mu every genuine lower theta presentation has the same
literal successor value, proved by the LOW successor theorem. For epsilon
mu this file supplies the actual self-context resolution and its successor;
it does not select that resolution as the printed parameter-plus convention
or equate it with a HIGH epsilon presentation. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ParameterSuccessor.Resolution

def activeParameterTerm (q root : Nat) : RelativeTerm Nat := .parameter (publicMu q root)

theorem activeParameterTerm_primrec : Primrec
    (fun p : Context => activeParameterTerm p.1 p.2) :=
  parameter_primrec.comp publicMu_primrec

/-- The below-root branch gives the actual admitted parameter in the
active beta context; no lower-context presentation is assumed. -/
theorem activeParameter_spec (q root : Nat) (ha : Mu.inputCheck q root = true)
    (hsmall : sourceValue q root < interpretation q root) :
    check (betaCode q root) (activeParameterTerm q root) = true ∧
      Comparison.Normal (betaCode q root) (activeParameterTerm q root) ∧
      denote (betaCode q root) (activeParameterTerm q root) = sourceValue q root := by
  have hp := publicMu_spec q root ha
  have hc : parameterCheck (betaCode q root) (publicMu q root) = true :=
    (parameterCheck_exact _ _).mpr ⟨Canonical.check_original hp.1,
      Canonical.check_original (betaCode_spec q root ha).1, by
        change unionInterpretation (publicMu q root) < base (betaCode q root)
        rw [hp.2, beta_base q root ha]
        exact hsmall⟩
  refine ⟨?_, trivial, ?_⟩
  · simp only [activeParameterTerm, check, betaCode_baseCheck q root ha,
      finiteCheck_parameter, hc, Bool.true_and]
  · exact hp.2

/-- The actual original finite source representation has a genuine
strictly smaller E1 context. The real source-zero dictionary is retained. -/
theorem original_lower_resolution (q root : Nat) (ha : Mu.inputCheck q root = true)
    (hsmall : sourceValue q root < interpretation q root) :
    ∃ b : RelativeTerm Nat,
      (finiteBase (PublicEpsilonSourceDictionary.level (publicMu q root)) = 1 ∨
        Ordinal.omega0 ^ finiteBase (PublicEpsilonSourceDictionary.level (publicMu q root)) =
          finiteBase (PublicEpsilonSourceDictionary.level (publicMu q root))) ∧
      finiteBase (PublicEpsilonSourceDictionary.level (publicMu q root)) < base (betaCode q root) ∧
      Hereditary.check (PublicEpsilonSourceDictionary.level (publicMu q root)) (.theta 0 b) = true ∧
      Theta.Normal (PublicEpsilonSourceDictionary.level (publicMu q root)) (.theta 0 b) ∧
      Hereditary.denote (PublicEpsilonSourceDictionary.level (publicMu q root)) (.theta 0 b) =
        denote (betaCode q root) (activeParameterTerm q root) := by
  have hp := publicMu_spec q root ha
  obtain ⟨b, _, hc, hn, hv⟩ := MuParameterSuccessor.principal_sourceTerm_spec (publicMu q root)
    hp.1 (publicMu_positive q root ha) (publicMu_principal q root ha)
  refine ⟨b, finiteBase_epsilon_or_one _, ?_, hc, hn, ?_⟩
  · rw [beta_base q root ha]
    exact (MuParameterSuccessor.principal_level_lower _ hp.1 (publicMu_positive q root ha)).trans_lt
      (hp.2.trans_lt hsmall)
  · exact hv.trans (hp.2.trans (activeParameter_spec q root ha hsmall).2.2.symm)

/-- The genuine epsilon self-context resolves the admitted active-beta
parameter by the concrete theta_mu(0) term, with strict E1 context order. -/
theorem epsilon_self_resolution (q root : Nat) (ha : Mu.inputCheck q root = true)
    (he : Ordinal.omega0 ^ sourceValue q root = sourceValue q root)
    (hsmall : sourceValue q root < interpretation q root) :
    baseCheck (publicMu q root) = true ∧
      base (publicMu q root) < base (betaCode q root) ∧
      check (betaCode q root) (activeParameterTerm q root) = true ∧
      check (publicMu q root) SourceChi.Powers.baseTree = true ∧
      denote (publicMu q root) SourceChi.Powers.baseTree =
        denote (betaCode q root) (activeParameterTerm q root) ∧
      denote (publicMu q root) (selfSuccessorTerm q root) =
        nextAdditivePrincipal (denote (betaCode q root) (activeParameterTerm q root)) ∧
      denote (publicMu q root) (selfSuccessorTerm q root) < interpretation q root := by
  have hs := epsilon_self_successor q root ha he hsmall
  have hp := publicMu_spec q root ha
  have ha' := activeParameter_spec q root ha hsmall
  refine ⟨hs.1, ?_, ha'.1, hs.2.1, hs.2.2.1.trans ha'.2.2.symm, ?_, hs.2.2.2.2.2.2⟩
  · change unionInterpretation (publicMu q root) < base (betaCode q root)
    rw [hp.2, beta_base q root ha]
    exact hsmall
  · have hx := NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm_spec (publicMu q root)
      Normalization.zeroTree hs.2.1
    rw [selfSuccessorTerm, hx.2.2.2, Normalization.zeroTree_denote, zero_add]
    change globalCollapse (unionInterpretation (publicMu q root)) 0 1 = _
    rw [hp.2, ha'.2.2]
    exact ParameterSuccessorBounds.LowContext.epsilon_self_successor_eq_next _ he

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ParameterSuccessor.Resolution
