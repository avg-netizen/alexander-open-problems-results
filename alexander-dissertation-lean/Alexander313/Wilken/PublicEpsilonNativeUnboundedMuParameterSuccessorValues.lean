import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuParameterSuccessor
import Alexander313.Wilken.HereditaryLowContextSuccessor

/-!
# Value of the actual computed lower-context mu successor

The genuine original hereditary theta argument-plus-one operation has the
existing next additive principal value whenever its root is non-epsilon.
This includes source level zero and does not assume a selected lower
context. The concrete lower successor of an originally admitted mu has
that value as well. Together with its actual epsilon ceiling bound, this
identifies the numerical value without defining a parameter-plus operation
or choosing a HIGH epsilon presentation. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuParameterSuccessor.Values

theorem sourceSuccessorTerm_value_eq_next (r : Nat) (b : RelativeTerm Nat)
    (ht : check r (.theta 0 b) = true)
    (hne : Ordinal.omega0 ^ denote r (.theta 0 b) ≠ denote r (.theta 0 b)) :
    denote r (sourceSuccessorTerm r b) = nextAdditivePrincipal (denote r (.theta 0 b)) := by
  have hb := SourceFixedPoint.checked_theta_argument r 0 b ht
  have hlo := ParameterSuccessorBounds.non_epsilon_argument_low (finiteBase r)
    (finiteBase_epsilon_or_one r) (SourceFixedPoint.sourceOrdinal r 0 b hb)
    (SourceFixedPoint.checked_theta_sort r 0 b ht) hne
  rw [(sourceSuccessorTerm_spec r b ht).2.2.2]
  exact ParameterSuccessorBounds.LowContext.low_collapse_successor_eq_next (finiteBase r)
    (finiteBase_epsilon_or_one r) (denote r b) hlo

end Alexander313.Wilken.RelativeTerm.Hereditary.MuParameterSuccessor.Values

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ParameterSuccessor.Values

/-- The actual computed lower-context successor value follows from the
original mu guard alone and the genuine non-epsilon branch. -/
theorem non_epsilon_lower_successor_value (q root : Nat)
    (ha : Mu.inputCheck q root = true)
    (hne : Ordinal.omega0 ^ sourceValue q root ≠ sourceValue q root) :
    Hereditary.denote (PublicEpsilonSourceDictionary.level (publicMu q root))
      (lowerSuccessorTerm q root) = nextAdditivePrincipal (sourceValue q root) := by
  let p := publicMu q root
  let r := PublicEpsilonSourceDictionary.level p
  have hp := publicMu_spec q root ha
  obtain ⟨b, hb, hc, hn, hv⟩ := MuParameterSuccessor.principal_sourceTerm_spec p hp.1
    (publicMu_positive q root ha) (publicMu_principal q root ha)
  have hcode : lowerSuccessorTerm q root = MuParameterSuccessor.sourceSuccessorTerm r b := by
    change MuParameterSuccessor.sourceSuccessorTerm r
      (ThetaCourse.rawTree (Localization.argumentCode (PublicEpsilonSourceDictionary.sourceTerm p).code)) = _
    rw [hb, Localization.argumentCode_theta, ThetaCourse.rawTree_code]
  have hvalue : Hereditary.denote r (.theta 0 b) = sourceValue q root := hv.trans hp.2
  rw [hcode, MuParameterSuccessor.Values.sourceSuccessorTerm_value_eq_next r b hc
    (by rw [hvalue]; exact hne), hvalue]

/-- The actual lower successor and its existing value operation share the
strict epsilon ceiling from the original root. -/
theorem non_epsilon_next_interval (q root : Nat) (ha : Mu.inputCheck q root = true)
    (hne : Ordinal.omega0 ^ sourceValue q root ≠ sourceValue q root)
    (hsmall : sourceValue q root < interpretation q root) :
    sourceValue q root < nextAdditivePrincipal (sourceValue q root) ∧
      nextAdditivePrincipal (sourceValue q root) < interpretation q root := by
  have hs := non_epsilon_lower_successor q root ha hne hsmall
  rw [non_epsilon_lower_successor_value q root ha hne] at hs
  exact hs.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ParameterSuccessor.Values
