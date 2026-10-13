import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSuccessorIntervals
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingMultiplicativePrefix

/-!
# A genuine singleton candidate for the source connectivity boundary

The original high root alone constructs its real source argument successor
at the actual root context. Its same-value Delta carrier has no full
zero-level principal support, so the genuine finite localization has no
proper intermediate node. The independently executing full assignment
therefore returns the literal singleton endpoint, above both the original
root and its actual mu. No singleton, endpoint or localization is supplied.
This proves a candidate for Definition3.30, not a computed least boundary.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.GammaHatSupport

open ThetaCourse Enclosure
open SourceMultiplicativeTracking
open SourceTrackingSequences (lastCode lastCode_singleton stripLast_singleton)

/-- The genuine same-value carrier stops every original zero node, even
inside arguments. Thus its full principal support, not merely its exposed
support, contains no zero-level node. -/
theorem unshifted_principal_zero (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hr : Restricted q root t) :
    RelativeTerm.PrincipalSupport.principalList 0 (unshifted q root t) = [] := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hs := (restricted_sum q root t u).mp hr
    cases h : small q root (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, RelativeTerm.PrincipalSupport.principalList]
    | false =>
      simp only [unshifted, h, Bool.cond_false, RelativeTerm.PrincipalSupport.principalList,
        iht hc.1 hs.1, ihu hc.2 hs.2, List.nil_append]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [unshifted_below q root ha _ ht ((restricted_theta_zero q root t).mp hr).1]
      rfl
    | succ k =>
      rw [unshifted_theta_succ q root k ha t ht hr,
        RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) _
          (Nat.zero_lt_succ k)]
      exact ih (BaseTransformation.theta_argument_check q (k + 1) t ht)
        ((restricted_theta_succ q root k t).mp hr)

def endpointCode (q root : Nat) : Nat := (deltaEnclosureTerm q root).code

theorem endpoint_node (q root : Nat) (ha : rootCheck q root = true) :
    SourceLocalization.Node (betaCode q root) (endpointCode q root) := by
  have hs := delta_enclosure_spec q root ha
  exact ⟨unshifted q root (deltaTerm root), rfl, hs.1, hs.2.1⟩

theorem endpoint_value (q root : Nat) (ha : rootCheck q root = true) :
    interpretation (betaCode q root) (endpointCode q root) = sourceAlphaPlus q root :=
  (delta_enclosure_code_spec q root ha).2.2

theorem endpoint_support (q root : Nat) (ha : rootCheck q root = true) :
    SourceLocalization.support (endpointCode q root) = [endpointCode q root] := by
  have hd := delta_original q root ha
  have hz := unshifted_principal_zero q root ha (deltaTerm root) hd.1 hd.2.2
  simp only [endpointCode, deltaEnclosureTerm, SourceLocalization.support,
    PrincipalSupport.listCode_code, RelativeTerm.PrincipalSupport.principalList_theta_same,
    hz, List.map_cons, List.map_nil]

/-- The actual finite walk, starting at its genuine base spelling, has
exactly its original base and the source successor endpoint. -/
theorem endpoint_path (q root : Nat) (ha : rootCheck q root = true) :
    SourceLocalization.nativePath (betaCode q root) (endpointCode q root) =
      [SourceLocalization.baseRaw (betaCode q root), endpointCode q root] := by
  have hn := endpoint_node q root ha
  have hq := betaCode_baseCheck q root ha
  have hb : SourceLocalization.value (betaCode q root)
      (SourceLocalization.baseRaw (betaCode q root)) <
        SourceLocalization.value (betaCode q root) (endpointCode q root) := by
    rw [SourceLocalization.baseRaw_value _ hq, SourceLocalization.value, endpoint_value q root ha,
      beta_base q root ha]
    rw [← delta_enclosure_value q root ha]
    exact root_lt_enclosure q root ha
  have hl := (SourceLocalization.value_less_exact _ _ _
    (SourceLocalization.baseRaw_node _ hq) hn).mpr hb
  rw [SourceLocalization.nativePath, endpoint_support q root ha]
  simp only [List.length_singleton, SourceLocalization.live, hl, Bool.cond_true,
    SourceLocalization.walk_succ, SourceLocalization.best, SourceLocalization.choose,
    SourceLocalization.walk_zero]

theorem endpoint_properPrefix (q root : Nat) (ha : rootCheck q root = true) :
    properPrefix (betaCode q root) (endpointCode q root) = [] := by
  simp only [properPrefix, endpoint_path q root ha, List.tail_cons, stripLast_singleton]

theorem endpoint_word (q root : Nat) (ha : rootCheck q root = true) :
    word (betaCode q root) (endpointCode q root) = [endpointCode q root] := by
  simp only [word, endpoint_properPrefix q root ha, Support.table, List.reverse_nil,
    Support.buildRev, Support.extend, Support.select]

theorem endpoint_multiplicative (q root : Nat) (ha : rootCheck q root = true) :
    SourceMultiplicativePrincipal.inputCheck (betaCode q root) (endpointCode q root) = true := by
  have hl := (delta_enclosure_code_spec q root ha).1
  have hb : base (betaCode q root) ≤ interpretation (betaCode q root) (endpointCode q root) := by
    rw [beta_base q root ha, endpoint_value q root ha, ← delta_enclosure_value q root ha]
    exact (root_lt_enclosure q root ha).le
  apply (SourceMultiplicativePrincipal.inputCheck_exact _ _).mpr
  exact ⟨hl, hb, SourceMultiplicativePrincipal.epsilon_multiplicative _
    (by rw [endpoint_value q root ha]; exact sourceAlphaPlus_epsilon q root ha)⟩

/-- The raw M procedure keeps its literal final input. Its independently
localized VALUE singleton therefore forces the actual literal singleton. -/
theorem endpoint_rawWord (q root : Nat) (ha : rootCheck q root = true) :
    rawWord (betaCode q root) (endpointCode q root) = [endpointCode q root] := by
  have hi := (SourceLocalization.inputCheck_exact _ _).mpr (endpoint_node q root ha)
  have hv := RawRecurrence.rawWord_values_word _ _ hi
  rw [endpoint_word q root ha, List.map_cons, List.map_nil] at hv
  obtain ⟨a, he, _⟩ := List.map_eq_singleton_iff.mp hv
  have haeq : a = endpointCode q root := by
    simpa only [he, lastCode_singleton] using rawWord_last (betaCode q root) (endpointCode q root)
  simpa only [haeq] using he

/-- The full independently executing native assignment gives a genuine
Definition3.30 singleton candidate strictly above BOTH gamma and mu_gamma. -/
theorem endpoint_candidate (q root : Nat) (ha : rootCheck q root = true) :
    SourceMultiplicativePrincipal.inputCheck (betaCode q root) (endpointCode q root) = true ∧
      [endpointCode q root] ∈ SourceAdditiveTracking.Assignment.execute
        (betaCode q root) (endpointCode q root) ∧
      interpretation q root < interpretation (betaCode q root) (endpointCode q root) ∧
      Mu.sourceValue q root < interpretation (betaCode q root) (endpointCode q root) := by
  refine ⟨endpoint_multiplicative q root ha, ?_, ?_, ?_⟩
  · rw [← endpoint_rawWord q root ha]
    exact SourceAdditiveTracking.Assignment.execute_multiplicative _ _ (endpoint_multiplicative q root ha)
  · rw [endpoint_value q root ha, ← delta_enclosure_value q root ha]
    exact root_lt_enclosure q root ha
  · rw [endpoint_value q root ha, ← (Mu.muCode_spec q root ha).2.2]
    exact Mu.SuccessorIntervals.muCode_lt_sourceAlphaPlus q root ha

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.GammaHatSupport
