import Alexander313.Wilken.SourceOneNativeMuBounds
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingMultiplicativePrefix

/-!
# A genuine original-source-one singleton-boundary candidate

The original check-zero high root constructs its same-value Delta carrier
in the actual epsilon alpha context. Every original zero node is stopped,
including nodes inside arguments, so the full native principal support of
the enclosure is a singleton. The real localization and complete assignment
therefore execute its literal singleton above BOTH the original root and
the original source-one mu. Native operations occur only at the genuine
epsilon alphaCode, never base one. No endpoint, support or singleton oracle.
This is a source-only uncompiled candidate, not an executing minimum.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.GammaHatSupport

open ThetaCourse OrderSupport Enclosure
open NativeContext.SourceMultiplicativeTracking
open NativeContext.SourceTrackingSequences (lastCode_singleton stripLast_singleton)

/-- The actual original restriction stops every source-zero node, including
hidden argument nodes, from the full native zero-level principal support. -/
theorem unshifted_principal_zero (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hr : Restricted a t) :
    RelativeTerm.PrincipalSupport.principalList 0 (unshifted a t) = [] := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, RelativeTerm.PrincipalSupport.principalList]
    | false =>
      simp only [unshifted, h, Bool.cond_false, RelativeTerm.PrincipalSupport.principalList,
        iht hc.1 hs.1, ihu hc.2 hs.2, List.nil_append]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [unshifted_below a ha _ ht ((restricted_theta_zero a t).mp hr).1]
      rfl
    | succ k =>
      rw [unshifted_theta_succ a k ha t ht hr,
        RelativeTerm.PrincipalSupport.principalList_theta_higher 0 (k + 1) _
          (Nat.zero_lt_succ k)]
      exact ih (argument_checked (k + 1) t ht) ((restricted_theta_succ a k t).mp hr)

def endpointCode (a : Nat) : Nat := (deltaEnclosureTerm a).code

theorem endpoint_node (a : Nat) (ha : rootCheck a = true) :
    NativeContext.SourceLocalization.Node (alphaCode a) (endpointCode a) := by
  have hs := delta_enclosure_spec a ha
  exact ⟨unshifted a (deltaTerm a), rfl, hs.1, hs.2.1⟩

theorem endpoint_value (a : Nat) (ha : rootCheck a = true) :
    NativeContext.interpretation (alphaCode a) (endpointCode a) = sourceAlphaPlus a := by
  simpa only [endpointCode, NativeContext.interpretation_code] using
    delta_enclosure_eq_sourceAlphaPlus a ha

theorem endpoint_support (a : Nat) (ha : rootCheck a = true) :
    NativeContext.SourceLocalization.support (endpointCode a) = [endpointCode a] := by
  have hc := Lambda.argument_accepted a ha
  have hp := (SourceDecomposition.parts_checked 0 0 (Lambda.argumentCode a) hc).1
  have hz := unshifted_principal_zero a ha (deltaTerm a) hp (Lambda.delta_restricted a ha)
  simp only [endpointCode, deltaEnclosureTerm, NativeContext.SourceLocalization.support,
    PrincipalSupport.listCode_code, RelativeTerm.PrincipalSupport.principalList_theta_same,
    hz, List.map_cons, List.map_nil]

/-- The actual finite walk uses the genuine base spelling and has no
intermediate zero-level node before the real original successor enclosure. -/
theorem endpoint_path (a : Nat) (ha : rootCheck a = true) :
    NativeContext.SourceLocalization.nativePath (alphaCode a) (endpointCode a) =
      [NativeContext.SourceLocalization.baseRaw (alphaCode a), endpointCode a] := by
  have hn := endpoint_node a ha
  have hq := alphaCode_baseCheck a ha
  have hb : NativeContext.SourceLocalization.value (alphaCode a)
      (NativeContext.SourceLocalization.baseRaw (alphaCode a)) <
        NativeContext.SourceLocalization.value (alphaCode a) (endpointCode a) := by
    rw [NativeContext.SourceLocalization.baseRaw_value _ hq,
      NativeContext.SourceLocalization.value, endpoint_value a ha, alpha_base a ha,
      ← delta_enclosure_eq_sourceAlphaPlus a ha]
    exact (delta_enclosure_spec a ha).2.2.2
  have hl := (NativeContext.SourceLocalization.value_less_exact _ _ _
    (NativeContext.SourceLocalization.baseRaw_node _ hq) hn).mpr hb
  rw [NativeContext.SourceLocalization.nativePath, endpoint_support a ha]
  simp only [List.length_singleton, NativeContext.SourceLocalization.live, hl, Bool.cond_true,
    NativeContext.SourceLocalization.walk_succ, NativeContext.SourceLocalization.best,
    NativeContext.SourceLocalization.choose, NativeContext.SourceLocalization.walk_zero]

theorem endpoint_properPrefix (a : Nat) (ha : rootCheck a = true) :
    properPrefix (alphaCode a) (endpointCode a) = [] := by
  simp only [properPrefix, endpoint_path a ha, List.tail_cons, stripLast_singleton]

theorem endpoint_word (a : Nat) (ha : rootCheck a = true) :
    word (alphaCode a) (endpointCode a) = [endpointCode a] := by
  simp only [word, endpoint_properPrefix a ha, Support.table, List.reverse_nil,
    Support.buildRev, Support.extend, Support.select]

theorem endpoint_multiplicative (a : Nat) (ha : rootCheck a = true) :
    NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) (endpointCode a) = true := by
  have hl := NativeContext.SourceLocalization.node_low _ _ (endpoint_node a ha)
  have hb : NativeContext.base (alphaCode a) ≤
      NativeContext.interpretation (alphaCode a) (endpointCode a) := by
    rw [alpha_base a ha, endpoint_value a ha, ← delta_enclosure_eq_sourceAlphaPlus a ha]
    exact (delta_enclosure_spec a ha).2.2.2.le
  apply (NativeContext.SourceMultiplicativePrincipal.inputCheck_exact _ _).mpr
  exact ⟨hl, hb, NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _
    (by rw [endpoint_value a ha]; exact Mu.Bounds.source_alphaPlus_epsilon a ha)⟩

/-- The real raw M procedure retains its literal final input, so its
computed VALUE singleton is already the literal singleton enclosure code. -/
theorem endpoint_rawWord (a : Nat) (ha : rootCheck a = true) :
    rawWord (alphaCode a) (endpointCode a) = [endpointCode a] := by
  have hi := (NativeContext.SourceLocalization.inputCheck_exact _ _).mpr (endpoint_node a ha)
  have hv := RawRecurrence.rawWord_values_word _ _ hi
  rw [endpoint_word a ha, List.map_cons, List.map_nil] at hv
  obtain ⟨c, he, _⟩ := List.map_eq_singleton_iff.mp hv
  have heq : c = endpointCode a := by
    simpa only [he, lastCode_singleton] using rawWord_last (alphaCode a) (endpointCode a)
  simpa only [heq] using he

/-- The actual original source-one root supplies a complete singleton
assignment candidate above both itself and its actual original mu. -/
theorem endpoint_candidate (a : Nat) (ha : rootCheck a = true) :
    NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) (endpointCode a) = true ∧
      [endpointCode a] ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
        (alphaCode a) (endpointCode a) ∧
      interpretation 0 a < NativeContext.interpretation (alphaCode a) (endpointCode a) ∧
      Mu.sourceValue a < NativeContext.interpretation (alphaCode a) (endpointCode a) := by
  refine ⟨endpoint_multiplicative a ha, ?_, ?_, ?_⟩
  · rw [← endpoint_rawWord a ha]
    exact NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ _
      (endpoint_multiplicative a ha)
  · rw [endpoint_value a ha, ← delta_enclosure_eq_sourceAlphaPlus a ha]
    exact (delta_enclosure_spec a ha).2.2.2
  · rw [endpoint_value a ha, ← (Mu.muCode_spec a ha).2.2]
    exact Mu.Bounds.muCode_lt_source_alphaPlus a ha

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.GammaHatSupport
