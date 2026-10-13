import Alexander313.Wilken.PublicEpsilonNativeSkIteration
import Alexander313.Wilken.PublicEpsilonNativeContextMuInvariance
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSuccessorIntervals

/-!
# Genuine original-source provenance for a continuing sk next root

An actual true next flag supplies an admitted HIGH root at the current
root's genuine context. Its value is at most current mu, hence below the
original source successor endpoint. Actual context return and contextual
mu fidelity therefore supply an original-source HIGH representative with
the same value, canonical beta spelling and next mu. The more general
form retains an already derived original-source current representative and
its actual mu equality, so it can be iterated along the finite native Path.
No endpoint, next representative or mu equality is supplied in the direct
step theorem. This is semantic provenance; an executing flat-word search
consumer remains separate. Uncompiled source candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkContextFidelity

theorem betaCode_eq_of_value_eq (q root r current : Nat)
    (ha : Mu.inputCheck q root = true) (hc : Mu.inputCheck r current = true)
    (hv : interpretation q root = interpretation r current) :
    betaCode q root = betaCode r current :=
  UniformPublicReturn.publicCode_value_invariant q r root current
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low q root ha))
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low r current hc)) hv

theorem mu_lt_sourceAlphaPlus (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Mu.sourceValue q root < Enclosure.sourceAlphaPlus q root := by
  have hs := Mu.SuccessorIntervals.muCode_lt_sourceAlphaPlus q root ha
  rw [(Mu.muCode_spec q root ha).2.2] at hs
  exact hs

/-- An already derived original-q current representative transports every
actual continuing next root back to that SAME original source. The new
interval bound, representative, canonical base and next-mu equality are
all conclusions. -/
theorem continued_source (q root r current cutoff : Nat) (out : SkNextSearch.Step)
    (ha : Mu.inputCheck q root = true)
    (ho : out ∈ SkNextSearch.execute ((r, current), cutoff)) (hh : out.1 = true)
    (hv : interpretation q root = interpretation r current)
    (hm : Mu.sourceValue q root = Mu.sourceValue r current) :
    Mu.inputCheck q (ContextTranslation.Return.returnedRoot q root out.2) = true ∧
      interpretation q (ContextTranslation.Return.returnedRoot q root out.2) =
        interpretation (betaCode r current) out.2 ∧
      betaCode q (ContextTranslation.Return.returnedRoot q root out.2) =
        betaCode (betaCode r current) out.2 ∧
      Mu.sourceValue q (ContextTranslation.Return.returnedRoot q root out.2) =
        Mu.sourceValue (betaCode r current) out.2 ∧
      interpretation (betaCode r current) out.2 < Enclosure.sourceAlphaPlus q root := by
  have hs := SkNextSearch.execute_spec r current cutoff out ho
  have hc := ((SkNextSearch.inputCheck_exact r current cutoff).mp hs.1).1
  have hn := (SkNextSearch.execute_continue r current cutoff out ho hh).1
  have hbase := betaCode_eq_of_value_eq q root r current ha hc hv
  have hnext : Mu.inputCheck (betaCode q root) out.2 = true := by rw [hbase]; exact hn
  have hbound : interpretation (betaCode r current) out.2 < Enclosure.sourceAlphaPlus q root := by
    have hle : interpretation (betaCode r current) out.2 ≤ Mu.sourceValue q root := by
      rw [hm, hs.2.2.2.1]
      exact SkNextStep.nextValue_le_mu r current (unionInterpretation cutoff)
    exact hle.trans_lt (mu_lt_sourceAlphaPlus q root ha)
  have hr := ContextTranslation.Return.returnedRoot_spec q root out.2 ha hnext
  have hb := ContextTranslation.Return.returnedRoot_betaCode q root out.2 ha hnext
  have hmu := ContextTranslation.MuInvariance.returned_sourceValue_eq q root out.2 ha hnext
    (by rw [hbase]; exact hbound)
  rw [hbase] at hr hb hmu
  exact ⟨hr.1, hr.2, hb, hmu, hbound⟩

/-- The direct original query derives all original-source next callers
and its true contextual mu equation without any provenance premise. -/
theorem next_source (q root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute ((q, root), cutoff)) (hh : out.1 = true) :
    Mu.inputCheck q (ContextTranslation.Return.returnedRoot q root out.2) = true ∧
      interpretation q (ContextTranslation.Return.returnedRoot q root out.2) =
        interpretation (betaCode q root) out.2 ∧
      betaCode q (ContextTranslation.Return.returnedRoot q root out.2) =
        betaCode (betaCode q root) out.2 ∧
      Mu.sourceValue q (ContextTranslation.Return.returnedRoot q root out.2) =
        Mu.sourceValue (betaCode q root) out.2 ∧
      interpretation (betaCode q root) out.2 < Enclosure.sourceAlphaPlus q root :=
  continued_source q root q root cutoff out
    ((SkNextSearch.inputCheck_exact q root cutoff).mp (SkNextSearch.execute_spec q root cutoff out ho).1).1
    ho hh rfl rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkContextFidelity
