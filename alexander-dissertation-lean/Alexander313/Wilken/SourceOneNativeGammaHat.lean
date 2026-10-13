import Alexander313.Wilken.SourceOneNativeGammaHatSupport
import Mathlib.Order.WellFounded

/-!
# The genuine original-source-one least singleton boundary

The original source-zero high root supplies a real alpha-context singleton
candidate above itself and its original mu. Ordinal well-foundedness selects
the least represented candidate, retaining an admitted native code and its
complete independently executed assignment. The minimum is semantic and
noncomputable; numerical hat, mts, large h and evaluation remain separate.
Source-only uncompiled candidates, never a Native-base-one source adapter.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.GammaHat

open GammaHatSupport Enclosure

def CandidateValues (a : Nat) : Set Ordinal.{0} := fun v =>
  ∃ c : Nat, NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) c = true ∧
    v = NativeContext.interpretation (alphaCode a) c ∧ interpretation 0 a < v ∧
      Mu.sourceValue a < v ∧
        [c] ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode a) c

theorem candidateValues_nonempty (a : Nat) (ha : rootCheck a = true) :
    (CandidateValues a).Nonempty := by
  have hs := endpoint_candidate a ha
  exact ⟨NativeContext.interpretation (alphaCode a) (endpointCode a), endpointCode a,
    hs.1, rfl, hs.2.2.1, hs.2.2.2, hs.2.1⟩

def value (a : Nat) (ha : rootCheck a = true) : Ordinal.{0} :=
  Ordinal.lt_wf.min (CandidateValues a) (candidateValues_nonempty a ha)

theorem value_mem (a : Nat) (ha : rootCheck a = true) : value a ha ∈ CandidateValues a :=
  Ordinal.lt_wf.min_mem _ (candidateValues_nonempty a ha)

theorem value_le_candidate (a : Nat) (ha : rootCheck a = true)
    (v : Ordinal.{0}) (hv : v ∈ CandidateValues a) : value a ha ≤ v := by
  apply le_of_not_gt
  simpa only [value] using Ordinal.lt_wf.not_lt_min (CandidateValues a) hv

theorem value_le_sourceAlphaPlus (a : Nat) (ha : rootCheck a = true) :
    value a ha ≤ sourceAlphaPlus a := by
  have hs := endpoint_candidate a ha
  have hc : NativeContext.interpretation (alphaCode a) (endpointCode a) ∈ CandidateValues a :=
    ⟨endpointCode a, hs.1, rfl, hs.2.2.1, hs.2.2.2, hs.2.1⟩
  simpa only [endpoint_value a ha] using value_le_candidate a ha _ hc

/-- The least represented value still has a genuine complete finite
native caller and literal singleton execution at the actual alpha context. -/
theorem value_spec (a : Nat) (ha : rootCheck a = true) :
    ∃ c : Nat, NativeContext.SourceMultiplicativePrincipal.inputCheck (alphaCode a) c = true ∧
      NativeContext.interpretation (alphaCode a) c = value a ha ∧
      [c] ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode a) c ∧
      interpretation 0 a < value a ha ∧ Mu.sourceValue a < value a ha ∧
      value a ha ≤ sourceAlphaPlus a := by
  obtain ⟨c, hc, hv, hroot, hmu, ho⟩ := value_mem a ha
  exact ⟨c, hc, hv.symm, ho, hroot, hmu, value_le_sourceAlphaPlus a ha⟩

theorem value_isLeast (a : Nat) (ha : rootCheck a = true) :
    IsLeast (CandidateValues a) (value a ha) :=
  ⟨value_mem a ha, fun v hv => value_le_candidate a ha v hv⟩

theorem least_unique (a : Nat) (ha : rootCheck a = true)
    (v : Ordinal.{0}) (hv : IsLeast (CandidateValues a) v) : v = value a ha :=
  le_antisymm (hv.2 _ (value_mem a ha)) ((value_isLeast a ha).2 _ hv.1)

theorem value_multiplicative (a : Nat) (ha : rootCheck a = true) :
    MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (value a ha) := by
  obtain ⟨c, hc, hv, _⟩ := value_spec a ha
  rw [← hv]
  exact ((NativeContext.SourceMultiplicativePrincipal.inputCheck_exact _ _).mp hc).2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.GammaHat
