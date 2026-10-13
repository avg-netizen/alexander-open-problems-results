import Alexander313.Wilken.PublicEpsilonNativeGammaHatSupport
import Mathlib.Order.WellFounded

/-!
# The genuine least represented singleton boundary

Definition3.30 requires a multiplicative value strictly above the original
root AND its original mu, whose independently executing assignment in the
root context is a singleton. The real original source successor supplies a
candidate, so ordinal well-foundedness gives a least such represented value.
The returned witness is an actual native code with a real full assignment,
not a supplied boundary or singleton. This semantic minimum is noncomputable;
no executing gamma-hat, mts criterion, large h or evaluation is claimed.
Source-only and uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.GammaHat

open GammaHatSupport Enclosure

def CandidateValues (q root : Nat) : Set Ordinal.{0} := fun v =>
  ∃ c : Nat, SourceMultiplicativePrincipal.inputCheck (betaCode q root) c = true ∧
    v = interpretation (betaCode q root) c ∧ interpretation q root < v ∧
      Mu.sourceValue q root < v ∧
        [c] ∈ SourceAdditiveTracking.Assignment.execute (betaCode q root) c

theorem candidateValues_nonempty (q root : Nat) (ha : rootCheck q root = true) :
    (CandidateValues q root).Nonempty := by
  have hs := endpoint_candidate q root ha
  exact ⟨interpretation (betaCode q root) (endpointCode q root), endpointCode q root,
    hs.1, rfl, hs.2.2.1, hs.2.2.2, hs.2.1⟩

def value (q root : Nat) (ha : rootCheck q root = true) : Ordinal.{0} :=
  Ordinal.lt_wf.min (CandidateValues q root) (candidateValues_nonempty q root ha)

theorem value_mem (q root : Nat) (ha : rootCheck q root = true) :
    value q root ha ∈ CandidateValues q root :=
  Ordinal.lt_wf.min_mem _ (candidateValues_nonempty q root ha)

theorem value_le_candidate (q root : Nat) (ha : rootCheck q root = true)
    (v : Ordinal.{0}) (hv : v ∈ CandidateValues q root) : value q root ha ≤ v := by
  apply le_of_not_gt
  simpa only [value] using Ordinal.lt_wf.not_lt_min (CandidateValues q root) hv

theorem value_le_sourceAlphaPlus (q root : Nat) (ha : rootCheck q root = true) :
    value q root ha ≤ sourceAlphaPlus q root := by
  have hs := endpoint_candidate q root ha
  have hc : interpretation (betaCode q root) (endpointCode q root) ∈ CandidateValues q root :=
    ⟨endpointCode q root, hs.1, rfl, hs.2.2.1, hs.2.2.2, hs.2.1⟩
  simpa only [endpoint_value q root ha] using value_le_candidate q root ha _ hc

/-- The actual ordinal least witness retains all original finite native
callers and its independently executing literal singleton assignment. -/
theorem value_spec (q root : Nat) (ha : rootCheck q root = true) :
    ∃ c : Nat, SourceMultiplicativePrincipal.inputCheck (betaCode q root) c = true ∧
      interpretation (betaCode q root) c = value q root ha ∧
      [c] ∈ SourceAdditiveTracking.Assignment.execute (betaCode q root) c ∧
      interpretation q root < value q root ha ∧ Mu.sourceValue q root < value q root ha ∧
      value q root ha ≤ sourceAlphaPlus q root := by
  obtain ⟨c, hc, hv, hroot, hmu, ho⟩ := value_mem q root ha
  exact ⟨c, hc, hv.symm, ho, hroot, hmu, value_le_sourceAlphaPlus q root ha⟩

theorem value_isLeast (q root : Nat) (ha : rootCheck q root = true) :
    IsLeast (CandidateValues q root) (value q root ha) :=
  ⟨value_mem q root ha, fun v hv => value_le_candidate q root ha v hv⟩

theorem least_unique (q root : Nat) (ha : rootCheck q root = true)
    (v : Ordinal.{0}) (hv : IsLeast (CandidateValues q root) v) : v = value q root ha :=
  le_antisymm (hv.2 _ (value_mem q root ha))
    ((value_isLeast q root ha).2 _ hv.1)

theorem value_multiplicative (q root : Nat) (ha : rootCheck q root = true) :
    MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (value q root ha) := by
  obtain ⟨c, hc, hv, _⟩ := value_spec q root ha
  rw [← hv]
  exact ((SourceMultiplicativePrincipal.inputCheck_exact _ _).mp hc).2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.GammaHat
