import Alexander313.Wilken.PublicEpsilonNativeUnboundedOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativeOmegaQuotientBaseChangeSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaShiftedIndicatorBaseChange

/-!
# Actual original-domain coefficient provenance under base change

The original written high-root Par cutoff derives the smaller-context
root and argument callers. The genuine ANY-q quotient atom and ANF
operations therefore agree literally, including the Omega-one equality
threshold and the zero-or-limit/finite-unit split. The genuine target
operations supply FULL hidden coefficient payloads before Par and pi.
No selected endpoint or target-root/coefficient oracle is supplied.
These uncompiled source candidates are a mu3.9 dependency.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.OmegaQuotient.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)
open BoundedContextIota.OmegaQuotient (limitTerm finiteOffset)

theorem target_root (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    rootCheck v root = true := RootLowCollapse.target_root q v root ha hv hp

theorem argument_target_accepted (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    Decomposition.inputCheck v (argumentCode root) = true :=
  Support.argument_accepted v root (target_root q v root ha hv hp)

/-- The genuine atom/word kernel is universal on actual dual admission;
the old selected-root wrapper is not invoked. -/
theorem coefficient_literal_context (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    coefficientCode q root = (limitTerm v (argumentCode root)).code ∧
      coefficientOffset q root = finiteOffset v (argumentCode root) := by
  have hcq := Support.argument_accepted q root ha
  have hcv := argument_target_accepted q v root ha hv hp
  rw [coefficientCode_literal q root ha, coefficientOffset_literal q root ha,
    PublicEpsilonIota.OmegaQuotient.BaseChange.limitTerm_context q v _ hcq hcv,
    PublicEpsilonIota.OmegaQuotient.BaseChange.finiteOffset_context q v _ hcq hcv]
  exact ⟨rfl, rfl⟩

theorem coefficientCode_change (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    coefficientCode q root = coefficientCode v root ∧
      coefficientOffset q root = coefficientOffset v root := by
  have hs := coefficient_literal_context q v root ha hv hp
  have hr := target_root q v root ha hv hp
  rw [coefficientCode_literal v root hr, coefficientOffset_literal v root hr]
  exact hs

theorem coefficient_payloads (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    Payloads v (rawTree (coefficientCode q root)) := by
  rw [(coefficient_literal_context q v root ha hv hp).1, rawTree_code]
  exact PublicEpsilonIota.OmegaQuotient.BaseChange.limitTerm_payloads v _
    (argument_target_accepted q v root ha hv hp)

theorem coefficient_parBounded (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    ParBounded q v (rawTree (coefficientCode q root)) := by
  have hc := ((Comparison.acceptedCode_exact q _).mp (coefficientCode_accepted q root ha)).1
  exact (BaseTransformation.parBounded_iff_payloads q v _ (Arithmetic.raw_checked q _ hc) hv).mpr
    (coefficient_payloads q v root ha hv hp)

theorem coefficient_pi_caller (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    BaseTransformation.inputCheck q v (coefficientCode q root) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨((Comparison.acceptedCode_exact q _).mp (coefficientCode_accepted q root ha)).1,
      hv, hl, coefficient_parBounded q v root ha hv hp⟩

/-- The ACTUAL smaller-context guarded coefficient producer is derived
from the original root Par alone; no endpoint is retained. -/
theorem piCode_coefficientCode (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree root)) :
    BaseTransformation.piCode q v (coefficientCode q root) = coefficientCode v root := by
  rw [BaseTransformation.piCode_eq q v _ (coefficient_pi_caller q v root ha hv hl hp)]
  exact (coefficientCode_change q v root ha hv hp).1

/-- Original coefficient admission and restriction are actual constructed
callers for the relative-indicator base-change theorem. -/
theorem coefficient_target_callers (q v root : Nat) (ha : rootCheck q root = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree root)) :
    rootCheck v root = true ∧
      PublicEpsilonUnboundedIota.inputCheck v root (coefficientCode q root) = true := by
  have hr := target_root q v root ha hv hp
  refine ⟨hr, ?_⟩
  rw [(coefficientCode_change q v root ha hv hp).1]
  exact coefficient_iota_input v root hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.OmegaQuotient.BaseChange
