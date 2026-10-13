import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSourceBaseChange
import Alexander313.Wilken.PublicEpsilonNativeContextSupport

/-!
# Genuine mu invariance under base spelling alone

Actual equality of admitted base VALUES preserves the original literal
root check. Its second-context checker supplies every payload cutoff used
by the genuine returned-source mu producer; the existing source-code
change theorem therefore applies without a lower-base premise. Literal
returned-source outputs and their true denotations identify the two mu
values. No base-changing HIGH root, Par cutoff or mu invariance is supplied.
This is SAME-base spelling invariance, not arbitrary cross-base fidelity.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.BaseValueInvariance

open ThetaCourse

theorem root_caller (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (he : base q = base v) : inputCheck v root = true := by
  obtain ⟨t, hroot, ht, hn, hsort⟩ := (RootLowCollapse.rootCheck_exact q root).mp ha
  have hq := RootLowCollapse.source_checked q root ha
  exact (RootLowCollapse.rootCheck_exact v root).mpr
    ⟨t, hroot,
      (PublicEpsilonSourceDictionary.native_check_invariant q v hq hv he _).symm.trans ht,
      (PublicEpsilonSourceDictionary.native_normal_iff q v he t).mp hn, hsort⟩

/-- The actual second-context root checker derives the full cutoff; the
original mu provenance theorem then gives literal source-code agreement. -/
theorem sourceCode_eq (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (he : base q = base v) :
    MuSource.sourceCode q root = MuSource.sourceCode v root := by
  have hr := root_caller q v root ha hv he
  have hq := Arithmetic.raw_checked q root (RootLowCollapse.root_original q root ha)
  have ht := Arithmetic.raw_checked v root (RootLowCollapse.root_original v root hr)
  have hp : BaseTransformation.ParBounded q v (rawTree root) :=
    (BaseTransformation.parBounded_iff_payloads q v _ hq hv).mpr
      (checked_admissible v _ ht).1
  exact MuSource.BaseChange.sourceCode_change q v root ha hv hp

/-- SAME admitted base values and the original HIGH root alone derive
actual mu value equality, through the genuine returned-source execution. -/
theorem sourceValue_eq (q v root : Nat) (ha : inputCheck q root = true)
    (hv : baseCheck v = true) (he : base q = base v) :
    sourceValue q root = sourceValue v root := by
  have hr := root_caller q v root ha hv he
  calc
    sourceValue q root = interpretation q (MuSource.sourceCode q root) :=
      (MuSource.source_definition_3_6 q root ha).symm
    _ = interpretation v (MuSource.sourceCode q root) := interpretation_invariant q v _ he
    _ = interpretation v (MuSource.sourceCode v root) :=
      congrArg (interpretation v) (sourceCode_eq q v root ha hv he)
    _ = sourceValue v root := MuSource.source_definition_3_6 v root hr

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.BaseValueInvariance
