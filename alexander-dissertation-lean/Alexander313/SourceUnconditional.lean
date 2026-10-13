import Alexander313.SourceParticularCode
import Alexander313.Carlson.EffectiveCorePackage

/-!
# Unconditional witnesses for the literal source particular-code formula

The previously checked source bridge preserves the concrete canonical arithmetic
template and places the code existential outside knowledge, exactly as displayed
in Alexander's dissertation. Carlson's constructed effective package now
discharges its last premise. Each result supplies one family for all unrestricted
unary formulas and every recursively enumerable well-founded hierarchy.
-/

namespace Alexander313

theorem thesis313_with_source_particular_unconditional
    (R : Nat → Nat → Prop) (hR : HierarchyRE R) (wf : WellFounded R) :
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R :=
  thesis313_with_source_particular Carlson.EffectiveCorePackage.package R hR wf

theorem thesis312_with_source_particular_unconditional
    (R : Nat → Nat → Prop) (hR : HierarchyRE R) (wf : WellFounded R) :
    ∃ S : Solution312 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R := by
  obtain ⟨S, hcanonical, hsource⟩ :=
    thesis313_with_source_particular_unconditional R hR wf
  exact ⟨S.toSolution312, hcanonical, hsource⟩

end Alexander313
