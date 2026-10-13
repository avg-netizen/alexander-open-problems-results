import Alexander313.Carlson.EffectiveCorePackage
import Alexander313.Thesis313FromPackage

/-!
# Unconditional thesis 3-1-3 and 3-1-2 against the independent comparator

The constructed effective Carlson-core package discharges the final premise
of the already checked stage-soundness assembly. Neither statement accepts
an ordinal package or any source-family, arithmetic-coding or soundness
parameter. The independent comparator and specification remain unchanged.
-/

namespace Alexander313

/-- Every recursively enumerable well-founded hierarchy has the original
language family required by the independent 3-1-3 comparator. -/
theorem thesis313 : Comparator.challenge313 :=
  challenge313_of_nonempty_package Carlson.EffectiveCorePackage.package_exists

/-- Thesis 3-1-2 follows by forgetting the extra mechanicalness clause. -/
theorem thesis312 : Comparator.challenge312 :=
  challenge312_of_nonempty_package Carlson.EffectiveCorePackage.package_exists

end Alexander313
