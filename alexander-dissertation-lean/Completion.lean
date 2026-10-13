import Alexander313.Thesis313Unconditional
import Alexander313.SourceUnconditional
import Alexander313.ComparatorChallenge

/-!
# Unconditional completion gate

All three declarations are checked against the unchanged, independently imported
comparator targets. Stronger witnesses also satisfy the literal source code
formula with its existential outside knowledge. These examples have no
ordinal-package premise. The axiom audit must accept only propext,
Classical.choice and Quot.sound.
-/

example : Alexander313.Comparator.challenge311 := Alexander313.thesis311
example : Alexander313.Comparator.challenge313 := Alexander313.thesis313
example : Alexander313.Comparator.challenge312 := Alexander313.thesis312

open Alexander313

example : ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R →
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      ∀ i j, R j i → ∀ (φ : UnaryFormula Nat) s,
        actualTruth S.family.effective.proves
          (.ex (φ.input + 1) (.know i (.all φ.input
            (.iff (.know j φ.body)
              (S.arithmetic.member (.var (φ.input + 1)) (.var φ.input)))))) s :=
  thesis313_with_source_particular_unconditional

example : ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R →
    ∃ S : Solution312 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      knowsSourceParticularCodes S.arithmetic S.family R :=
  thesis312_with_source_particular_unconditional

#print axioms Alexander313.Carlson.EffectiveCorePackage.package_exists
#print axioms Alexander313.thesis311
#print axioms Alexander313.thesis313
#print axioms Alexander313.thesis312
#print axioms Alexander313.thesis311_with_source_particular
#print axioms Alexander313.thesis313_with_source_particular_unconditional
#print axioms Alexander313.thesis312_with_source_particular_unconditional
