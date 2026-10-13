import Alexander313.SourceParticularCode

/-!
# Literal source particular-code quantifier gate

The new bridge supplements, and does not edit, the independent comparator.
Its stronger witnesses preserve the actual canonical arithmetic template and
prove the literal source existential outside knowledge. The 3-1-3 witness
retains its explicit ordinal-package input.
-/

open Alexander313

example : ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R →
    ∃ S : Solution311 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      ∀ i j, R j i → ∀ (φ : UnaryFormula Nat) s,
        actualTruth S.family.effective.proves
          (.ex (φ.input + 1) (.know i (.all φ.input
            (.iff (.know j φ.body)
              (S.arithmetic.member (.var (φ.input + 1)) (.var φ.input)))))) s :=
  thesis311_with_source_particular

example : OrdinalPackage → ∀ R : Nat → Nat → Prop, HierarchyRE R → WellFounded R →
    ∃ S : Solution313 R, S.arithmetic = canonicalArithmeticCoding Nat ∧
      ∀ i j, R j i → ∀ (φ : UnaryFormula Nat) s,
        actualTruth S.family.effective.proves
          (.ex (φ.input + 1) (.know i (.all φ.input
            (.iff (.know j φ.body)
              (S.arithmetic.member (.var (φ.input + 1)) (.var φ.input)))))) s :=
  thesis313_with_source_particular

#print axioms sourceCodeMatrix_close_valid
#print axioms MachineFamily.sourceParticular_of_codeMember
#print axioms knowsParticularCodes_to_source
#print axioms thesis311_with_source_particular
#print axioms thesis313_with_source_particular
