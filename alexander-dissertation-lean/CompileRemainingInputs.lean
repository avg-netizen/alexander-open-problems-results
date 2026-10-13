import Alexander313.RemainingOrdinalInputs

/-!
# The remaining ordinal inputs, in their plainest form

3-1-3 and 3-1-2 follow from computable decisions of the actual pure first and
second relations on the canonical codes, together with the finite maximal
second chain `υ₂ <₂ υ₃ <₂ ⋯` on the source upsilon sequence. This gate checks
those implications against the independent comparator targets; it does not
assert either input.
-/

open Alexander313
open Alexander313.CanonicalOrdinalPackage

example (decideFirst decideSecond : Nat → Nat → Bool)
    (hfirst : Computable₂ decideFirst) (hsecond : Computable₂ decideSecond)
    (first_exact : ∀ n m, decideFirst n m = true ↔
      Wilken.PureRelations.R1 (HereditaryCanonicalEnumeration.ordinalValue n)
        (HereditaryCanonicalEnumeration.ordinalValue m))
    (second_exact : ∀ n m, decideSecond n m = true ↔
      Wilken.PureRelations.R2 (HereditaryCanonicalEnumeration.ordinalValue n)
        (HereditaryCanonicalEnumeration.ordinalValue m))
    (chain : UpsilonSecondChain) : Comparator.challenge313 :=
  challenge313_of_inputs decideFirst decideSecond hfirst hsecond first_exact second_exact chain

#print axioms Alexander313.CanonicalOrdinalPackage.tall_of_upsilonSecondChain
#print axioms Alexander313.CanonicalOrdinalPackage.program_of_decision
#print axioms Alexander313.CanonicalOrdinalPackage.challenge313_of_inputs
#print axioms Alexander313.CanonicalOrdinalPackage.challenge312_of_inputs
