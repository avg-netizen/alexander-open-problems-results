import Alexander313.CanonicalOrdinalPackage
import Alexander313.Thesis313FromPackage

/-!
# Exact remaining-input gate on the actual canonical ordinal presentation

This is conditional on two genuine recognizing Programs and finite strict
second-relation tallness. No arbitrary order, semantic reflection, room,
effectivity of ordinary comparison, or interval coverage is an input.
-/

open Alexander313
open Alexander313.CanonicalOrdinalPackage

example (firstProgram secondProgram : Program)
    (hfirst : ∀ n m : Label, firstProgram.domain (Nat.pair n m) ↔ first n m)
    (hsecond : ∀ n m : Label, secondProgram.domain (Nat.pair n m) ↔ second n m)
    (htall : ∀ k, ∃ top : Label, GuardHead second k top) : Comparator.challenge313 :=
  challenge313_of_package (assemble firstProgram secondProgram hfirst hsecond htall)

#print axioms Alexander313.HereditaryCanonicalEnumeration.enumCode_computable
#print axioms Alexander313.HereditaryCanonicalEnumeration.sourceIntervalOrderIso
#print axioms smallOrderIso
#print axioms ltProgram_domain
#print axioms assemble
