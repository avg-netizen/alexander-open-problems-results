import Alexander313.Thesis313FromPackage
import Alexander313.ComparatorChallenge

/-!
# Conditional thesis 3-1-3 / 3-1-2 compilation and axiom check

This entry point imports the stage-genericity chain, conditional only on an
`OrdinalPackage` (the abstract order-2 ordinal input of note 24 §1). It checks
the two implications against the unchanged independent comparator targets and
prints their axioms. No package instance exists yet, so this is not the
unconditional gate; `Completion.lean` remains that gate. Both implications passed
on 2026-10-09 with only the ordinary foundational axioms. Run
`scripts/verify_checked.py` to rebuild and record the current source hashes.
-/

example : Alexander313.OrdinalPackage → Alexander313.Comparator.challenge313 :=
  Alexander313.challenge313_of_package

example : Alexander313.OrdinalPackage → Alexander313.Comparator.challenge312 :=
  Alexander313.challenge312_of_package

#print axioms Alexander313.challenge313_of_package
#print axioms Alexander313.challenge312_of_package
