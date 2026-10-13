import Alexander313.Thesis311Complete
import Alexander313.ComparatorChallenge

/-!
# Isolated thesis 3-1-1 compilation and axiom check

This entry point imports the actual 3-1-1 theorem and its dependencies,
without importing the whole ordinal library. It checks the exact independent
comparator type and prints the theorem's axioms. It passed on 2026-10-09;
`scripts/verify_checked.py` rebuilds this gate and records current source hashes.
Completion.lean remains the separate unchanged gate for all three targets.
-/

example : Alexander313.Comparator.challenge311 := Alexander313.thesis311

#print axioms Alexander313.thesis311
