import Alexander313.Specification
import Alexander313.ProofClosure
import Alexander313.Alexander.AlphaSemantics

/-!
# Admissible realizations are derived for every sentence consequence family

Sentence consequence closure transfers proofs across alpha-equivalent
conclusions. Hence any MachineFamily already has the raw invariance needed
by the proved actual and filtered realization constructors. Source soundness
is not used here, and no separate model contract is added.
-/

namespace Alexander313

theorem MachineFamily.rawAlphabetic (F : MachineFamily) :
    RawAlphabetic F.effective.proves := by
  intro i φ ψ hφ hψ hα
  constructor
  · intro hp
    exact (F.theory_closed i ψ hψ).mp ((Provable.of_axiom hp).alpha hα)
  · intro hp
    have hreverse : ψ.AlphaEquivalent φ := hα.symm
    exact (F.theory_closed i φ hφ).mp ((Provable.of_axiom hp).alpha hreverse)

def MachineFamily.actualRealization (F : MachineFamily) :
    ActualRealization F.effective.proves :=
  ActualRealization.ofAlphabetic _ F.rawAlphabetic

def MachineFamily.filteredRealization (F : MachineFamily) :
    FilteredRealization F.effective.proves :=
  FilteredRealization.ofAlphabetic _ F.rawAlphabetic

end Alexander313
