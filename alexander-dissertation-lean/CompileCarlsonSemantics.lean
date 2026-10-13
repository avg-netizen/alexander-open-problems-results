import Alexander313.Carlson.Package
import Alexander313.Carlson.Order
import Alexander313.Thesis313FromPackage

/-!
# Carlson's covering relations of order two: semantics and package assembly

Milestone C1 of `ROADMAP-2026-10-09-CARLSON-ROUTE.md`. Carlson's pure-case
relations are defined by recursion on the upper ordinal (Definition 5.3). Their
copy, connectedness and transitivity properties (Lemma 5.5) give covering
reflection and separated guard room on any presentation of an initial segment
of the ordinals. 3-1-3 then follows from such a presentation, its three
recognizing Programs and finite tallness; this gate checks that implication
against the independent comparator. It does not assert those inputs.
-/

open Alexander313

example (order : LinearOrder Nat) (P : OrdinalPresentation (CodedLabel order))
    (ltProgram firstProgram secondProgram : Program)
    (hlt : ∀ μ ν : CodedLabel order, ltProgram.domain (Nat.pair μ ν) ↔ μ < ν)
    (hfirst : ∀ μ ν : CodedLabel order, firstProgram.domain (Nat.pair μ ν) ↔ P.first μ ν)
    (hsecond : ∀ μ ν : CodedLabel order, secondProgram.domain (Nat.pair μ ν) ↔ P.second μ ν)
    (htall : ∀ k, ∃ top : CodedLabel order, GuardHead P.second k top) :
    Comparator.challenge313 :=
  challenge313_of_package (OrdinalPackage.ofCarlson order P ltProgram firstProgram
    secondProgram hlt hfirst hsecond htall)

#print axioms Alexander313.Carlson.R1_iff
#print axioms Alexander313.Carlson.R2_iff
#print axioms Alexander313.Carlson.R1_refl
#print axioms Alexander313.Carlson.R2_refl
#print axioms Alexander313.Carlson.R2_R1
#print axioms Alexander313.Carlson.R1_copy
#print axioms Alexander313.Carlson.R2_copy
#print axioms Alexander313.Carlson.R1_between
#print axioms Alexander313.Carlson.R1_trans
#print axioms Alexander313.Carlson.guard_one_copy
#print axioms Alexander313.Carlson.finite_guard_room
#print axioms Alexander313.OrdinalPresentation.covering
#print axioms Alexander313.OrdinalPresentation.room
#print axioms Alexander313.OrdinalPackage.ofCarlson
#print axioms Alexander313.Carlson.R2_cofinal
#print axioms Alexander313.Carlson.R2_trans
#print axioms Alexander313.Carlson.R2_respects_R1
#print axioms Alexander313.Carlson.model_of_reflection
