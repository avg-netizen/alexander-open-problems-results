import Alexander313.OrdinalPackageFromSmallLabels
import Alexander313.Thesis313FromPackage

/-!
# Conditional effective-presentation assembly gate

This gate assumes actual numerical recognizers and finite tallness within
the interval named by the supplied order isomorphism. Every other ordinal
package field is derived from the actual pure relations. Neither the source
presentation nor its tallness is asserted to exist by this gate.
-/

open Alexander313
open Alexander313.Wilken.PureRelations

example (order : LinearOrder Nat) (Ω : Ordinal.{0})
    (e : CodedLabel order ≃o SmallLabels.Labels Ω)
    (ltProgram firstProgram secondProgram : Program)
    (hlt : ∀ μ ν : CodedLabel order,
      ltProgram.domain (Nat.pair μ ν) ↔ e μ < e ν)
    (hfirst : ∀ μ ν : CodedLabel order,
      firstProgram.domain (Nat.pair μ ν) ↔ SmallLabels.first Ω (e μ) (e ν))
    (hsecond : ∀ μ ν : CodedLabel order,
      secondProgram.domain (Nat.pair μ ν) ↔ SmallLabels.second Ω (e μ) (e ν))
    (htall : ∀ k, ∃ top : SmallLabels.Labels Ω, GuardHead (SmallLabels.second Ω) k top) :
    Comparator.challenge313 :=
  challenge313_of_package (OrdinalPackage.ofEffectiveSmallLabels order Ω e
    ltProgram firstProgram secondProgram hlt hfirst hsecond htall)

#print axioms GuardHead.mapOrderIso
#print axioms FiniteLabelReflection.ofOrderIso
#print axioms OrdinalPackage.ofEffectiveSmallLabels
