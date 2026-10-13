import Alexander313.Carlson.CoreTallness
import Alexander313.Carlson.Package

/-!
# The proved core supplies the ordinal package's tallness field

An initial-segment presentation with bound `coreBound` inherits finite
tallness. The package constructor no longer needs this as an independent
hypothesis; its remaining inputs are the effective presentation and three
actual relation-recognizing Programs.
-/

noncomputable section

namespace Alexander313
namespace OrdinalPresentation

variable {Label : Type} [LinearOrder Label] (P : OrdinalPresentation Label)

theorem tall_of_core (hbound : P.bound = Carlson.coreBound) (k : ℕ) :
    ∃ top : Label, GuardHead P.second k top := by
  obtain ⟨top, tail, hlen, hord, hrel, hcore⟩ := Carlson.exists_guard_in_core k
  have hval (z : Ordinal.{0}) (hz : z ∈ top :: tail) : P.val (P.pre z) = z :=
    P.val_pre z (hbound ▸ hcore z hz)
  refine ⟨P.pre top, tail.map P.pre, by rw [List.length_map, hlen], ?_, ?_⟩
  · simpa only [List.map_cons] using guardRoom_pairwise_map (· < ·) (· < ·) P.pre
      (top :: tail) hord (fun x hx y hy hxy => by
        rw [← P.lt_iff, hval x hx, hval y hy]
        exact hxy)
  · simpa only [List.map_cons] using guardRoom_pairwise_map Carlson.R2 P.second P.pre
      (top :: tail) hrel (fun x hx y hy hxy => by
        change Carlson.R2 (P.val (P.pre x)) (P.val (P.pre y))
        rw [hval x hx, hval y hy]
        exact hxy)

end OrdinalPresentation

namespace OrdinalPackage

/-- Assemble the ordinal package on the actual Carlson core. Tallness is
proved; no tallness or coveredness parameter is supplied to this constructor. -/
def ofCarlsonCore (order : LinearOrder Nat) (P : OrdinalPresentation (CodedLabel order))
    (hbound : P.bound = Carlson.coreBound)
    (ltProgram firstProgram secondProgram : Program)
    (hlt : ∀ μ ν : CodedLabel order, ltProgram.domain (Nat.pair μ ν) ↔ μ < ν)
    (hfirst : ∀ μ ν : CodedLabel order, firstProgram.domain (Nat.pair μ ν) ↔ P.first μ ν)
    (hsecond : ∀ μ ν : CodedLabel order, secondProgram.domain (Nat.pair μ ν) ↔ P.second μ ν) :
    OrdinalPackage :=
  ofCarlson order P ltProgram firstProgram secondProgram hlt hfirst hsecond
    (P.tall_of_core hbound)

end OrdinalPackage
end Alexander313
