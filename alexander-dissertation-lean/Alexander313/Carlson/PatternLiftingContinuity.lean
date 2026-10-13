import Alexander313.Carlson.PatternLifting
import Alexander313.Carlson.ContinuityAnchors

/-!
# Continuity of minimal pattern liftings

On a fixed arithmetic carrier, a minimal lifting is covered by every
candidate lifting by the identity map. Hence a continuous candidate makes
every minimal lifting on that carrier continuous: its relations are a subset
of the candidate's relations, and k-correctness only requires an implication.

This supplies the minimality step in Carlson's Lemma 12.6(2), in the pure
case, without requiring a chosen candidate itself to be minimal.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 49–56 of the author's October 16, 2008 manuscript.
-/

noncomputable section

namespace Alexander313.Carlson

namespace PatternLifting

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A minimal lifting inherits continuity from any continuous lifting on
the same arithmetic carrier. The competing lifting map may differ. -/
theorem IsMinimal.continuous_of_lifting
    {P Pplus : Str α} {Q R S : Str β} {h f g : α → β}
    (hM : IsMinimal P Pplus Q R h)
    (D : PatternLifting P Pplus Q R h f)
    (E : PatternLifting P Pplus Q S h g)
    (hU : S.U = R.U) (hS : Str.Continuous Q S) : Str.Continuous Q R :=
  hS.of_covering_id D.target_sub (hM S g hU E)

/-- A continuous candidate admits a minimal lifting on the same carrier,
and that minimal lifting remains continuous. -/
theorem exists_minimal_continuous
    {P Pplus : Str α} {Q Qplus : Str β} {h f : α → β}
    (D : PatternLifting P Pplus Q Qplus h f) (hC : Str.Continuous Q Qplus) :
    ∃ R : Str β, R.U = Qplus.U ∧ PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.Continuous Q R := by
  obtain ⟨R, hU, DR, hM⟩ := D.exists_minimal
  exact ⟨R, hU, DR, hM, hM.continuous_of_lifting DR D hU.symm hC⟩

end PatternLifting

end Alexander313.Carlson
