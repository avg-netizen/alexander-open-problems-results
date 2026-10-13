import Alexander313.Carlson.ComputableAnchors
import Alexander313.Carlson.PatternLiftingData
import Alexander313.Carlson.PatternTransport
import Alexander313.Carlson.RationalPresentation

/-!
# Executable rational images and normalized lifting candidates

Finite rational presentations can be mapped without choosing inverse labels:
map the carrier and every on-carrier edge. This agrees exactly with `Str.map`,
even for a map that is not injective. Edges outside the source carrier are
discarded before taking the image.

The normalized continuous-lifting candidate has an executable presentation.
Both relation tables are obtained by filtering the supplied finite carrier
square. The four old/new endpoint cases are the cases of
`PatternLiftingConstruction.Data.candidate`; upper anchors use
`Str.computableUp`, and the incoming second relation searches the finite
source carrier. The presentation agrees with the existing candidate on its
carrier, hence gives an identity isomorphism. No pattern or continuity
decision is needed to compute either table.
-/

namespace Alexander313.Carlson.Finite.RationalPresentation

/-- Map a presentation's carrier and its on-carrier relation edges. -/
def map (P : RationalPresentation) (f : ℚ → ℚ) : RationalPresentation where
  U := P.U.image f
  r₁ := ((P.U ×ˢ P.U).filter (fun xy => xy ∈ P.r₁)).image
    (fun xy => (f xy.1, f xy.2))
  r₂ := ((P.U ×ˢ P.U).filter (fun xy => xy ∈ P.r₂)).image
    (fun xy => (f xy.1, f xy.2))

@[simp] theorem map_U (P : RationalPresentation) (f : ℚ → ℚ) :
    (P.map f).U = P.U.image f := rfl

private theorem mem_mapped_edges (U : Finset ℚ) (E : Finset (ℚ × ℚ))
    (f : ℚ → ℚ) (u v : ℚ) :
    (u, v) ∈ ((U ×ˢ U).filter (fun xy => xy ∈ E)).image
        (fun xy => (f xy.1, f xy.2)) ↔
      ∃ x ∈ U, ∃ y ∈ U, f x = u ∧ f y = v ∧ (x, y) ∈ E := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hU, hE⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hU
    exact ⟨x, hx, y, hy, congrArg Prod.fst heq, congrArg Prod.snd heq, hE⟩
  · rintro ⟨x, hx, y, hy, hfx, hfy, hE⟩
    exact Finset.mem_image.mpr ⟨(x, y),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hE⟩,
      Prod.ext hfx hfy⟩

/-- The first mapped edge has source endpoints in the original carrier. -/
@[simp] theorem toStr_map_r₁ (P : RationalPresentation) (f : ℚ → ℚ) (u v : ℚ) :
    (P.map f).toStr.r₁ u v ↔
      ∃ x ∈ P.U, ∃ y ∈ P.U, f x = u ∧ f y = v ∧ P.toStr.r₁ x y :=
  mem_mapped_edges P.U P.r₁ f u v

/-- The second mapped edge has source endpoints in the original carrier. -/
@[simp] theorem toStr_map_r₂ (P : RationalPresentation) (f : ℚ → ℚ) (u v : ℚ) :
    (P.map f).toStr.r₂ u v ↔
      ∃ x ∈ P.U, ∃ y ∈ P.U, f x = u ∧ f y = v ∧ P.toStr.r₂ x y :=
  mem_mapped_edges P.U P.r₂ f u v

/-- Executable image tables interpret as the existing finite image
structure, with exact agreement also outside the image carrier. -/
@[simp] theorem map_toStr (P : RationalPresentation) (f : ℚ → ℚ) :
    (P.map f).toStr = P.toStr.map f := by
  change Str.mk (P.U.image f) _ _ = Str.mk (P.U.image f) _ _
  congr 1 <;> funext u v <;> apply propext
  · exact toStr_map_r₁ P f u v
  · exact toStr_map_r₂ P f u v

/-- An increasing supplied map gives an exact isomorphism to its computed
finite presentation. -/
theorem map_isIso (P : RationalPresentation) (f : ℚ → ℚ)
    (hmono : ∀ x ∈ P.U, ∀ y ∈ P.U, x < y → f x < f y) :
    Str.IsIso P.toStr (P.map f).toStr f := by
  rw [map_toStr]
  exact P.toStr.map_isIso f hmono

/-- Compute the normalized lifting's two finite edge tables. The source
and old target are already presented in the same rational ambient order. -/
def liftingCandidate (A : Finset ℚ) (S Q : RationalPresentation)
    (U : Finset ℚ) : RationalPresentation where
  U := U
  r₁ := (U ×ˢ U).filter fun xy =>
    if xy.1 ∈ Q.U then
      if xy.2 ∈ Q.U then Q.toStr.r₁ xy.1 xy.2
      else xy.1 ≤ xy.2 ∧ Q.toStr.r₁ xy.1 (Str.computableUp A xy.2)
    else
      if xy.2 ∈ Q.U then
        S.toStr.r₁ xy.1 (Str.computableUp A xy.1) ∧
          Q.toStr.r₁ (Str.computableUp A xy.1) xy.2
      else S.toStr.r₁ xy.1 xy.2
  r₂ := (U ×ˢ U).filter fun xy =>
    if xy.1 ∈ Q.U then
      if xy.2 ∈ Q.U then Q.toStr.r₂ xy.1 xy.2
      else ∃ a ∈ S.U, xy.1 ≤ a ∧ S.toStr.r₁ a (Str.computableUp A a) ∧
        Q.toStr.r₂ xy.1 (Str.computableUp A a) ∧ S.toStr.r₂ a xy.2
    else
      if xy.2 ∈ Q.U then
        S.toStr.r₂ xy.1 (Str.computableUp A xy.1) ∧
          Q.toStr.r₂ (Str.computableUp A xy.1) xy.2
      else S.toStr.r₂ xy.1 xy.2

@[simp] theorem liftingCandidate_U (A : Finset ℚ) (S Q : RationalPresentation)
    (U : Finset ℚ) : (liftingCandidate A S Q U).U = U := rfl

/-- The computed first table is the original candidate relation restricted
to the declared finite carrier. -/
theorem liftingCandidate_r₁ {P : Str ℚ} {S Q : RationalPresentation} {U : Finset ℚ}
    (D : PatternLiftingConstruction.Data P S.toStr Q.toStr U) (x y : ℚ) :
    (liftingCandidate P.U S Q U).toStr.r₁ x y ↔
      x ∈ U ∧ y ∈ U ∧ D.candidate.r₁ x y := by
  simp [toStr, liftingCandidate, PatternLiftingConstruction.Data.candidate,
    Str.computableUp_eq_up, and_assoc]

/-- The computed second table is the original candidate relation restricted
to the declared finite carrier, including its finite incoming-edge search. -/
theorem liftingCandidate_r₂ {P : Str ℚ} {S Q : RationalPresentation} {U : Finset ℚ}
    (D : PatternLiftingConstruction.Data P S.toStr Q.toStr U) (x y : ℚ) :
    (liftingCandidate P.U S Q U).toStr.r₂ x y ↔
      x ∈ U ∧ y ∈ U ∧ D.candidate.r₂ x y := by
  simp [toStr, liftingCandidate, PatternLiftingConstruction.Data.candidate,
    Str.computableUp_eq_up, and_assoc]

/-- The computed finite tables present the normalized lifting candidate
exactly on its carrier. Only off-carrier relation values are discarded. -/
theorem liftingCandidate_iso {P : Str ℚ} {S Q : RationalPresentation} {U : Finset ℚ}
    (D : PatternLiftingConstruction.Data P S.toStr Q.toStr U) :
    Str.IsIso D.candidate (liftingCandidate P.U S Q U).toStr id := by
  refine ⟨Finset.image_id, fun _ _ _ _ h => h, ?_⟩
  intro x hx y hy
  change x ∈ U at hx
  change y ∈ U at hy
  simp only [id_eq, liftingCandidate_r₁ D, liftingCandidate_r₂ D,
    hx, hy, true_and, iff_self, and_self]

end Alexander313.Carlson.Finite.RationalPresentation

namespace Alexander313.Carlson.ComputablePatternCandidateExamples

open Finite Finite.RationalPresentation

/-- Source edges include deliberately off-carrier entries. -/
def source : RationalPresentation where
  U := {-1, 0}
  r₁ := {(-1, -1), (-1, 0), (0, 0), (8, 9)}
  r₂ := {(-1, -1), (-1, 0), (0, 0), (9, 8)}

/-- Two old anchors surrounding the new source point `-1`. -/
def target : RationalPresentation where
  U := {-2, 0}
  r₁ := {(-2, -2), (-2, 0), (0, 0)}
  r₂ := {(-2, -2), (-2, 0), (0, 0)}

/-- Identity mapping removes off-carrier edges; a constant map merges all
carrier points and keeps the resulting self edges. Both are computed. -/
theorem map_regression_suite :
    (source.map id).U = {-1, 0} ∧
    (source.map id).r₁ = {(-1, -1), (-1, 0), (0, 0)} ∧
    (source.map id).r₂ = {(-1, -1), (-1, 0), (0, 0)} ∧
    (source.map (fun _ => 3)).U = {3} ∧
    (source.map (fun _ => 3)).r₁ = {(3, 3)} ∧
    (source.map (fun _ => 3)).r₂ = {(3, 3)} := by
  decide +kernel

/-- The incoming second relation really searches the source carrier:
`-2` first reaches `-1`, whose source self edge reaches the query `-1`.
All four old/new endpoint cases occur; the reverse mixed edges fail. -/
theorem candidate_regression_suite :
    let C := liftingCandidate {0} source target {-2, -1, 0}
    C.U = {-2, -1, 0} ∧
    C.toStr.r₁ (-2) 0 ∧ C.toStr.r₂ (-2) 0 ∧
    C.toStr.r₁ (-2) (-1) ∧ C.toStr.r₂ (-2) (-1) ∧
    C.toStr.r₁ (-1) 0 ∧ C.toStr.r₂ (-1) 0 ∧
    C.toStr.r₁ (-1) (-1) ∧ C.toStr.r₂ (-1) (-1) ∧
    ¬ C.toStr.r₁ 0 (-1) ∧ ¬ C.toStr.r₂ 0 (-1) ∧
    ¬ C.toStr.r₁ (-1) (-2) ∧ ¬ C.toStr.r₂ (-1) (-2) ∧
    ¬ C.toStr.r₁ 8 9 ∧ ¬ C.toStr.r₂ 9 8 := by
  decide +kernel

/-- Here the incoming second edge must pass through `-3/2`: the queried
point `-1` has no first edge to the old upper anchor `0`. -/
def incomingSource : RationalPresentation where
  U := {-3 / 2, -1, 0}
  r₁ := {(-3 / 2, -3 / 2), (-3 / 2, -1), (-3 / 2, 0), (-1, -1), (0, 0)}
  r₂ := {(-3 / 2, -3 / 2), (-3 / 2, -1), (-1, -1), (0, 0)}

/-- The apparent intermediate witness `-1/2` lies outside this carrier. -/
def outsiderSource : RationalPresentation where
  U := {-1, 0}
  r₁ := {(-1, -1), (0, 0), (-1 / 2, 0)}
  r₂ := {(-1, -1), (0, 0), (-1 / 2, -1)}

/-- The source search accepts a genuine intermediate witness distinct from
the query and rejects off-carrier witnesses, even when their edges exist. -/
theorem incoming_search_regression :
    (liftingCandidate {0} incomingSource target {-2, -3 / 2, -1, 0}).toStr.r₂
      (-2) (-1) ∧
    ¬ incomingSource.toStr.r₁ (-1) 0 ∧
    ¬ (liftingCandidate {0} outsiderSource target {-2, -1, 0}).toStr.r₂ (-2) (-1) := by
  decide +kernel

/-- An empty declared carrier produces no edges, even when the supplied
presentations contain edges and the anchor set is empty. -/
theorem empty_regression_suite :
    (liftingCandidate ∅ source target ∅).U = ∅ ∧
    (liftingCandidate ∅ source target ∅).r₁ = ∅ ∧
    (liftingCandidate ∅ source target ∅).r₂ = ∅ := by
  decide +kernel

end Alexander313.Carlson.ComputablePatternCandidateExamples
