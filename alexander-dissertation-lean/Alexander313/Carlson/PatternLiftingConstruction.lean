import Alexander313.Carlson.PatternLiftingSecond
import Alexander313.Carlson.PatternLiftingContinuity
import Alexander313.Carlson.LiftingCofinality

/-!
# The continuous minimal lifting on a normalized carrier

The two relation calculations assemble into a pure pattern containing both
the extended source and the old target. Taking the least old upper bound
preserves each relation, which proves continuity over the old target.

Every mixed edge is forced in any pattern containing the two given patterns:
first edges follow from convexity and transitivity, while incoming second
edges follow from respect and transitivity. Thus the explicit candidate is
already a minimal lifting, without passing to an intersection of liftings.

Carlson, *Patterns of resemblance of order 2*, Lemma 12.6, pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 49–56 of the author's October 16, 2008 manuscript.
-/

noncomputable section

namespace Alexander313.Carlson
namespace PatternLiftingConstruction
namespace Data

variable {α : Type*} [LinearOrder α]
variable {P Pplus Q : Str α} {U : Finset α} (D : Data P Pplus Q U)

include D

/-- All eight pure-pattern axioms hold for the explicit candidate. -/
theorem candidate_isPattern : D.candidate.IsPattern where
  le₁ := fun _ hx _ hy hr => D.candidate_le₁ hx hy hr
  sub₂ := fun _ hx _ hy hr => D.candidate_sub₂ hx hy hr
  refl₁ := fun _ hx => D.candidate_refl₁ hx
  refl₂ := fun _ hx => D.candidate_refl₂ hx
  trans₁ := fun _ hx _ hy _ hz hxy hyz => D.candidate_trans₁ hx hy hz hxy hyz
  trans₂ := fun _ hx _ hy _ hz hxy hyz => D.candidate_trans₂ hx hy hz hxy hyz
  convex₁ := fun _ hx _ hy _ hz hxy hyz hxz =>
    D.candidate_convex₁ hx hy hz hxy hyz hxz
  respect₂ := fun _ hx _ hy _ hz hxy hyz hxz hyz' =>
    D.candidate_respect₂ hx hy hz hxy hyz hxz hyz'

theorem candidate_target_sub : Str.IsSub Q D.candidate := by
  refine ⟨fun _ hx => D.target_mem hx, ?_⟩
  intro x hx y hy
  exact ⟨(D.candidate_r₁_target hx hy).symm, (D.candidate_r₂_target hx hy).symm⟩

theorem candidate_source_sub : Str.IsSub Pplus D.candidate := by
  refine ⟨fun _ hx => D.source_mem hx, ?_⟩
  intro x hx y hy
  exact ⟨(D.candidate_r₁_source hx hy).symm, (D.candidate_r₂_source hx hy).symm⟩

/-- The candidate realizes the supplied normalized arithmetic lifting. -/
theorem candidate_lifting : PatternLifting P Pplus Q D.candidate id id where
  source_pattern := D.source_pattern
  target_pattern := D.candidate_isPattern
  source_sub := D.source_cont.1
  target_sub := D.candidate_target_sub
  arithmetic := D.arithmetic
  relations := fun x hx y hy => D.candidate_source_sub.2 x hx y hy

theorem up_target_eq_source {x : α} (hx : x ∈ Pplus.U) :
    Str.up Q.U x = Str.up P.U x :=
  D.arithmetic.up_image hx

/-- Passing to the least old target upper bound preserves the first relation. -/
theorem candidate_r₁_up_target {x y : α} (hx : x ∈ U) (hy : y ∈ U)
    (hr : D.candidate.r₁ x y) : Q.r₁ (Str.up Q.U x) (Str.up Q.U y) := by
  classical
  by_cases hxQ : x ∈ Q.U
  · rw [Str.up_of_mem hxQ]
    by_cases hyQ : y ∈ Q.U
    · rw [Str.up_of_mem hyQ]
      exact (D.candidate_r₁_target hxQ hyQ).mp hr
    · have hyS := D.source_of_not_target hy hyQ
      rw [D.up_target_eq_source hyS]
      exact ((D.candidate_r₁_from_target hxQ hyQ).mp hr).2
  · have hxS := D.source_of_not_target hx hxQ
    rw [D.up_target_eq_source hxS]
    by_cases hyQ : y ∈ Q.U
    · rw [Str.up_of_mem hyQ]
      exact ((D.candidate_r₁_to_target hxQ hyQ).mp hr).2
    · have hyS := D.source_of_not_target hy hyQ
      rw [D.up_target_eq_source hyS]
      exact D.source_anchor_rel₁ hxS hyS ((D.candidate_r₁_new hxQ hyQ).mp hr)

/-- Passing to the least old target upper bound preserves the second relation. -/
theorem candidate_r₂_up_target {x y : α} (hx : x ∈ U) (hy : y ∈ U)
    (hr : D.candidate.r₂ x y) : Q.r₂ (Str.up Q.U x) (Str.up Q.U y) := by
  classical
  by_cases hxQ : x ∈ Q.U
  · rw [Str.up_of_mem hxQ]
    by_cases hyQ : y ∈ Q.U
    · rw [Str.up_of_mem hyQ]
      exact (D.candidate_r₂_target hxQ hyQ).mp hr
    · have hyS := D.source_of_not_target hy hyQ
      rw [D.up_target_eq_source hyS]
      exact D.candidate_r₂_target_anchor hxQ hyS hr
  · have hxS := D.source_of_not_target hx hxQ
    rw [D.up_target_eq_source hxS]
    by_cases hyQ : y ∈ Q.U
    · rw [Str.up_of_mem hyQ]
      exact ((D.candidate_r₂_to_target hxQ hyQ).mp hr).2
    · have hyS := D.source_of_not_target hy hyQ
      rw [D.up_target_eq_source hyS]
      exact D.source_anchor_rel₂ hxS hyS ((D.candidate_r₂_new hxQ hyQ).mp hr)

/-- The constructed extension of the old target is continuous. -/
theorem candidate_continuous : Str.Continuous Q D.candidate := by
  refine ⟨D.candidate_target_sub, D.arithmetic.target_bounded, ?_, ?_⟩
  · intro p x y hx hy hp _ hr
    have hpx := Str.up_spec (D.arithmetic.target_bounded x hx)
    have hpy := Str.up_spec (D.arithmetic.target_bounded y hy)
    refine ⟨Str.up Q.U y, hpy, ?_⟩
    have heq : Str.up Q.U x = p := hpx.unique hp
    simpa only [Str.rel, heq] using D.candidate_r₁_up_target hx hy hr
  · intro p x y hx hy hp _ hr
    have hpx := Str.up_spec (D.arithmetic.target_bounded x hx)
    have hpy := Str.up_spec (D.arithmetic.target_bounded y hy)
    refine ⟨Str.up Q.U y, hpy, ?_⟩
    have heq : Str.up Q.U x = p := hpx.unique hp
    simpa only [Str.rel, heq] using D.candidate_r₂_up_target hx hy hr

/-- Every candidate edge is forced in any pattern containing the given
source and target on the same carrier. -/
theorem candidate_coversInto {R : Str α} (hR : R.IsPattern) (hU : R.U = U)
    (hsource : Str.IsSub Pplus R) (htarget : Str.IsSub Q R) :
    Str.CoversInto D.candidate R id := by
  classical
  have hs₁ {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) :
      Pplus.r₁ x y → R.r₁ x y := (hsource.2 x hx y hy).1.mp
  have hs₂ {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) :
      Pplus.r₂ x y → R.r₂ x y := (hsource.2 x hx y hy).2.mp
  have ht₁ {x y : α} (hx : x ∈ Q.U) (hy : y ∈ Q.U) :
      Q.r₁ x y → R.r₁ x y := (htarget.2 x hx y hy).1.mp
  have ht₂ {x y : α} (hx : x ∈ Q.U) (hy : y ∈ Q.U) :
      Q.r₂ x y → R.r₂ x y := (htarget.2 x hx y hy).2.mp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hU.symm ▸ hx
  · intro x hx y hy hxy
    exact hxy
  · intro x hx y hy hr
    by_cases hxQ : x ∈ Q.U
    · by_cases hyQ : y ∈ Q.U
      · exact ht₁ hxQ hyQ ((D.candidate_r₁_target hxQ hyQ).mp hr)
      · have hyS := D.source_of_not_target hy hyQ
        obtain ⟨hxy, hxyUp⟩ := (D.candidate_r₁_from_target hxQ hyQ).mp hr
        exact hR.convex₁ x (htarget.1 hxQ) y (hsource.1 hyS)
          _ (htarget.1 (D.up_target_mem hyS)) hxy (D.up_source hyS).2.1
          (ht₁ hxQ (D.up_target_mem hyS) hxyUp)
    · have hxS := D.source_of_not_target hx hxQ
      by_cases hyQ : y ∈ Q.U
      · obtain ⟨hxUp, hUpy⟩ := (D.candidate_r₁_to_target hxQ hyQ).mp hr
        exact hR.trans₁ x (hsource.1 hxS) _ (hsource.1 (D.up_source_mem hxS))
          y (htarget.1 hyQ) (hs₁ hxS (D.up_source_mem hxS) hxUp)
          (ht₁ (D.up_target_mem hxS) hyQ hUpy)
      · have hyS := D.source_of_not_target hy hyQ
        exact hs₁ hxS hyS ((D.candidate_r₁_new hxQ hyQ).mp hr)
  · intro x hx y hy hr
    by_cases hxQ : x ∈ Q.U
    · by_cases hyQ : y ∈ Q.U
      · exact ht₂ hxQ hyQ ((D.candidate_r₂_target hxQ hyQ).mp hr)
      · have hyS := D.source_of_not_target hy hyQ
        obtain ⟨a, ha, hxa, haUp, hxaUp, hay⟩ :=
          (D.candidate_r₂_from_target hxQ hyQ).mp hr
        have hxa' : R.r₂ x a :=
          hR.respect₂ x (htarget.1 hxQ) a (hsource.1 ha)
            _ (hsource.1 (D.up_source_mem ha)) hxa (D.up_source ha).2.1
            (ht₂ hxQ (D.up_target_mem ha) hxaUp)
            (hs₁ ha (D.up_source_mem ha) haUp)
        exact hR.trans₂ x (htarget.1 hxQ) a (hsource.1 ha) y (hsource.1 hyS)
          hxa' (hs₂ ha hyS hay)
    · have hxS := D.source_of_not_target hx hxQ
      by_cases hyQ : y ∈ Q.U
      · obtain ⟨hxUp, hUpy⟩ := (D.candidate_r₂_to_target hxQ hyQ).mp hr
        exact hR.trans₂ x (hsource.1 hxS) _ (hsource.1 (D.up_source_mem hxS))
          y (htarget.1 hyQ) (hs₂ hxS (D.up_source_mem hxS) hxUp)
          (ht₂ (D.up_target_mem hxS) hyQ hUpy)
      · have hyS := D.source_of_not_target hy hyQ
        exact hs₂ hxS hyS ((D.candidate_r₂_new hxQ hyQ).mp hr)

/-- The explicit continuous candidate is a minimal pattern lifting. -/
theorem candidate_isMinimal : PatternLifting.IsMinimal P Pplus Q D.candidate id := by
  intro R g hU E
  have hRU : R.U = U := hU
  have hE : ArithmeticLifting P.U Pplus.U Q.U U id g := by
    simpa only [hRU] using E.arithmetic
  have hg {x : α} (hx : x ∈ Pplus.U) : g x = x :=
    (D.arithmetic.unique hE hx).symm
  have hsource : Str.IsSub Pplus R := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hRU.symm ▸ D.source_mem hx
    · intro x hx y hy
      simpa only [hg hx, hg hy] using E.relations x hx y hy
  exact D.candidate_coversInto E.target_pattern hRU hsource E.target_sub

/-- Continuous normalized source data give a continuous minimal lifting on
the supplied arithmetic carrier. -/
theorem exists_continuous_minimal :
    ∃ R : Str α, R.U = U ∧ PatternLifting P Pplus Q R id id ∧
      PatternLifting.IsMinimal P Pplus Q R id ∧ Str.Continuous Q R :=
  ⟨D.candidate, rfl, D.candidate_lifting, D.candidate_isMinimal, D.candidate_continuous⟩

/-- Cofinal validity is preserved by the constructed minimal lifting. -/
theorem candidate_cofinallyValid (hcv : Str.CofinallyValid P Pplus) :
    Str.CofinallyValid Q D.candidate :=
  D.candidate_lifting.cofinallyValid D.candidate_isMinimal hcv

end Data
end PatternLiftingConstruction
end Alexander313.Carlson
