import Alexander313.Carlson.PatternLiftingData

/-!
# The first relation of the normalized continuous lifting

The first relation of the common-carrier candidate is an order-bounded,
reflexive, transitive, convex relation. Its restrictions to the source and
target are exactly the given relations. The proof uses the least old upper
bounds from `ContinuityAnchors` to pass between the two given structures.

Carlson, *Patterns of resemblance of order 2*, Lemma 12.6, pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf.
-/

noncomputable section

namespace Alexander313.Carlson
namespace PatternLiftingConstruction
namespace Data

variable {α : Type*} [LinearOrder α]
variable {P Pplus Q : Str α} {U : Finset α} (D : Data P Pplus Q U)

include D

/-- The two given structures agree on the base at either relation level. -/
theorem source_target_rel_iff {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U)
    (k : Lvl) : Pplus.rel k x y ↔ Q.rel k x y :=
  (D.source_cont.1.rel_iff hx hy k).symm.trans (D.target_cont.1.rel_iff hx hy k)

/-- A source relation induces the same target relation between its anchors. -/
theorem source_anchor_rel (k : Lvl) {x y : α}
    (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) (hr : Pplus.rel k x y) :
    Q.rel k (Str.up P.U x) (Str.up P.U y) := by
  have hP : P.rel k (Str.up P.U x) (Str.up P.U y) :=
    D.source_cont.rel_up_of_rel D.source_pattern k hx hy
      (D.up_source hx) (D.up_source hy) hr
  exact (D.target_cont.1.rel_iff (D.up_source hx).1 (D.up_source hy).1 k).mp hP

theorem source_anchor_rel₁ {x y : α}
    (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) (hr : Pplus.r₁ x y) :
    Q.r₁ (Str.up P.U x) (Str.up P.U y) :=
  D.source_anchor_rel .one hx hy hr

theorem source_up_mono {x y : α}
    (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) (hxy : x ≤ y) :
    Str.up P.U x ≤ Str.up P.U y :=
  Str.up_mono (D.source_cont.2.1 x hx) (D.source_cont.2.1 y hy) hxy

theorem candidate_r₁_target {x y : α} (hx : x ∈ Q.U) (hy : y ∈ Q.U) :
    D.candidate.r₁ x y ↔ Q.r₁ x y := by
  classical
  simp only [candidate, if_pos hx, if_pos hy]

theorem candidate_r₁_from_target {x y : α} (hx : x ∈ Q.U) (hy : y ∉ Q.U) :
    D.candidate.r₁ x y ↔ x ≤ y ∧ Q.r₁ x (Str.up P.U y) := by
  classical
  simp only [candidate, if_pos hx, if_neg hy]

theorem candidate_r₁_to_target {x y : α} (hx : x ∉ Q.U) (hy : y ∈ Q.U) :
    D.candidate.r₁ x y ↔
      Pplus.r₁ x (Str.up P.U x) ∧ Q.r₁ (Str.up P.U x) y := by
  classical
  simp only [candidate, if_neg hx, if_pos hy]

theorem candidate_r₁_new {x y : α} (hx : x ∉ Q.U) (hy : y ∉ Q.U) :
    D.candidate.r₁ x y ↔ Pplus.r₁ x y := by
  classical
  simp only [candidate, if_neg hx, if_neg hy]

/-- The candidate preserves the entire first relation of the source. -/
theorem candidate_r₁_source {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) :
    D.candidate.r₁ x y ↔ Pplus.r₁ x y := by
  classical
  by_cases hxQ : x ∈ Q.U
  · have hxP : x ∈ P.U := (D.source_target_iff hx).mp hxQ
    by_cases hyQ : y ∈ Q.U
    · have hyP : y ∈ P.U := (D.source_target_iff hy).mp hyQ
      exact (D.candidate_r₁_target hxQ hyQ).trans
        (D.source_target_rel_iff hxP hyP .one).symm
    · rw [D.candidate_r₁_from_target hxQ hyQ]
      constructor
      · rintro ⟨hxy, hr⟩
        have hS : Pplus.r₁ x (Str.up P.U y) :=
          (D.source_target_rel_iff hxP (D.up_source hy).1 .one).mpr hr
        exact D.source_pattern.convex₁ x hx y hy _ (D.up_source_mem hy)
          hxy (D.up_source hy).2.1 hS
      · intro hr
        refine ⟨D.source_pattern.le₁ x hx y hy hr, ?_⟩
        have hP : P.r₁ x (Str.up P.U y) :=
          D.source_cont.rel_from_old_up D.source_pattern (k := .one)
            hxP hy (D.up_source hy) hr
        exact (D.target_cont.1.rel_iff hxP (D.up_source hy).1 .one).mp hP
  · by_cases hyQ : y ∈ Q.U
    · have hyP : y ∈ P.U := (D.source_target_iff hy).mp hyQ
      rw [D.candidate_r₁_to_target hxQ hyQ]
      constructor
      · rintro ⟨hxu, huy⟩
        have hS : Pplus.r₁ (Str.up P.U x) y :=
          (D.source_target_rel_iff (D.up_source hx).1 hyP .one).mpr huy
        exact D.source_pattern.trans₁ x hx _ (D.up_source_mem hx) y hy hxu hS
      · intro hr
        obtain ⟨hxu, huy⟩ := D.source_cont.factor_rel_to_old D.source_pattern
          (k := .one) hx hyP (D.up_source hx) hr
        exact ⟨hxu, (D.target_cont.1.rel_iff (D.up_source hx).1 hyP .one).mp huy⟩
    · exact D.candidate_r₁_new hxQ hyQ

/-- Every candidate first-relation edge respects the ambient order. -/
theorem candidate_le₁ {x y : α} (hx : x ∈ U) (hy : y ∈ U)
    (hr : D.candidate.r₁ x y) : x ≤ y := by
  classical
  by_cases hxQ : x ∈ Q.U
  · by_cases hyQ : y ∈ Q.U
    · exact D.target_pattern.le₁ x hxQ y hyQ
        ((D.candidate_r₁_target hxQ hyQ).mp hr)
    · exact ((D.candidate_r₁_from_target hxQ hyQ).mp hr).1
  · have hxS : x ∈ Pplus.U := D.source_of_not_target hx hxQ
    by_cases hyQ : y ∈ Q.U
    · have h := (D.candidate_r₁_to_target hxQ hyQ).mp hr
      exact (D.up_source hxS).2.1.trans
        (D.target_pattern.le₁ _ (D.up_target_mem hxS) y hyQ h.2)
    · have hyS : y ∈ Pplus.U := D.source_of_not_target hy hyQ
      exact D.source_pattern.le₁ x hxS y hyS
        ((D.candidate_r₁_new hxQ hyQ).mp hr)

theorem candidate_refl₁ {x : α} (hx : x ∈ U) : D.candidate.r₁ x x := by
  classical
  by_cases hxQ : x ∈ Q.U
  · exact (D.candidate_r₁_target hxQ hxQ).mpr (D.target_pattern.refl₁ x hxQ)
  · exact (D.candidate_r₁_new hxQ hxQ).mpr
      (D.source_pattern.refl₁ x (D.source_of_not_target hx hxQ))

/-- Transitivity of the candidate's first relation, including mixed triples. -/
theorem candidate_trans₁ {x y z : α}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : D.candidate.r₁ x y) (hyz : D.candidate.r₁ y z) :
    D.candidate.r₁ x z := by
  classical
  have hxz : x ≤ z := (D.candidate_le₁ hx hy hxy).trans (D.candidate_le₁ hy hz hyz)
  by_cases hxQ : x ∈ Q.U
  · by_cases hyQ : y ∈ Q.U
    · have hxyQ := (D.candidate_r₁_target hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · exact (D.candidate_r₁_target hxQ hzQ).mpr
          (D.target_pattern.trans₁ x hxQ y hyQ z hzQ hxyQ
            ((D.candidate_r₁_target hyQ hzQ).mp hyz))
      · have hzS := D.source_of_not_target hz hzQ
        have hyzQ := ((D.candidate_r₁_from_target hyQ hzQ).mp hyz).2
        exact (D.candidate_r₁_from_target hxQ hzQ).mpr ⟨hxz,
          D.target_pattern.trans₁ x hxQ y hyQ _ (D.up_target_mem hzS) hxyQ hyzQ⟩
    · have hyS := D.source_of_not_target hy hyQ
      have hxyQ := ((D.candidate_r₁_from_target hxQ hyQ).mp hxy).2
      by_cases hzQ : z ∈ Q.U
      · have hyzQ := ((D.candidate_r₁_to_target hyQ hzQ).mp hyz).2
        exact (D.candidate_r₁_target hxQ hzQ).mpr
          (D.target_pattern.trans₁ x hxQ _ (D.up_target_mem hyS) z hzQ hxyQ hyzQ)
      · have hzS := D.source_of_not_target hz hzQ
        have hyzS := (D.candidate_r₁_new hyQ hzQ).mp hyz
        exact (D.candidate_r₁_from_target hxQ hzQ).mpr ⟨hxz,
          D.target_pattern.trans₁ x hxQ _ (D.up_target_mem hyS) _ (D.up_target_mem hzS)
            hxyQ (D.source_anchor_rel₁ hyS hzS hyzS)⟩
  · have hxS := D.source_of_not_target hx hxQ
    by_cases hyQ : y ∈ Q.U
    · obtain ⟨hxu, huy⟩ := (D.candidate_r₁_to_target hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · exact (D.candidate_r₁_to_target hxQ hzQ).mpr ⟨hxu,
          D.target_pattern.trans₁ _ (D.up_target_mem hxS) y hyQ z hzQ huy
            ((D.candidate_r₁_target hyQ hzQ).mp hyz)⟩
      · have hzS := D.source_of_not_target hz hzQ
        have hyzQ := ((D.candidate_r₁_from_target hyQ hzQ).mp hyz).2
        have huuQ : Q.r₁ (Str.up P.U x) (Str.up P.U z) :=
          D.target_pattern.trans₁ _ (D.up_target_mem hxS) y hyQ _ (D.up_target_mem hzS)
            huy hyzQ
        have huuS : Pplus.r₁ (Str.up P.U x) (Str.up P.U z) :=
          (D.source_target_rel_iff (D.up_source hxS).1 (D.up_source hzS).1 .one).mpr huuQ
        have hxuS : Pplus.r₁ x (Str.up P.U z) :=
          D.source_pattern.trans₁ x hxS _ (D.up_source_mem hxS) _ (D.up_source_mem hzS)
            hxu huuS
        exact (D.candidate_r₁_new hxQ hzQ).mpr
          (D.source_pattern.convex₁ x hxS z hzS _ (D.up_source_mem hzS)
            hxz (D.up_source hzS).2.1 hxuS)
    · have hyS := D.source_of_not_target hy hyQ
      have hxyS := (D.candidate_r₁_new hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · obtain ⟨hyu, huz⟩ := (D.candidate_r₁_to_target hyQ hzQ).mp hyz
        have hxuS : Pplus.r₁ x (Str.up P.U y) :=
          D.source_pattern.trans₁ x hxS y hyS _ (D.up_source_mem hyS) hxyS hyu
        obtain ⟨hxu, _⟩ := D.source_cont.factor_rel_to_old D.source_pattern
          (k := .one) hxS (D.up_source hyS).1 (D.up_source hxS) hxuS
        exact (D.candidate_r₁_to_target hxQ hzQ).mpr ⟨hxu,
          D.target_pattern.trans₁ _ (D.up_target_mem hxS) _ (D.up_target_mem hyS) z hzQ
            (D.source_anchor_rel₁ hxS hyS hxyS) huz⟩
      · have hzS := D.source_of_not_target hz hzQ
        exact (D.candidate_r₁_new hxQ hzQ).mpr
          (D.source_pattern.trans₁ x hxS y hyS z hzS hxyS
            ((D.candidate_r₁_new hyQ hzQ).mp hyz))

/-- First-relation intervals remain convex after the two carriers are joined. -/
theorem candidate_convex₁ {x y z : α}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : x ≤ y) (hyz : y ≤ z) (hxz : D.candidate.r₁ x z) :
    D.candidate.r₁ x y := by
  classical
  by_cases hxQ : x ∈ Q.U
  · by_cases hyQ : y ∈ Q.U
    · by_cases hzQ : z ∈ Q.U
      · exact (D.candidate_r₁_target hxQ hyQ).mpr
          (D.target_pattern.convex₁ x hxQ y hyQ z hzQ hxy hyz
            ((D.candidate_r₁_target hxQ hzQ).mp hxz))
      · have hzS := D.source_of_not_target hz hzQ
        exact (D.candidate_r₁_target hxQ hyQ).mpr
          (D.target_pattern.convex₁ x hxQ y hyQ _ (D.up_target_mem hzS)
            hxy (hyz.trans (D.up_source hzS).2.1)
            ((D.candidate_r₁_from_target hxQ hzQ).mp hxz).2)
    · have hyS := D.source_of_not_target hy hyQ
      apply (D.candidate_r₁_from_target hxQ hyQ).mpr
      refine ⟨hxy, ?_⟩
      by_cases hzQ : z ∈ Q.U
      · exact D.target_pattern.convex₁ x hxQ _ (D.up_target_mem hyS) z hzQ
          (hxy.trans (D.up_source hyS).2.1) (D.source_le_old_up hyS hzQ hyz)
          ((D.candidate_r₁_target hxQ hzQ).mp hxz)
      · have hzS := D.source_of_not_target hz hzQ
        exact D.target_pattern.convex₁ x hxQ _ (D.up_target_mem hyS) _ (D.up_target_mem hzS)
          (hxy.trans (D.up_source hyS).2.1) (D.source_up_mono hyS hzS hyz)
          ((D.candidate_r₁_from_target hxQ hzQ).mp hxz).2
  · have hxS := D.source_of_not_target hx hxQ
    by_cases hyQ : y ∈ Q.U
    · have huy : Str.up P.U x ≤ y := D.source_le_old_up hxS hyQ hxy
      apply (D.candidate_r₁_to_target hxQ hyQ).mpr
      by_cases hzQ : z ∈ Q.U
      · obtain ⟨hxu, huz⟩ := (D.candidate_r₁_to_target hxQ hzQ).mp hxz
        exact ⟨hxu, D.target_pattern.convex₁ _ (D.up_target_mem hxS) y hyQ z hzQ
          huy hyz huz⟩
      · have hzS := D.source_of_not_target hz hzQ
        have hxzS := (D.candidate_r₁_new hxQ hzQ).mp hxz
        refine ⟨D.source_pattern.convex₁ x hxS _ (D.up_source_mem hxS) z hzS
          (D.up_source hxS).2.1 (huy.trans hyz) hxzS, ?_⟩
        exact D.target_pattern.convex₁ _ (D.up_target_mem hxS) y hyQ _ (D.up_target_mem hzS)
          huy (hyz.trans (D.up_source hzS).2.1) (D.source_anchor_rel₁ hxS hzS hxzS)
    · have hyS := D.source_of_not_target hy hyQ
      apply (D.candidate_r₁_new hxQ hyQ).mpr
      by_cases hzQ : z ∈ Q.U
      · obtain ⟨hxu, huz⟩ := (D.candidate_r₁_to_target hxQ hzQ).mp hxz
        have huuQ : Q.r₁ (Str.up P.U x) (Str.up P.U y) :=
          D.target_pattern.convex₁ _ (D.up_target_mem hxS) _ (D.up_target_mem hyS) z hzQ
            (D.source_up_mono hxS hyS hxy) (D.source_le_old_up hyS hzQ hyz) huz
        have huuS : Pplus.r₁ (Str.up P.U x) (Str.up P.U y) :=
          (D.source_target_rel_iff (D.up_source hxS).1 (D.up_source hyS).1 .one).mpr huuQ
        have hxyu : Pplus.r₁ x (Str.up P.U y) :=
          D.source_pattern.trans₁ x hxS _ (D.up_source_mem hxS) _ (D.up_source_mem hyS)
            hxu huuS
        exact D.source_pattern.convex₁ x hxS y hyS _ (D.up_source_mem hyS)
          hxy (D.up_source hyS).2.1 hxyu
      · have hzS := D.source_of_not_target hz hzQ
        exact D.source_pattern.convex₁ x hxS y hyS z hzS hxy hyz
          ((D.candidate_r₁_new hxQ hzQ).mp hxz)

end Data
end PatternLiftingConstruction
end Alexander313.Carlson
