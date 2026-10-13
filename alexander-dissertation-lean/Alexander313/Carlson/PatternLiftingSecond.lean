import Alexander313.Carlson.PatternLiftingFirst

/-!
# The second relation of the normalized continuous lifting

The existential incoming edge in Carlson's Lemma 12.6 is stable under
composition and respect. Its source bridge also makes the restriction to
the extended source exact. Together with the first-relation calculations,
these establish the remaining pure-pattern axioms for the candidate.

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

theorem candidate_r₂_target {x y : α} (hx : x ∈ Q.U) (hy : y ∈ Q.U) :
    D.candidate.r₂ x y ↔ Q.r₂ x y := by
  simp only [candidate, if_pos hx, if_pos hy]

theorem candidate_r₂_new {x y : α} (hx : x ∉ Q.U) (hy : y ∉ Q.U) :
    D.candidate.r₂ x y ↔ Pplus.r₂ x y := by
  simp only [candidate, if_neg hx, if_neg hy]

theorem candidate_r₂_from_target {x y : α} (hx : x ∈ Q.U) (hy : y ∉ Q.U) :
    D.candidate.r₂ x y ↔
      ∃ a ∈ Pplus.U, x ≤ a ∧ Pplus.r₁ a (Str.up P.U a) ∧
        Q.r₂ x (Str.up P.U a) ∧ Pplus.r₂ a y := by
  simp only [candidate, if_pos hx, if_neg hy]

theorem candidate_r₂_to_target {x y : α} (hx : x ∉ Q.U) (hy : y ∈ Q.U) :
    D.candidate.r₂ x y ↔
      Pplus.r₂ x (Str.up P.U x) ∧ Q.r₂ (Str.up P.U x) y := by
  simp only [candidate, if_neg hx, if_pos hy]

theorem source_anchor_rel₂ {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U)
    (hr : Pplus.r₂ x y) : Q.r₂ (Str.up P.U x) (Str.up P.U y) :=
  D.source_anchor_rel .two hx hy hr

/-- The outgoing normal form also applies when its source is in the base. -/
theorem candidate_r₂_source_to_target {x y : α}
    (hx : x ∈ Pplus.U) (hy : y ∈ Q.U) :
    D.candidate.r₂ x y ↔
      Pplus.r₂ x (Str.up P.U x) ∧ Q.r₂ (Str.up P.U x) y := by
  by_cases hxQ : x ∈ Q.U
  · have hxP : x ∈ P.U := (D.source_target_iff hx).mp hxQ
    rw [D.candidate_r₂_target hxQ hy, Str.up_of_mem hxP]
    constructor
    · exact fun h => ⟨D.source_pattern.refl₂ x hx, h⟩
    · exact fun h => h.2
  · exact D.candidate_r₂_to_target hxQ hy

/-- The bridge normal form also applies when its destination is in the base. -/
theorem candidate_r₂_target_to_source {x y : α}
    (hx : x ∈ Q.U) (hy : y ∈ Pplus.U) :
    D.candidate.r₂ x y ↔
      ∃ a ∈ Pplus.U, x ≤ a ∧ Pplus.r₁ a (Str.up P.U a) ∧
        Q.r₂ x (Str.up P.U a) ∧ Pplus.r₂ a y := by
  by_cases hyQ : y ∈ Q.U
  · have hyP : y ∈ P.U := (D.source_target_iff hy).mp hyQ
    rw [D.candidate_r₂_target hx hyQ]
    constructor
    · intro hxy
      refine ⟨y, hy, D.target_pattern.rel_le .two hx hyQ hxy, ?_, ?_,
        D.source_pattern.refl₂ y hy⟩
      · simpa only [Str.up_of_mem hyP] using D.source_pattern.refl₁ y hy
      · simpa only [Str.up_of_mem hyP] using hxy
    · rintro ⟨a, ha, _, _, hxa, hay⟩
      have hay' : Q.r₂ (Str.up P.U a) y := by
        simpa only [Str.up_of_mem hyP] using D.source_anchor_rel₂ ha hy hay
      exact D.target_pattern.trans₂ x hx _ (D.up_target_mem ha) y hyQ hxa hay'
  · exact D.candidate_r₂_from_target hx hyQ

/-- An incoming second edge reaches the old upper bound of its destination. -/
theorem candidate_r₂_target_anchor {x y : α}
    (hx : x ∈ Q.U) (hy : y ∈ Pplus.U) (hr : D.candidate.r₂ x y) :
    Q.r₂ x (Str.up P.U y) := by
  obtain ⟨a, ha, _, _, hxa, hay⟩ := (D.candidate_r₂_target_to_source hx hy).mp hr
  exact D.target_pattern.trans₂ x hx _ (D.up_target_mem ha) _ (D.up_target_mem hy)
    hxa (D.source_anchor_rel₂ ha hy hay)

/-- The candidate reflects and preserves the second relation on the source. -/
theorem candidate_r₂_source {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ Pplus.U) :
    D.candidate.r₂ x y ↔ Pplus.r₂ x y := by
  by_cases hxQ : x ∈ Q.U
  · have hxP : x ∈ P.U := (D.source_target_iff hx).mp hxQ
    rw [D.candidate_r₂_target_to_source hxQ hy]
    constructor
    · rintro ⟨a, ha, hxa, haUp, hxaUp, hay⟩
      have hxaUp' : Pplus.r₂ x (Str.up P.U a) :=
        (D.source_target_rel_iff hxP (D.up_source ha).1 .two).mpr hxaUp
      have hxa' : Pplus.r₂ x a :=
        D.source_pattern.respect₂ x hx a ha _ (D.up_source_mem ha)
          hxa (D.up_source ha).2.1 hxaUp' haUp
      exact D.source_pattern.trans₂ x hx a ha y hy hxa' hay
    · intro hxy
      refine ⟨x, hx, le_rfl, ?_, ?_, hxy⟩
      · simpa only [Str.up_of_mem hxP] using D.source_pattern.refl₁ x hx
      · simpa only [Str.up_of_mem hxP] using D.target_pattern.refl₂ x hxQ
  · by_cases hyQ : y ∈ Q.U
    · have hyP : y ∈ P.U := (D.source_target_iff hy).mp hyQ
      rw [D.candidate_r₂_to_target hxQ hyQ]
      constructor
      · rintro ⟨hxUp, hUpy⟩
        exact D.source_pattern.trans₂ x hx _ (D.up_source_mem hx) y hy hxUp
          ((D.source_target_rel_iff (D.up_source hx).1 hyP .two).mpr hUpy)
      · intro hxy
        obtain ⟨hxUp, hUpy⟩ :=
          D.source_cont.factor_rel_to_old D.source_pattern (k := .two)
            hx hyP (D.up_source hx) hxy
        exact ⟨hxUp, (D.target_cont.1.rel_iff (D.up_source hx).1 hyP .two).mp hUpy⟩
    · exact D.candidate_r₂_new hxQ hyQ

theorem candidate_sub₂ {x y : α} (hx : x ∈ U) (hy : y ∈ U)
    (hr : D.candidate.r₂ x y) : D.candidate.r₁ x y := by
  by_cases hxQ : x ∈ Q.U
  · by_cases hyQ : y ∈ Q.U
    · exact (D.candidate_r₁_target hxQ hyQ).mpr
        (D.target_pattern.sub₂ x hxQ y hyQ ((D.candidate_r₂_target hxQ hyQ).mp hr))
    · have hyS := D.source_of_not_target hy hyQ
      obtain ⟨a, ha, hxa, _, _, hay⟩ := (D.candidate_r₂_from_target hxQ hyQ).mp hr
      exact (D.candidate_r₁_from_target hxQ hyQ).mpr
        ⟨hxa.trans (D.source_pattern.rel_le .two ha hyS hay),
          D.target_pattern.sub₂ x hxQ _ (D.up_target_mem hyS)
            (D.candidate_r₂_target_anchor hxQ hyS hr)⟩
  · have hxS := D.source_of_not_target hx hxQ
    by_cases hyQ : y ∈ Q.U
    · obtain ⟨hxUp, hUpy⟩ := (D.candidate_r₂_to_target hxQ hyQ).mp hr
      exact (D.candidate_r₁_to_target hxQ hyQ).mpr
        ⟨D.source_pattern.sub₂ x hxS _ (D.up_source_mem hxS) hxUp,
          D.target_pattern.sub₂ _ (D.up_target_mem hxS) y hyQ hUpy⟩
    · have hyS := D.source_of_not_target hy hyQ
      exact (D.candidate_r₁_new hxQ hyQ).mpr
        (D.source_pattern.sub₂ x hxS y hyS ((D.candidate_r₂_new hxQ hyQ).mp hr))

theorem candidate_refl₂ {x : α} (hx : x ∈ U) : D.candidate.r₂ x x := by
  by_cases hxQ : x ∈ Q.U
  · exact (D.candidate_r₂_target hxQ hxQ).mpr (D.target_pattern.refl₂ x hxQ)
  · exact (D.candidate_r₂_new hxQ hxQ).mpr
      (D.source_pattern.refl₂ x (D.source_of_not_target hx hxQ))

/-- Factor a source second edge at its first base point, in target notation. -/
theorem source_r₂_to_base {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ P.U)
    (hr : Pplus.r₂ x y) :
    Pplus.r₂ x (Str.up P.U x) ∧ Q.r₂ (Str.up P.U x) y :=
  (D.candidate_r₂_source_to_target hx (D.base_target_mem hy)).mp
    ((D.candidate_r₂_source hx (D.base_source_mem hy)).mpr hr)

theorem candidate_trans₂ {x y z : α} (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : D.candidate.r₂ x y) (hyz : D.candidate.r₂ y z) : D.candidate.r₂ x z := by
  by_cases hxQ : x ∈ Q.U
  · by_cases hyQ : y ∈ Q.U
    · have hxyQ := (D.candidate_r₂_target hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · exact (D.candidate_r₂_target hxQ hzQ).mpr
          (D.target_pattern.trans₂ x hxQ y hyQ z hzQ hxyQ
            ((D.candidate_r₂_target hyQ hzQ).mp hyz))
      · obtain ⟨a, ha, hya, haUp, hyaUp, haz⟩ :=
          (D.candidate_r₂_from_target hyQ hzQ).mp hyz
        exact (D.candidate_r₂_from_target hxQ hzQ).mpr
          ⟨a, ha, (D.target_pattern.rel_le .two hxQ hyQ hxyQ).trans hya, haUp,
            D.target_pattern.trans₂ x hxQ y hyQ _ (D.up_target_mem ha) hxyQ hyaUp,
            haz⟩
    · have hyS := D.source_of_not_target hy hyQ
      obtain ⟨a, ha, hxa, haUp, hxaUp, hay⟩ :=
        (D.candidate_r₂_from_target hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · obtain ⟨hyUp, hUpz⟩ := (D.candidate_r₂_to_target hyQ hzQ).mp hyz
        have haUpY : Pplus.r₂ a (Str.up P.U y) :=
          D.source_pattern.trans₂ a ha y hyS _ (D.up_source_mem hyS) hay hyUp
        have hUpaUpy : Q.r₂ (Str.up P.U a) (Str.up P.U y) :=
          (D.source_r₂_to_base ha (D.up_source hyS).1 haUpY).2
        exact (D.candidate_r₂_target hxQ hzQ).mpr
          (D.target_pattern.trans₂ x hxQ _ (D.up_target_mem hyS) z hzQ
            (D.target_pattern.trans₂ x hxQ _ (D.up_target_mem ha) _
              (D.up_target_mem hyS) hxaUp hUpaUpy) hUpz)
      · have hzS := D.source_of_not_target hz hzQ
        exact (D.candidate_r₂_from_target hxQ hzQ).mpr
          ⟨a, ha, hxa, haUp, hxaUp,
            D.source_pattern.trans₂ a ha y hyS z hzS hay
              ((D.candidate_r₂_new hyQ hzQ).mp hyz)⟩
  · have hxS := D.source_of_not_target hx hxQ
    by_cases hyQ : y ∈ Q.U
    · obtain ⟨hxUp, hUpy⟩ := (D.candidate_r₂_to_target hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · exact (D.candidate_r₂_to_target hxQ hzQ).mpr
          ⟨hxUp, D.target_pattern.trans₂ _ (D.up_target_mem hxS) y hyQ z hzQ hUpy
            ((D.candidate_r₂_target hyQ hzQ).mp hyz)⟩
      · have hzS := D.source_of_not_target hz hzQ
        obtain ⟨a, ha, hya, haUp, hyaUp, haz⟩ :=
          (D.candidate_r₂_from_target hyQ hzQ).mp hyz
        have hUpxUpa : Q.r₂ (Str.up P.U x) (Str.up P.U a) :=
          D.target_pattern.trans₂ _ (D.up_target_mem hxS) y hyQ _
            (D.up_target_mem ha) hUpy hyaUp
        have hxUpa : Pplus.r₂ x (Str.up P.U a) :=
          D.source_pattern.trans₂ x hxS _ (D.up_source_mem hxS) _ (D.up_source_mem ha)
            hxUp ((D.source_target_rel_iff (D.up_source hxS).1 (D.up_source ha).1
              .two).mpr hUpxUpa)
        have hxa : x ≤ a :=
          (D.candidate_le₁ hx hy (D.candidate_sub₂ hx hy hxy)).trans hya
        have hxaS : Pplus.r₂ x a :=
          D.source_pattern.respect₂ x hxS a ha _ (D.up_source_mem ha)
            hxa (D.up_source ha).2.1 hxUpa haUp
        exact (D.candidate_r₂_new hxQ hzQ).mpr
          (D.source_pattern.trans₂ x hxS a ha z hzS hxaS haz)
    · have hyS := D.source_of_not_target hy hyQ
      have hxyS := (D.candidate_r₂_new hxQ hyQ).mp hxy
      by_cases hzQ : z ∈ Q.U
      · obtain ⟨hyUp, hUpz⟩ := (D.candidate_r₂_to_target hyQ hzQ).mp hyz
        have hxUpY : Pplus.r₂ x (Str.up P.U y) :=
          D.source_pattern.trans₂ x hxS y hyS _ (D.up_source_mem hyS) hxyS hyUp
        obtain ⟨hxUp, hUpxUpy⟩ := D.source_r₂_to_base hxS (D.up_source hyS).1 hxUpY
        exact (D.candidate_r₂_to_target hxQ hzQ).mpr
          ⟨hxUp, D.target_pattern.trans₂ _ (D.up_target_mem hxS) _
            (D.up_target_mem hyS) z hzQ hUpxUpy hUpz⟩
      · have hzS := D.source_of_not_target hz hzQ
        exact (D.candidate_r₂_new hxQ hzQ).mpr
          (D.source_pattern.trans₂ x hxS y hyS z hzS hxyS
            ((D.candidate_r₂_new hyQ hzQ).mp hyz))

theorem candidate_respect₂ {x y z : α} (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : x ≤ y) (hyz : y ≤ z) (hxz : D.candidate.r₂ x z)
    (hyz₁ : D.candidate.r₁ y z) : D.candidate.r₂ x y := by
  by_cases hxQ : x ∈ Q.U
  · by_cases hzQ : z ∈ Q.U
    · have hxzQ := (D.candidate_r₂_target hxQ hzQ).mp hxz
      by_cases hyQ : y ∈ Q.U
      · exact (D.candidate_r₂_target hxQ hyQ).mpr
          (D.target_pattern.respect₂ x hxQ y hyQ z hzQ hxy hyz hxzQ
            ((D.candidate_r₁_target hyQ hzQ).mp hyz₁))
      · have hyS := D.source_of_not_target hy hyQ
        obtain ⟨hyUp, hUpz⟩ := (D.candidate_r₁_to_target hyQ hzQ).mp hyz₁
        have hxUp : Q.r₂ x (Str.up P.U y) :=
          D.target_pattern.respect₂ x hxQ _ (D.up_target_mem hyS) z hzQ
            (hxy.trans (D.up_source hyS).2.1)
            (D.source_le_old_up hyS hzQ hyz) hxzQ hUpz
        exact (D.candidate_r₂_from_target hxQ hyQ).mpr
          ⟨y, hyS, hxy, hyUp, hxUp, D.source_pattern.refl₂ y hyS⟩
    · have hzS := D.source_of_not_target hz hzQ
      by_cases hyQ : y ∈ Q.U
      · have hyUp : Q.r₁ y (Str.up P.U z) :=
          ((D.candidate_r₁_from_target hyQ hzQ).mp hyz₁).2
        exact (D.candidate_r₂_target hxQ hyQ).mpr
          (D.target_pattern.respect₂ x hxQ y hyQ _ (D.up_target_mem hzS)
            hxy (hyz.trans (D.up_source hzS).2.1)
            (D.candidate_r₂_target_anchor hxQ hzS hxz) hyUp)
      · have hyS := D.source_of_not_target hy hyQ
        have hyzS := (D.candidate_r₁_new hyQ hzQ).mp hyz₁
        obtain ⟨a, ha, hxa, haUp, hxaUp, haz⟩ :=
          (D.candidate_r₂_from_target hxQ hzQ).mp hxz
        by_cases hay : a ≤ y
        · exact (D.candidate_r₂_from_target hxQ hyQ).mpr
            ⟨a, ha, hxa, haUp, hxaUp,
              D.source_pattern.respect₂ a ha y hyS z hzS hay hyz haz hyzS⟩
        · have hya : y ≤ a := (not_le.mp hay).le
          have hayz : a ≤ z := D.source_pattern.rel_le .two ha hzS haz
          have hyaS : Pplus.r₁ y a :=
            D.source_pattern.convex₁ y hyS a ha z hzS hya hayz hyzS
          have hyUpa : Pplus.r₁ y (Str.up P.U a) :=
            D.source_pattern.trans₁ y hyS a ha _ (D.up_source_mem ha) hyaS haUp
          obtain ⟨hyUp, hUpyUpa⟩ :=
            D.source_cont.factor_rel_to_old D.source_pattern (k := .one)
              hyS (D.up_source ha).1 (D.up_source hyS) hyUpa
          have hUpyUpaQ : Q.r₁ (Str.up P.U y) (Str.up P.U a) :=
            (D.target_cont.1.rel_iff (D.up_source hyS).1 (D.up_source ha).1 .one).mp hUpyUpa
          have hxUp : Q.r₂ x (Str.up P.U y) :=
            D.target_pattern.respect₂ x hxQ _ (D.up_target_mem hyS) _ (D.up_target_mem ha)
              (hxy.trans (D.up_source hyS).2.1)
              (D.target_pattern.le₁ _ (D.up_target_mem hyS) _ (D.up_target_mem ha) hUpyUpaQ)
              hxaUp hUpyUpaQ
          exact (D.candidate_r₂_from_target hxQ hyQ).mpr
            ⟨y, hyS, hxy, hyUp, hxUp, D.source_pattern.refl₂ y hyS⟩
  · have hxS := D.source_of_not_target hx hxQ
    by_cases hzQ : z ∈ Q.U
    · obtain ⟨hxUp, hUpz⟩ := (D.candidate_r₂_to_target hxQ hzQ).mp hxz
      by_cases hyQ : y ∈ Q.U
      · exact (D.candidate_r₂_to_target hxQ hyQ).mpr
          ⟨hxUp, D.target_pattern.respect₂ _ (D.up_target_mem hxS) y hyQ z hzQ
            (D.source_le_old_up hxS hyQ hxy) hyz hUpz
            ((D.candidate_r₁_target hyQ hzQ).mp hyz₁)⟩
      · have hyS := D.source_of_not_target hy hyQ
        obtain ⟨hyUp, hUpyz⟩ := (D.candidate_r₁_to_target hyQ hzQ).mp hyz₁
        have hUpxUpyLe : Str.up P.U x ≤ Str.up P.U y :=
          Str.up_mono (D.source_cont.2.1 x hxS) (D.source_cont.2.1 y hyS) hxy
        have hUpxUpy : Q.r₂ (Str.up P.U x) (Str.up P.U y) :=
          D.target_pattern.respect₂ _ (D.up_target_mem hxS) _ (D.up_target_mem hyS) z hzQ
            hUpxUpyLe (D.source_le_old_up hyS hzQ hyz) hUpz hUpyz
        have hxUpy : Pplus.r₂ x (Str.up P.U y) :=
          D.source_pattern.trans₂ x hxS _ (D.up_source_mem hxS) _ (D.up_source_mem hyS)
            hxUp ((D.source_target_rel_iff (D.up_source hxS).1 (D.up_source hyS).1
              .two).mpr hUpxUpy)
        exact (D.candidate_r₂_new hxQ hyQ).mpr
          (D.source_pattern.respect₂ x hxS y hyS _ (D.up_source_mem hyS)
            hxy (D.up_source hyS).2.1 hxUpy hyUp)
    · have hzS := D.source_of_not_target hz hzQ
      have hxzS := (D.candidate_r₂_new hxQ hzQ).mp hxz
      by_cases hyQ : y ∈ Q.U
      · have hUpxY : Str.up P.U x ≤ y := D.source_le_old_up hxS hyQ hxy
        have hyzLt : y < z := lt_of_le_of_ne hyz (fun heq => hzQ (heq ▸ hyQ))
        obtain ⟨hxUp, hUpxUpz⟩ :=
          D.source_cont.factor_rel_cross D.source_pattern (k := .two)
            hxS hzS (D.up_source hxS) (D.up_source hzS) (hUpxY.trans_lt hyzLt) hxzS
        have hUpxUpzQ : Q.r₂ (Str.up P.U x) (Str.up P.U z) :=
          (D.target_cont.1.rel_iff (D.up_source hxS).1 (D.up_source hzS).1 .two).mp hUpxUpz
        exact (D.candidate_r₂_to_target hxQ hyQ).mpr
          ⟨hxUp, D.target_pattern.respect₂ _ (D.up_target_mem hxS) y hyQ _ (D.up_target_mem hzS)
            hUpxY (hyz.trans (D.up_source hzS).2.1) hUpxUpzQ
            ((D.candidate_r₁_from_target hyQ hzQ).mp hyz₁).2⟩
      · have hyS := D.source_of_not_target hy hyQ
        exact (D.candidate_r₂_new hxQ hyQ).mpr
          (D.source_pattern.respect₂ x hxS y hyS z hzS hxy hyz hxzS
            ((D.candidate_r₁_new hyQ hzQ).mp hyz₁))

end Data
end PatternLiftingConstruction
end Alexander313.Carlson
