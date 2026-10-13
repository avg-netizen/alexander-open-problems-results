import Alexander313.Carlson.Rules

/-!
# Images of patterns and transport of continuity

Finite increasing isomorphisms transport the eight pattern axioms and
continuous extensions. This supplies the change of labels used at the start
of Carlson's Lemma 12.6: identify the source and its extension with their
images under the arithmetic lifting map.

The image relations are defined by finite preimages, so no inverse map or
inhabited ambient type is required. All assertions concern only the finite
carriers.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
variable {P Pplus : Str α} {Q Qplus : Str β} {h f : α → β}

theorem IsIso.mem (e : IsIso P Q f) {x : α} (hx : x ∈ P.U) : f x ∈ Q.U := by
  rw [← e.1]
  exact Finset.mem_image_of_mem f hx

theorem IsIso.preimage (e : IsIso P Q f) {y : β} (hy : y ∈ Q.U) :
    ∃ x ∈ P.U, f x = y := by
  rw [← e.1] at hy
  exact Finset.mem_image.mp hy

theorem IsIso.le_iff (e : IsIso P Q f) {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U) :
    f x ≤ f y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra hnot
    exact absurd (e.2.1 y hy x hx (not_le.mp hnot)) (not_lt.mpr hxy)
  · intro hxy
    rcases hxy.lt_or_eq with hlt | rfl
    · exact (e.2.1 x hx y hy hlt).le
    · exact le_rfl

theorem IsIso.lt_iff (e : IsIso P Q f) {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U) :
    f x < f y ↔ x < y := by
  constructor
  · intro hxy
    by_contra hnot
    exact absurd hxy (not_lt.mpr ((e.le_iff hy hx).mpr (not_lt.mp hnot)))
  · exact e.2.1 x hx y hy

theorem IsIso.rel_iff (e : IsIso P Q f) {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U)
    (k : Lvl) : P.rel k x y ↔ Q.rel k (f x) (f y) := by
  cases k
  · exact (e.2.2 x hx y hy).1
  · exact (e.2.2 x hx y hy).2

/-- Increasing finite isomorphisms preserve the pattern axioms. -/
theorem IsIso.isPattern (e : IsIso P Q f) (hP : P.IsPattern) : Q.IsPattern := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv hr
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    exact (e.le_iff hx hy).mpr (hP.le₁ x hx y hy ((e.2.2 x hx y hy).1.mpr hr))
  · intro u hu v hv hr
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    exact (e.2.2 x hx y hy).1.mp (hP.sub₂ x hx y hy ((e.2.2 x hx y hy).2.mpr hr))
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    exact (e.2.2 x hx x hx).1.mp (hP.refl₁ x hx)
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    exact (e.2.2 x hx x hx).2.mp (hP.refl₂ x hx)
  · intro u hu v hv w hw huv hvw
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    obtain ⟨z, hz, rfl⟩ := e.preimage hw
    exact (e.2.2 x hx z hz).1.mp (hP.trans₁ x hx y hy z hz
      ((e.2.2 x hx y hy).1.mpr huv) ((e.2.2 y hy z hz).1.mpr hvw))
  · intro u hu v hv w hw huv hvw
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    obtain ⟨z, hz, rfl⟩ := e.preimage hw
    exact (e.2.2 x hx z hz).2.mp (hP.trans₂ x hx y hy z hz
      ((e.2.2 x hx y hy).2.mpr huv) ((e.2.2 y hy z hz).2.mpr hvw))
  · intro u hu v hv w hw huv hvw huw
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    obtain ⟨z, hz, rfl⟩ := e.preimage hw
    exact (e.2.2 x hx y hy).1.mp (hP.convex₁ x hx y hy z hz
      ((e.le_iff hx hy).mp huv) ((e.le_iff hy hz).mp hvw)
      ((e.2.2 x hx z hz).1.mpr huw))
  · intro u hu v hv w hw huv hvw huw hvw'
    obtain ⟨x, hx, rfl⟩ := e.preimage hu
    obtain ⟨y, hy, rfl⟩ := e.preimage hv
    obtain ⟨z, hz, rfl⟩ := e.preimage hw
    exact (e.2.2 x hx y hy).2.mp (hP.respect₂ x hx y hy z hz
      ((e.le_iff hx hy).mp huv) ((e.le_iff hy hz).mp hvw)
      ((e.2.2 x hx z hz).2.mpr huw) ((e.2.2 y hy z hz).1.mpr hvw'))

/-- The finite image structure under a map. Relations outside the image
carrier are irrelevant to the structure. -/
def map (P : Str α) (f : α → β) : Str β :=
  { U := P.U.image f
    r₁ := fun u v => ∃ x ∈ P.U, ∃ y ∈ P.U, f x = u ∧ f y = v ∧ P.r₁ x y
    r₂ := fun u v => ∃ x ∈ P.U, ∃ y ∈ P.U, f x = u ∧ f y = v ∧ P.r₂ x y }

/-- A strictly increasing map identifies a finite structure with its image. -/
theorem map_isIso (P : Str α) (f : α → β)
    (hmono : ∀ x ∈ P.U, ∀ y ∈ P.U, x < y → f x < f y) : IsIso P (P.map f) f := by
  have hinj : ∀ x ∈ P.U, ∀ y ∈ P.U, f x = f y → x = y := by
    intro x hx y hy heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd (hmono x hx y hy hlt) (by rw [heq]; exact lt_irrefl _)
    · exact absurd (hmono y hy x hx hlt) (by rw [heq]; exact lt_irrefl _)
  refine ⟨rfl, hmono, ?_⟩
  intro x hx y hy
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hr
    exact ⟨x, hx, y, hy, rfl, rfl, hr⟩
  · rintro ⟨u, hu, v, hv, hux, hvy, hr⟩
    simpa only [hinj u hu x hx hux, hinj v hv y hy hvy] using hr
  · intro hr
    exact ⟨x, hx, y, hy, rfl, rfl, hr⟩
  · rintro ⟨u, hu, v, hv, hux, hvy, hr⟩
    simpa only [hinj u hu x hx hux, hinj v hv y hy hvy] using hr

/-- Continuity is invariant under compatible changes of labels of the base
and its extension. -/
theorem Continuous.of_isIso (hc : Continuous P Pplus)
    (e : IsIso P Q h) (eplus : IsIso Pplus Qplus f)
    (hfix : ∀ x ∈ P.U, f x = h x) : Continuous Q Qplus := by
  have liftLeast {x p : α} (hx : x ∈ Pplus.U) (hp : LeastGE P.U x p) :
      LeastGE Q.U (f x) (h p) := by
    refine ⟨e.mem hp.1, ?_, ?_⟩
    · have hle := (eplus.le_iff hx (hc.1.1 hp.1)).mpr hp.2.1
      simpa only [hfix p hp.1] using hle
    · intro q hq hxq
      obtain ⟨a, ha, rfl⟩ := e.preimage hq
      have hxa : x ≤ a := (eplus.le_iff hx (hc.1.1 ha)).mp
        (by simpa only [hfix a ha] using hxq)
      exact (e.le_iff hp.1 ha).mpr (hp.2.2 a ha hxa)
  have pullLeast {x p : α} (hx : x ∈ Pplus.U) (hp : p ∈ P.U)
      (hL : LeastGE Q.U (f x) (h p)) : LeastGE P.U x p := by
    refine ⟨hp, ?_, ?_⟩
    · exact (eplus.le_iff hx (hc.1.1 hp)).mp (by simpa only [hfix p hp] using hL.2.1)
    · intro a ha hxa
      have hfxa := (eplus.le_iff hx (hc.1.1 ha)).mpr hxa
      have hxa' : f x ≤ h a := by simpa only [hfix a ha] using hfxa
      exact (e.le_iff hp ha).mp (hL.2.2 (h a) (e.mem ha) hxa')
  have hsub : IsSub Q Qplus := by
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨x, hx, rfl⟩ := e.preimage hu
      rw [← hfix x hx]
      exact eplus.mem (hc.1.1 hx)
    · intro u hu v hv
      obtain ⟨x, hx, rfl⟩ := e.preimage hu
      obtain ⟨y, hy, rfl⟩ := e.preimage hv
      have hs := hc.1.2 x hx y hy
      have he := e.2.2 x hx y hy
      have heplus := eplus.2.2 x (hc.1.1 hx) y (hc.1.1 hy)
      rw [hfix x hx, hfix y hy] at heplus
      exact ⟨he.1.symm.trans (hs.1.trans heplus.1), he.2.symm.trans (hs.2.trans heplus.2)⟩
  have hbounded : ∀ u ∈ Qplus.U, ∃ q ∈ Q.U, u ≤ q := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := eplus.preimage hu
    obtain ⟨p, hp, hxp⟩ := hc.2.1 x hx
    refine ⟨h p, e.mem hp, ?_⟩
    have hle := (eplus.le_iff hx (hc.1.1 hp)).mpr hxp
    simpa only [hfix p hp] using hle
  have hcorrect (k : Lvl) : KCorrect Q Qplus k := by
    intro p u v hu hv hL hpv hrel
    obtain ⟨x, hx, rfl⟩ := eplus.preimage hu
    obtain ⟨y, hy, rfl⟩ := eplus.preimage hv
    obtain ⟨a, ha, rfl⟩ := e.preimage hL.1
    have hLa := pullLeast hx ha hL
    have hay : a < y := (eplus.lt_iff (hc.1.1 ha) hy).mp
      (by simpa only [hfix a ha] using hpv)
    have hcK : KCorrect P Pplus k := by
      cases k
      · exact hc.2.2.1
      · exact hc.2.2.2
    obtain ⟨b, hb, hab⟩ := hcK a x y hx hy hLa hay ((eplus.rel_iff hx hy k).mpr hrel)
    exact ⟨h b, liftLeast hy hb, (e.rel_iff ha hb.1 k).mp hab⟩
  exact ⟨hsub, hbounded, hcorrect .one, hcorrect .two⟩

/-- Definition 7.4, pure case: a continuous embedding is an exact embedding
whose image is a continuous subpattern of the target. -/
def ContinuousEmbedding (P : Str α) (Q : Str β) (h : α → β) : Prop :=
  IsIso P (Q.restrict (P.U.image h)) h ∧ Continuous (Q.restrict (P.U.image h)) Q

end Str

end Alexander313.Carlson
