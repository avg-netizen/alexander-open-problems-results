import Alexander313.Carlson.Patterns

/-!
# Pullbacks and intersections of finite patterns

The eight pure pattern axioms are preserved by pullback along an increasing
map and by intersection of relations on a shared finite carrier. These
operations let a candidate lifting retain exactly the relations supported
both by a given pattern and by an ordinal realization.

No conditions are imposed on maps or relations outside the finite carriers.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Pull back both relations of `T` to the finite carrier `S` along `f`. -/
def pullback (T : Str β) (S : Finset α) (f : α → β) : Str α :=
  { U := S
    r₁ := fun x y => T.r₁ (f x) (f y)
    r₂ := fun x y => T.r₂ (f x) (f y) }

/-- An increasing map into a pattern induces a pattern on its source carrier. -/
theorem IsPattern.pullback {T : Str β} {S : Finset α} {f : α → β}
    (hT : T.IsPattern) (hmem : ∀ x ∈ S, f x ∈ T.U)
    (hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y) :
    (T.pullback S f).IsPattern := by
  have hle {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≤ y) : f x ≤ f y := by
    rcases hxy.lt_or_eq with hxy | rfl
    · exact (hmono x hx y hy hxy).le
    · exact le_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hr
    have hxy := hT.le₁ (f x) (hmem x hx) (f y) (hmem y hy) hr
    by_contra hnot
    exact absurd hxy (not_le.mpr (hmono y hy x hx (not_le.mp hnot)))
  · intro x hx y hy hr
    exact hT.sub₂ (f x) (hmem x hx) (f y) (hmem y hy) hr
  · intro x hx
    exact hT.refl₁ (f x) (hmem x hx)
  · intro x hx
    exact hT.refl₂ (f x) (hmem x hx)
  · intro x hx y hy z hz hxy hyz
    exact hT.trans₁ (f x) (hmem x hx) (f y) (hmem y hy) (f z) (hmem z hz) hxy hyz
  · intro x hx y hy z hz hxy hyz
    exact hT.trans₂ (f x) (hmem x hx) (f y) (hmem y hy) (f z) (hmem z hz) hxy hyz
  · intro x hx y hy z hz hxy hyz hxz
    exact hT.convex₁ (f x) (hmem x hx) (f y) (hmem y hy) (f z) (hmem z hz)
      (hle hx hy hxy) (hle hy hz hyz) hxz
  · intro x hx y hy z hz hxy hyz hxz hyz'
    exact hT.respect₂ (f x) (hmem x hx) (f y) (hmem y hy) (f z) (hmem z hz)
      (hle hx hy hxy) (hle hy hz hyz) hxz hyz'

/-- Intersect the two relations, retaining the carrier of the left structure. -/
def inter (P Q : Str α) : Str α :=
  { U := P.U
    r₁ := fun x y => P.r₁ x y ∧ Q.r₁ x y
    r₂ := fun x y => P.r₂ x y ∧ Q.r₂ x y }

/-- Intersecting the relations of two patterns on the same carrier yields a pattern. -/
theorem IsPattern.inter {P Q : Str α} (hP : P.IsPattern) (hQ : Q.IsPattern)
    (hU : Q.U = P.U) : (P.inter Q).IsPattern := by
  have memQ {x : α} (hx : x ∈ P.U) : x ∈ Q.U := hU.symm ▸ hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hr
    exact hP.le₁ x hx y hy hr.1
  · intro x hx y hy hr
    exact ⟨hP.sub₂ x hx y hy hr.1, hQ.sub₂ x (memQ hx) y (memQ hy) hr.2⟩
  · intro x hx
    exact ⟨hP.refl₁ x hx, hQ.refl₁ x (memQ hx)⟩
  · intro x hx
    exact ⟨hP.refl₂ x hx, hQ.refl₂ x (memQ hx)⟩
  · intro x hx y hy z hz hxy hyz
    exact ⟨hP.trans₁ x hx y hy z hz hxy.1 hyz.1,
      hQ.trans₁ x (memQ hx) y (memQ hy) z (memQ hz) hxy.2 hyz.2⟩
  · intro x hx y hy z hz hxy hyz
    exact ⟨hP.trans₂ x hx y hy z hz hxy.1 hyz.1,
      hQ.trans₂ x (memQ hx) y (memQ hy) z (memQ hz) hxy.2 hyz.2⟩
  · intro x hx y hy z hz hxy hyz hxz
    exact ⟨hP.convex₁ x hx y hy z hz hxy hyz hxz.1,
      hQ.convex₁ x (memQ hx) y (memQ hy) z (memQ hz) hxy hyz hxz.2⟩
  · intro x hx y hy z hz hxy hyz hxz hyz'
    exact ⟨hP.respect₂ x hx y hy z hz hxy hyz hxz.1 hyz'.1,
      hQ.respect₂ x (memQ hx) y (memQ hy) z (memQ hz) hxy hyz hxz.2 hyz'.2⟩

/-- Retain the relations of `Q` that also hold in its ordinal realization. -/
def interPullback (Q : Str α) (t : α → Ordinal.{0}) : Str α :=
  { U := Q.U
    r₁ := fun x y => Q.r₁ x y ∧ R1 (t x) (t y)
    r₂ := fun x y => Q.r₂ x y ∧ R2 (t x) (t y) }

/-- Intersecting with the pullback of the ordinal relations preserves patterns. -/
theorem interPullback_isPattern {Q : Str α} (hQ : Q.IsPattern) {t : α → Ordinal.{0}}
    (ht : ∀ x ∈ Q.U, ∀ y ∈ Q.U, x < y → t x < t y) :
    (Q.interPullback t).IsPattern := by
  have hT : ((ofOrdinals (Q.U.image t)).pullback Q.U t).IsPattern :=
    (ofOrdinals_isPattern (Q.U.image t)).pullback
      (fun x hx => Finset.mem_image_of_mem t hx) ht
  exact hQ.inter hT rfl

end Str

end Alexander313.Carlson
