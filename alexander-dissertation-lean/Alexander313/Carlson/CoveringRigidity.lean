import Alexander313.Carlson.Rules

/-!
# Covering rigidity for valid extensions

Carlson, *Patterns of resemblance of order 2*, Lemma 14.6, pure case.

A covering of a covered pattern into an extension generated from it cannot
move an old point downward. The proof uses only validity of the extension,
so the main theorem is stated for every valid rule.

For a fixed point of a covered pattern, ordinal well-foundedness supplies a
covering minimizing its image at that point. Extend that covering over the
valid rule and compose with a proposed downward-moving covering. The result
would give a strictly smaller image, contradicting minimality.

The minimizing covering is chosen separately for each point. No simultaneous
pointwise-minimal covering, coverage of every pattern, or core-realization
theorem is assumed or asserted here.

Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed p. 60 of the author's October 16, 2008 manuscript.
-/

noncomputable section

namespace Alexander313.Carlson
namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A covering into a finite structure composes with an ordinal covering of
that structure. -/
theorem CoversInto.comp_coveringR {P : Str α} {Q : Str β}
    {f : α → β} {g : β → Ordinal.{0}}
    (hf : CoversInto P Q f) (hg : CoveringR Q g) :
    CoveringR P (g ∘ f) :=
  hf.2.comp
    (fun x hx y hy => hg.1 (f x) (hf.1 x hx) (f y) (hf.1 y hy))
    (fun x hx y hy => hg.2.1 (f x) (hf.1 x hx) (f y) (hf.1 y hy))
    (fun x hx y hy => hg.2.2 (f x) (hf.1 x hx) (f y) (hf.1 y hy))

/-- At any specified point, some ordinal covering attains the least image
among all ordinal coverings of a covered structure. -/
theorem Covered.exists_minimal_at {P : Str α} (hP : Covered P) (x : α) :
    ∃ h : α → Ordinal.{0}, CoveringR P h ∧
      ∀ g : α → Ordinal.{0}, CoveringR P g → h x ≤ g x := by
  obtain ⟨h₀, hh₀⟩ := hP
  let S : Set Ordinal.{0} :=
    {ξ | ∃ h : α → Ordinal.{0}, CoveringR P h ∧ h x = ξ}
  obtain ⟨ξ, ⟨h, hh, hξ⟩, hmin⟩ :=
    Ordinal.lt_wf.has_min S ⟨h₀ x, h₀, hh₀, rfl⟩
  refine ⟨h, hh, fun g hg => ?_⟩
  rw [hξ]
  exact not_lt.mp (hmin (g x) ⟨g, hg, rfl⟩)

/-- Lemma 14.6 in its stronger validity form: every covering of a covered
structure into a valid extension is pointwise inflationary on the base. -/
theorem Valid.le_of_coversInto {P Q : Str α} (hv : Valid P Q)
    (hP : Covered P) {f : α → α} (hf : CoversInto P Q f)
    {x : α} (hx : x ∈ P.U) : x ≤ f x := by
  by_contra hnot
  have hfx : f x < x := not_le.mp hnot
  obtain ⟨h, hh, hmin⟩ := hP.exists_minimal_at x
  obtain ⟨g, hg, hext⟩ := hv.2 h hh
  have hlt : (g ∘ f) x < h x := by
    change g (f x) < h x
    rw [← hext x hx]
    exact hg.1 (f x) (hf.1 x hx) x (hv.1.1 hx) hfx
  exact (not_lt.mpr (hmin (g ∘ f) (hf.comp_coveringR hg))) hlt

/-- The no-downward-movement conclusion for cofinally valid rules. -/
theorem CofinallyValid.le_of_coversInto {P Q : Str α}
    (hv : CofinallyValid P Q) (hP : Covered P)
    {f : α → α} (hf : CoversInto P Q f) {x : α} (hx : x ∈ P.U) :
    x ≤ f x :=
  hv.valid.le_of_coversInto hP hf hx

/-- A downward-moving covering is an obstruction to validity whenever the
source has an ordinal covering. -/
theorem not_valid_of_coversInto_lt {P Q : Str α} (hP : Covered P)
    {f : α → α} (hf : CoversInto P Q f) {x : α}
    (hx : x ∈ P.U) (hfx : f x < x) : ¬ Valid P Q :=
  fun hv => (not_lt.mpr (hv.le_of_coversInto hP hf hx)) hfx

end Str
end Alexander313.Carlson
