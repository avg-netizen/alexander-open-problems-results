import Alexander313.Carlson.Rules
import Alexander313.Carlson.CoveringEnumeration

/-!
# Cofinal copies supplied by a valid rule

Carlson, *Patterns of resemblance of order 2*, proof of Lemma 10.3,
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
pp. 43–44 of the author's October 16, 2008 manuscript, pure case.

A cofinally valid extension of `P` at `a` supplies cofinally many copies of
its new block below the image of `a`, fixing the images of old points below
`a`. This module expresses those copies using the indexed finite relations
in `CofinalCopies`, so that the cofinal-copy clause of `R2` can transfer them
to a larger endpoint.
-/

noncomputable section

namespace Alexander313.Carlson.Str

variable {α : Type*} [LinearOrder α]

/-- The finite block of a cofinally valid extension occurs cofinally below
the image of its extension point, with the old lower block fixed. This is
the first cofinal-copy assertion in the proof of Carlson's Lemma 10.3. -/
theorem CofinallyValid.cofinalCopies_at {P Q : Str α} {a : α}
    (hcv : CofinallyValid P Q) (hext : ExtensionAt P Q a)
    {h : α → Ordinal.{0}} (hh : CoveringR P h) :
    CofinalCopies R1 R2 ((P.U.filter (· < a)).image h)
      (Q.restrict ((P.U.filter (· < a)) ∪ (Q.U \ P.U))).indexedFirst
      (Q.restrict ((P.U.filter (· < a)) ∪ (Q.U \ P.U))).indexedSecond (h a) := by
  classical
  intro ξ hξ
  let L : Finset α := P.U.filter (· < a)
  let M : Finset α := Q.U \ P.U
  let cut : α → Ordinal.{0} := fun x => if x = a then ξ else 0
  have hcut : ∀ x ∈ P.U, 0 < h x → cut x < h x := by
    intro x _ hx0
    by_cases hxa : x = a
    · subst x
      simpa only [cut, if_pos rfl] using hξ
    · simpa only [cut, if_neg hxa] using hx0
  obtain ⟨h', hcov, hfix, habove⟩ := hcv.2 h hh cut hcut
  refine ⟨M.image h', ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxQ, hxP⟩ := Finset.mem_sdiff.mp hx
    have hxa : JustBelow P.U a x := hext.2.2.2 x hxQ hxP
    have hξx : ξ < h' x := by
      have hbound := habove a x hxQ hxa
      simpa only [cut, if_pos rfl] using hbound
    have hxa' : h' x < h' a := hcov.1 x hxQ a (hext.1.1 hext.2.1) hxa.2.1
    rw [hfix a hext.2.1] at hxa'
    exact ⟨hξx, hxa'⟩
  · have hLQ : L ∪ M ⊆ Q.U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hext.1.1 (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_sdiff.mp hx).1
    have hL : L.image h' = L.image h := Finset.image_congr fun x hx =>
      hfix x (Finset.mem_filter.mp hx).1
    have hc := (hcov.mono (Q.restrict_isSub hLQ)).coversStructure_image
    change CoversStructure R1 R2 ((L ∪ M).image h')
      (Q.restrict (L ∪ M)).indexedFirst (Q.restrict (L ∪ M)).indexedSecond at hc
    rw [Finset.image_union, hL] at hc
    exact hc

end Alexander313.Carlson.Str
