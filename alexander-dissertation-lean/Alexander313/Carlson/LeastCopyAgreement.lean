import Alexander313.Carlson.LeastCopyCompleteness

/-!
# Least copies agree along valid rules

Carlson, Theorem 14.11, implication (3) => (4c), printed pp. 69--70.
The extension furnished by validity bounds the least target copy above
the least source copy. Restricting the least target covering gives the
opposite inequality. Continuity is not needed for this agreement itself.

For induced ordinal structures, a valid subpattern of an isominimal
target is therefore isominimal. These are agreement and inheritance
results; the converse characterization of generation is not assumed.
-/

noncomputable section

namespace Alexander313.Carlson

/-- Actual least realizations of a valid rational rule use the same
ordinal labels on the old carrier. This applies in particular to every
generated extension, since generation has already been proved valid. -/
theorem Str.Valid.least_copy_agrees {P Q : Str ℚ} (d : Str.Valid P Q)
    (A : PatternRealization P) (B : PatternRealization Q) :
    ∀ x ∈ P.U, B.label x = A.label x := by
  obtain ⟨g, hg, hfix⟩ := d.2 A.label A.seed_covering
  intro x hx
  have hle := B.seed_minimal hg (d.1.1 hx)
  rw [hfix x hx] at hle
  exact hle.antisymm (A.seed_minimal (B.seed_covering.mono d.1) hx)

/-- A valid induced subpattern of an isominimal ordinal target is
isominimal: extend each competing source covering and use target leastness. -/
theorem IsominimalOrdinalSet.of_valid {U V : Finset Ordinal.{0}}
    (hV : IsominimalOrdinalSet V)
    (d : Str.Valid (Str.ofOrdinals U) (Str.ofOrdinals V)) :
    IsominimalOrdinalSet U := by
  apply IsominimalOrdinalSet.iff_le_covering.mpr
  intro g hg z hz
  obtain ⟨f, hf, hfix⟩ := d.2 g hg
  have hle := hV.le_covering hf (d.1.1 hz)
  rw [hfix z hz] at hle
  exact hle

end Alexander313.Carlson
