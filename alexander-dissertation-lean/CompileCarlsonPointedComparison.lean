import Alexander313.Carlson.PointedPatternComparisonExamples
import Alexander313.Carlson.RationalAmalgamationExamples

open Alexander313.Carlson

-- Existence expands the original Definition 15.8 requirements and produces
-- a target in the existing finite-edge presentation format.
example {n : ℕ} (P : Fin n → Str ℚ) (hP : ∀ i, (P i).IsPattern) :
    ∃ (Q : Finite.RationalPresentation) (f : Fin n → ℚ → ℚ),
      Q.toStr.IsPattern ∧
      (∀ i, Str.IsIso (P i) (Q.toStr.restrict ((P i).U.image (f i))) (f i)) ∧
      Q.toStr.U = Finset.univ.biUnion (fun i => (P i).U.image (f i)) ∧
      (∀ i, Str.Exact (Q.toStr.restrict ((P i).U.image (f i))) Q.toStr) := by
  obtain ⟨Q, f, d⟩ := exists_presented_amalgamation P hP
  exact ⟨Q, f, d.pattern, d.embeddings, d.union, d.exact⟩

-- The isomorphism is compatible with every supplied input map, including
-- overlapping carriers and the empty family.
example {n : ℕ} {P : Fin n → Str ℚ} {Q Q' : Str ℚ}
    {f f' : Fin n → ℚ → ℚ} (hP : ∀ i, (P i).IsPattern)
    (d : Str.Amalgamation P Q f) (d' : Str.Amalgamation P Q' f') :
    ∃ g : ℚ → ℚ, Str.IsIso Q Q' g ∧
      ∀ i, ∀ x ∈ (P i).U, g (f i x) = f' i x :=
  d.exists_compatible_iso d' hP

-- The domain presents the existing whole core, with its actual ordinal labels.
example (a : Ordinal.{0}) :
    CorePoint a ↔ ∃ p : PointedPattern, (coreRealization p.seed).label p.point = a :=
  corePoint_iff_pointed a

example {n : ℕ} {p : Fin n → PointedPattern} {Q : Str ℚ} {f : Fin n → ℚ → ℚ}
    (d : Str.Amalgamation (fun i => (p i).seed.val.toStr) Q f) (i j : Fin n) :
    ((coreRealization (p i).seed).label (p i).point =
      (coreRealization (p j).seed).label (p j).point ↔
        f i (p i).point = f j (p j).point) ∧
    (R1 ((coreRealization (p i).seed).label (p i).point)
      ((coreRealization (p j).seed).label (p j).point) ↔
        Q.r₁ (f i (p i).point) (f j (p j).point)) ∧
    (R2 ((coreRealization (p i).seed).label (p i).point)
      ((coreRealization (p j).seed).label (p j).point) ↔
        Q.r₂ (f i (p i).point) (f j (p j).point)) :=
  ⟨d.pointed_eq_iff i j, d.pointed_one_iff i j, d.pointed_two_iff i j⟩

#print axioms Alexander313.Carlson.Str.IsIso.injOn
#print axioms Alexander313.Carlson.Str.IsIso.comp
#print axioms Alexander313.Carlson.Str.IsIso.orderIso
#print axioms Alexander313.Carlson.Str.IsIso.eqOn
#print axioms Alexander313.Carlson.Str.IsIso.between_copies
#print axioms Alexander313.Carlson.Str.Amalgamation.mem
#print axioms Alexander313.Carlson.Str.Amalgamation.least_image
#print axioms Alexander313.Carlson.Str.Amalgamation.exists_compatible_iso
#print axioms Alexander313.Carlson.PointedPattern
#print axioms Alexander313.Carlson.PointedPattern.iota
#print axioms Alexander313.Carlson.PointedPattern.corePoint
#print axioms Alexander313.Carlson.PointedPattern.lt_coreBound
#print axioms Alexander313.Carlson.corePoint_iff_pointed
#print axioms Alexander313.Carlson.Str.Amalgamation.pointed_eq_iff
#print axioms Alexander313.Carlson.Str.Amalgamation.pointed_le_iff
#print axioms Alexander313.Carlson.Str.Amalgamation.pointed_lt_iff
#print axioms Alexander313.Carlson.Str.Amalgamation.pointed_one_iff
#print axioms Alexander313.Carlson.Str.Amalgamation.pointed_two_iff
#print axioms Alexander313.Carlson.Str.Amalgamation.of_rational_iso
#print axioms Alexander313.Carlson.exists_rational_amalgamation
#print axioms Alexander313.Carlson.exists_presented_amalgamation
#print axioms Alexander313.Carlson.distinct_singleton_pointed_labels_agree
#print axioms Alexander313.Carlson.displaced_singleton_amalgamations_compatible
#print axioms Alexander313.Carlson.isomorphisms_can_differ_off_carrier
#print axioms Alexander313.Carlson.empty_rational_amalgamations_compatible
#print axioms Alexander313.Carlson.strict_chain_pointed_comparisons
#print axioms Alexander313.Carlson.singleton_before_strict_chain_first
#print axioms Alexander313.Carlson.singleton_chain_presented_amalgamation
