import Alexander313.Carlson.AmalgamationExistence
import Alexander313.Carlson.LeastCopyCompletenessExamples

/-! Empty-family, overlapping-image, and exactness controls for amalgamations. -/

noncomputable section

namespace Alexander313.Carlson

/-- A family of length zero has the empty ordinal amalgamation. -/
theorem empty_family_amalgamation (P : Fin 0 → Str ℚ) :
    ∃ f : Fin 0 → ℚ → Ordinal.{0}, Str.Amalgamation P (Str.ofOrdinals ∅) f := by
  obtain ⟨U, f, A, _, _⟩ := exists_ordinal_amalgamation P (fun i => Fin.elim0 i)
  have hU : U = ∅ := by simpa [Str.ofOrdinals] using A.union
  exact ⟨f, hU ▸ A⟩

/-- The two distinct rational singleton carriers have one common least
ordinal image. Amalgamation permits this overlap; it is not a disjoint union. -/
theorem distinct_singletons_amalgamate_to_zero :
    ∃ f : Fin 2 → ℚ → Ordinal.{0},
      Str.Amalgamation
        (fun i : Fin 2 => (rationalFullChain 2).restrict {(i.val : ℚ)})
        (Str.ofOrdinals {0}) f ∧ ∀ i, f i (i.val : ℚ) = 0 := by
  let P (i : Fin 2) := (rationalFullChain 2).restrict {(i.val : ℚ)}
  have hP (i : Fin 2) : (P i).IsPattern :=
    (rationalFullChain_isPattern 2).restrict
      (Finset.singleton_subset_iff.mpr (rationalFullChain_mem i.isLt))
  obtain ⟨U, f, A, hm, _⟩ := exists_ordinal_amalgamation P hP
  have hf (i : Fin 2) : f i (i.val : ℚ) = 0 := by
    apply (singleton_isominimal_iff_zero _).mp
    simpa only [P, Str.restrict, Finset.image_singleton] using hm i
  have hU : U = {0} := by
    change (Str.ofOrdinals U).U = {0}
    rw [A.union]
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, P, Str.restrict,
      Finset.image_singleton, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi⟩
      exact hi.trans (hf i)
    · intro hz
      exact ⟨0, hz.trans (hf 0).symm⟩
  exact ⟨f, hU ▸ A, hf⟩

/-- An ordinary bounded union need not be exact at a nonleast singleton. -/
theorem positive_singleton_not_exact_in_union (a : Ordinal.{0}) (ha : 0 < a) :
    ¬Str.Exact (Str.ofOrdinals {a}) (Str.ofOrdinals {0, a}) := by
  intro h
  obtain ⟨hb, hnot⟩ := positive_singleton_bounded_extension_rejected a ha
  have hs := Str.initialSpan_eq_of_bounded (P := Str.ofOrdinals {a})
    (Q := Str.ofOrdinals {0, a}) hb
  exact hnot (hs ▸ h.generates)

/-- Merely taking the union of two covered input structures does not meet
Definition 15.8: its positive singleton input is not exact. -/
theorem ordinary_singleton_union_not_amalgamation :
    ¬Str.Amalgamation (fun i : Fin 2 => Str.ofOrdinals {(i.val : Ordinal.{0})})
      (Str.ofOrdinals {0, 1}) (fun _ => id) := by
  intro A
  have h := A.exact 1
  have h' : Str.Exact (Str.ofOrdinals {1}) (Str.ofOrdinals {0, 1}) := by
    simpa only [Finset.image_id, Str.ofOrdinals, Str.restrict, Fin.val_one, Nat.cast_one] using h
  exact positive_singleton_not_exact_in_union 1 zero_lt_one h'

/-- Least-copy agreement is exercised on a genuine downward reflection
adding a third point, rather than an identity or arithmetic rule. -/
theorem downward_extension_least_copy_agrees :
    ∃ Q : Str ℚ, Str.GeneratingRule (rationalFullChain 2) Q ∧ Q.U.card = 3 ∧
      ∀ (A : PatternRealization (rationalFullChain 2)) (B : PatternRealization Q),
        ∀ x ∈ (rationalFullChain 2).U, B.label x = A.label x := by
  have hzero : (0 : ℚ) ∈ (rationalFullChain 2).U :=
    rationalFullChain_mem (by omega : 0 < 2)
  have hone : (1 : ℚ) ∈ (rationalFullChain 2).U :=
    rationalFullChain_mem (by omega : 1 < 2)
  obtain ⟨Q, d, _, hcard⟩ := Str.GeneratingRule.exists_downward_rat
    (k := .one) (a := 0) (b := 1) (X := {0})
    (rationalFullChain_isPattern 2) hzero hone (by norm_num)
    (by change (0 : ℚ) ≤ 1; norm_num)
    (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact ⟨hzero, le_rfl, by norm_num⟩)
    (Finset.singleton_nonempty 0)
  have hc : Q.U.card = 3 := by
    norm_num [rationalFullChain, Finset.range_add_one] at hcard
    exact hcard
  exact ⟨Q, d, hc, d.valid.least_copy_agrees⟩

end Alexander313.Carlson
