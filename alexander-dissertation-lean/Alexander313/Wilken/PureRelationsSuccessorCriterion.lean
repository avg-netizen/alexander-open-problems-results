import Alexander313.Wilken.PureRelationsSuccessorCriterionSupport
import Mathlib.Data.Finset.Max
import Alexander313.Wilken.PureRelationsNegativeBounds
import Alexander313.Wilken.PureRelationsReflectionConverse

/-!
# Full actual successor criterion in source Lemma 3.2(2)

One cutoff lies above every finite original lower point and every negative
first/second bound. If the finite set has positive second predecessors, its
ordinary largest such predecessor supplies a real second successor above
that cutoff; actual connectedness and transitivity preserve every other
positive second fact. First facts use genuine interval closure. If there is
no second predecessor, a proper-limit point above the cut suffices. This
constructs the complete finite pattern, hence actual R1 at alpha+1. The final
criterion has precisely the printed proper-limit and supremum premises.
No relation, reflection, endpoint-copy or negative-bound oracle is supplied.
This module has compiled. `CompileOrdinalRoom.lean` audits the final criterion;
it does not assert a computable presentation of the pure relations.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SuccessorCriterion

/-- The printed supremum condition constructs ONE lower endpoint with
all original positive AND negative first/second facts on the whole finite
set, even when the set has no positive second predecessor. -/
theorem finite_endpoint_matches (α : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    (suprema : ∀ δ : Ordinal.{0}, δ < α → R2 δ α →
      IsLUB (SecondSuccessorsBelow α δ) α)
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < α) :
    ∃ y : Ordinal.{0}, y < α ∧ (∀ x ∈ X, x < y) ∧
      (∀ x ∈ X, R1 x y ↔ R1 x α) ∧ (∀ x ∈ X, R2 x y ↔ R2 x α) := by
  classical
  obtain ⟨c, hc, below, negative⟩ := finite_negative_bounds α hα X hX
  let P := X.filter (fun x => R2 x α)
  have choice : ∃ y : Ordinal.{0}, c < y ∧ y < α ∧
      ∀ x ∈ X, R2 x α → R2 x y := by
    by_cases hn : P.Nonempty
    · obtain ⟨δ, hδP, largest⟩ := Finset.exists_max_image P id hn
      have hδX : δ ∈ X := (Finset.mem_filter.mp hδP).1
      have hδR : R2 δ α := (Finset.mem_filter.mp hδP).2
      obtain ⟨y, hcy, hy, hδy⟩ := secondSuccessors_above_cut α δ c
        (suprema δ (hX δ hδX) hδR) hc
      refine ⟨y, hcy, hy, ?_⟩
      intro x hx hR
      have hxP : x ∈ P := Finset.mem_filter.mpr ⟨hx, hR⟩
      have hxδ : x ≤ δ := largest x hxP
      exact R2_trans (R2_connected hR (R2_R1 hδR) hxδ) hδy
    · refine ⟨c + 1, lt_add_one c, hα.add_one_lt hc, ?_⟩
      intro x hx hR
      exact False.elim (hn ⟨x, Finset.mem_filter.mpr ⟨hx, hR⟩⟩)
  obtain ⟨y, hcy, hy, positive⟩ := choice
  refine ⟨y, hy, fun x hx => (below x hx).trans hcy, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxy
      by_contra hn
      exact (negative x hx y hcy.le hy).1 hn hxy
    · intro hxα
      exact R1_between hxα ((below x hx).trans hcy).le hy.le
  · intro x hx
    constructor
    · intro hxy
      by_contra hn
      exact (negative x hx y hcy.le hy).2 hn hxy
    · exact positive x hx

/-- Every original finite expanded pattern below alpha+1 has a genuine
lower copy fixing all its original lower labels. The possible point alpha
is replaced by the single endpoint constructed with ALL its facts. -/
theorem successor_finiteReflection (α : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    (suprema : ∀ δ : Ordinal.{0}, δ < α → R2 δ α →
      IsLUB (SecondSuccessorsBelow α δ) α) : FiniteReflection α (α + 1) := by
  classical
  intro F hF
  let X := F.erase α
  have hX : ∀ x ∈ X, x < α := by
    intro x hx
    have hm := Finset.mem_erase.mp hx
    exact lt_of_le_of_ne (Order.lt_add_one_iff.mp (hF x hm.2)) hm.1
  obtain ⟨y, hy, above, first, second⟩ := finite_endpoint_matches α hα suprema X hX
  obtain ⟨f, lower, fixed, pattern⟩ := endpoint_replacement α y X hX hy above first second
  have subset : ∀ x ∈ F, x ∈ X ∪ {α} := by
    intro x hx
    by_cases he : x = α
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr he))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨he, hx⟩))
  refine ⟨f, fun x hx => lower x (subset x hx), ?_, ?_⟩
  · intro x hx hxα
    exact fixed x (Finset.mem_erase.mpr ⟨ne_of_lt hxα, hx⟩)
  · exact ⟨fun x hx z hz => pattern.1 x (subset x hx) z (subset z hz),
      fun x hx z hz => pattern.2.1 x (subset x hx) z (subset z hz),
      fun x hx z hz => pattern.2.2.1 x (subset x hx) z (subset z hz),
      fun x hx z hz => pattern.2.2.2 x (subset x hx) z (subset z hz)⟩

/-- The genuine converse in the original expanded R2 language: the
printed proper-limit and second-successor suprema yield actual R1. -/
theorem R1_successor_of_limit_suprema (α : Ordinal.{0}) (hα : Order.IsSuccLimit α)
    (suprema : ∀ δ : Ordinal.{0}, δ < α → R2 δ α →
      IsLUB (SecondSuccessorsBelow α δ) α) : R1 α (α + 1) :=
  R1_of_finiteReflection α (α + 1) (lt_add_one α).le
    (successor_finiteReflection α hα suprema)

/-- Full source Lemma 3.2(2) for the ACTUAL recursively constructed pure
relations, with no assumed finite reflection or endpoint agreement. -/
theorem R1_successor_iff_limit_suprema (α : Ordinal.{0}) :
    R1 α (α + 1) ↔ Order.IsSuccLimit α ∧
      ∀ δ : Ordinal.{0}, δ < α → R2 δ α →
        IsLUB (SecondSuccessorsBelow α δ) α :=
  ⟨source_lemma_3_2_forward α,
    fun h => R1_successor_of_limit_suprema α h.1 h.2⟩

end Alexander313.Wilken.PureRelations.SuccessorCriterion
