import Alexander313.Alexander.HilbertDeduction
import Mathlib.Order.Zorn

/-!
# Actual maximal syntactically consistent sentence extensions

Finite native Hilbert proofs are supported by finite sentence theories, and
every proof over a nonempty directed union occurs at one stage. This proves
the chain-union consistency condition for Zorn rather than assuming it.
The resulting maximal theory decides every sentence and has the classical
membership laws. No structure or Henkin witness property is assumed or
claimed for this extension.
-/

namespace Alexander313.FirstOrderCalculus

universe u v w

variable {L : FirstOrder.Language.{u, v}}

namespace Derivation

variable {T : L.Theory} {φ : L.Formula Nat}

theorem finiteSupport (h : Derivation T φ) :
    ∃ F : Finset L.Sentence, (↑F : L.Theory) ⊆ T ∧ Derivation (↑F : L.Theory) φ := by
  classical
  induction h with
  | logical h => exact ⟨∅, by simp, .logical h⟩
  | theory σ hσ =>
    refine ⟨{σ}, ?_, .theory σ (by simp)⟩
    intro τ hτ
    rcases Finset.mem_singleton.mp hτ with rfl
    exact hσ
  | mp hp hq ihp ihq =>
    obtain ⟨F, hFT, hF⟩ := ihp
    obtain ⟨G, hGT, hG⟩ := ihq
    refine ⟨F ∪ G, ?_, .mp (hF.mono ?_) (hG.mono ?_)⟩
    · intro σ hσ
      exact (Finset.mem_union.mp hσ).elim (fun h => hFT h) (fun h => hGT h)
    · intro σ hσ
      exact Finset.mem_union_left _ hσ
    · intro σ hσ
      exact Finset.mem_union_right _ hσ
  | generalize x h ih =>
    obtain ⟨F, hFT, hF⟩ := ih
    exact ⟨F, hFT, .generalize x hF⟩

theorem directedUnion {C : Set L.Theory} (hne : C.Nonempty)
    (directed : DirectedOn (· ⊆ ·) C) (h : Derivation (⋃₀ C) φ) :
    ∃ T ∈ C, Derivation T φ := by
  induction h with
  | logical h =>
    obtain ⟨T, hT⟩ := hne
    exact ⟨T, hT, .logical h⟩
  | theory σ hσ =>
    obtain ⟨T, hT, hσT⟩ := Set.mem_sUnion.mp hσ
    exact ⟨T, hT, .theory σ hσT⟩
  | mp hp hq ihp ihq =>
    obtain ⟨T, hT, hpT⟩ := ihp
    obtain ⟨U, hU, hqU⟩ := ihq
    obtain ⟨V, hV, hTV, hUV⟩ := directed T hT U hU
    exact ⟨V, hV, .mp (hpT.mono hTV) (hqU.mono hUV)⟩
  | generalize x h ih =>
    obtain ⟨T, hT, hTφ⟩ := ih
    exact ⟨T, hT, .generalize x hTφ⟩

end Derivation

namespace Consistent

theorem sUnion {C : Set L.Theory} (hne : C.Nonempty)
    (directed : DirectedOn (· ⊆ ·) C) (consistent : ∀ T ∈ C, Consistent T) :
    Consistent (⋃₀ C) := by
  intro hfalse
  obtain ⟨T, hT, hTfalse⟩ := hfalse.directedUnion hne directed
  exact consistent T hT hTfalse

theorem insert_or_insert_not {T : L.Theory} (hT : Consistent T) (σ : L.Sentence) :
    Consistent (insert σ T) ∨ Consistent (insert σ.not T) := by
  classical
  by_cases hσ : Derivation T (sentenceFormula σ)
  · exact Or.inl (hT.insert_of_derivable σ hσ)
  · exact Or.inr ((consistent_insert_not_iff T σ).mpr hσ)

theorem of_model {T : L.Theory} (D : Type w) [Nonempty D] [L.Structure D]
    [FirstOrder.Language.Theory.Model D T] : Consistent T := by
  classical
  intro hfalse
  exact hfalse.sound (fun _ => Classical.choice (inferInstance : Nonempty D))

end Consistent

/-- Zorn's upper bounds are actual unions with proved syntactic consistency. -/
theorem exists_maximal_consistent (T : L.Theory) (hT : Consistent T) :
    ∃ U : L.Theory, T ⊆ U ∧ Maximal Consistent U := by
  apply zorn_subset_nonempty {U : L.Theory | Consistent U} ?_ T hT
  intro C hC chain hne
  refine ⟨⋃₀ C, Consistent.sUnion hne chain.directedOn (fun U hU => hC hU), ?_⟩
  intro U hU σ hσ
  exact Set.mem_sUnion.mpr ⟨U, hU, hσ⟩

namespace MaximalConsistency

variable {T : L.Theory}

theorem derivation_iff_mem (maximal : Maximal Consistent T) (σ : L.Sentence) :
    Derivation T (sentenceFormula σ) ↔ σ ∈ T := by
  refine ⟨fun hσ => ?_, fun hσ => .theory σ hσ⟩
  exact maximal.mem_of_prop_insert (maximal.prop.insert_of_derivable σ hσ)

theorem mem_or_not_mem (maximal : Maximal Consistent T) (σ : L.Sentence) :
    σ ∈ T ∨ σ.not ∈ T := by
  classical
  by_cases hσ : σ ∈ T
  · exact Or.inl hσ
  · have hinc : ¬Consistent (insert σ T) :=
      fun hc => hσ (maximal.mem_of_prop_insert hc)
    have hneg : Derivation T (sentenceFormula σ.not) := by
      by_contra h
      exact hinc ((consistent_insert_iff T σ).mpr h)
    exact Or.inr ((derivation_iff_mem maximal σ.not).mp hneg)

theorem not_mem_iff (maximal : Maximal Consistent T) (σ : L.Sentence) :
    σ.not ∈ T ↔ σ ∉ T := by
  constructor
  · intro hneg hσ
    exact maximal.prop (.mp (.theory σ.not hneg) (.theory σ hσ))
  · intro hσ
    exact (mem_or_not_mem maximal σ).resolve_left hσ

theorem falsum_not_mem (maximal : Maximal Consistent T) : (⊥ : L.Sentence) ∉ T :=
  fun hfalse => maximal.prop (.theory _ hfalse)

theorem imp_mem_iff (maximal : Maximal Consistent T) (σ τ : L.Sentence) :
    σ.imp τ ∈ T ↔ σ ∉ T ∨ τ ∈ T := by
  classical
  constructor
  · intro h
    by_cases hσ : σ ∈ T
    · right
      apply (derivation_iff_mem maximal τ).mp
      exact .mp (.theory (σ.imp τ) h) (.theory σ hσ)
    · exact Or.inl hσ
  · rintro (hσ | hτ)
    · apply (derivation_iff_mem maximal (σ.imp τ)).mp
      have hneg : Derivation T (sentenceFormula σ.not) :=
        .theory σ.not ((not_mem_iff maximal σ).mpr hσ)
      exact hneg.impTrans (Derivation.explosion (sentenceFormula τ))
    · apply (derivation_iff_mem maximal (σ.imp τ)).mp
      exact (Derivation.theory τ hτ).impOf (sentenceFormula σ)

end MaximalConsistency

/-- A nonderivable sentence has a genuinely constructed complete consistent
    extension containing its negation. This is not yet a countermodel. -/
theorem exists_maximal_refuting (T : L.Theory) (σ : L.Sentence)
    (hσ : ¬Derivation T (sentenceFormula σ)) :
    ∃ U : L.Theory, T ⊆ U ∧ Maximal Consistent U ∧ σ.not ∈ U ∧ σ ∉ U := by
  obtain ⟨U, hsub, hmax⟩ := exists_maximal_consistent (insert σ.not T)
    ((consistent_insert_not_iff T σ).mpr hσ)
  have hneg : σ.not ∈ U := hsub (Set.mem_insert σ.not T)
  exact ⟨U, (Set.subset_insert σ.not T).trans hsub, hmax, hneg,
    (MaximalConsistency.not_mem_iff hmax σ).mp hneg⟩

end Alexander313.FirstOrderCalculus
