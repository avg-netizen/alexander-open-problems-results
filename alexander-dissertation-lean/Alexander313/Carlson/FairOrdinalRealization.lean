import Alexander313.Carlson.FairSemantics
import Alexander313.Carlson.OrdinalRealization
import Alexander313.Carlson.SemanticUniqueness

/-!
# Exact ordinal realizations of covered fair sequences

The intrinsic finite-copy equations of a covered fair limit are transported
to its ordinal order type. Uniqueness of those equations identifies both
relations with Carlson's recursively defined ordinal relations.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {S : GeneratingSequence ℚ}

/-- The coupled semantic equations survive any change of the limit's
ordered presentation. This also includes the empty limit. -/
theorem Fair.semanticEquations_orderIso (hS : S.Fair) (hP : Str.Covered (S.stage 0))
    {β : Type*} [LinearOrder β] (e : S.Limit ≃o β) :
    let T₁ := fun x y : β => S.limitRel .one (e.symm x) (e.symm y)
    let T₂ := fun x y : β => S.limitRel .two (e.symm x) (e.symm y)
    (∀ a b, T₁ a b ↔ a ≤ b ∧ FirstCondition T₁ T₂ a b) ∧
      (∀ a b, T₂ a b ↔ SecondCondition T₁ T₂ a b) := by
  let T₁ := fun x y : β => S.limitRel .one (e.symm x) (e.symm y)
  let T₂ := fun x y : β => S.limitRel .two (e.symm x) (e.symm y)
  have h₁ : ∀ x y, S.limitRel .one x y ↔ T₁ (e x) (e y) := by
    intro x y
    simp only [T₁, OrderIso.symm_apply_apply]
  have h₂ : ∀ x y, S.limitRel .two x y ↔ T₂ (e x) (e y) := by
    intro x y
    simp only [T₂, OrderIso.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · intro a b
    constructor
    · intro h
      obtain ⟨hab, hcopy⟩ := (hS.rel_one_iff hP (e.symm a) (e.symm b)).mp h
      refine ⟨e.symm.le_iff_le.mp hab, ?_⟩
      simpa only [OrderIso.apply_symm_apply] using hcopy.orderIso e h₁ h₂
    · rintro ⟨hab, hcopy⟩
      exact (hS.rel_one_iff hP (e.symm a) (e.symm b)).mpr
        ⟨e.symm.monotone hab,
          hcopy.orderIso e.symm (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)⟩
  · intro a b
    constructor
    · intro h
      obtain ⟨hab, hlinked, hcofinal⟩ :=
        (hS.rel_two_iff hP (e.symm a) (e.symm b)).mp h
      refine ⟨e.symm.le_iff_le.mp hab, ?_, ?_⟩
      · have hu : ∀ x, S.limitRel .one x (e.symm b) ↔ T₁ (e x) b := by
          intro x
          simp only [T₁, OrderIso.symm_apply_apply]
        have hl : ∀ x, S.limitRel .one x (e.symm a) ↔ T₁ (e x) a := by
          intro x
          simp only [T₁, OrderIso.symm_apply_apply]
        simpa only [OrderIso.apply_symm_apply] using hlinked.orderIso e h₁ h₂ hu hl
      · simpa only [OrderIso.apply_symm_apply] using hcofinal.orderIso e h₁ h₂
    · rintro ⟨hab, hlinked, hcofinal⟩
      exact (hS.rel_two_iff hP (e.symm a) (e.symm b)).mpr
        ⟨e.symm.monotone hab,
          hlinked.orderIso e.symm (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
            (fun _ => Iff.rfl) (fun _ => Iff.rfl),
          hcofinal.orderIso e.symm (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)⟩

/-- The existence conclusion of Carlson's Lemma 14.9, using
Lemma 14.8(4,7--8): a covered fair limit is exactly an initial segment
of the ordinal structure, including both relations. -/
theorem Fair.ordinalRealization (hS : S.Fair) (hP : Str.Covered (S.stage 0)) :
    Nonempty (OrdinalRealization S) := by
  obtain ⟨o, ⟨e⟩⟩ := S.exists_ordinal_orderIso hP
  obtain ⟨h₁, h₂⟩ := hS.semanticEquations_orderIso hP e
  have h := ordinalRelations_unique h₁ h₂
  refine ⟨⟨o, e, ?_, ?_⟩⟩
  · intro x y
    simpa only [OrderIso.symm_apply_apply] using (h (e x) (e y)).1
  · intro x y
    simpa only [OrderIso.symm_apply_apply] using (h (e x) (e y)).2

/-- Every covered rational pattern starts a fair sequence with an exact
ordinal realization. The given initial structure is preserved literally. -/
theorem exists_fair_ordinalRealization (P : Str ℚ) (hP : P.IsPattern)
    (hcov : Str.Covered P) :
    ∃ S : GeneratingSequence ℚ, S.stage 0 = P ∧ S.Fair ∧
      Nonempty (OrdinalRealization S) := by
  obtain ⟨S, hzero, hfair⟩ := exists_fair P hP
  have hcov₀ : Str.Covered (S.stage 0) := by simpa only [hzero] using hcov
  exact ⟨S, hzero, hfair, hfair.ordinalRealization hcov₀⟩

/-- Carlson's Theorem 14.10(1--2), pure rational presentation: every
covered pattern has an exact ordinal copy whose labels are pointwise
least among all ordinal coverings. Pointwise minimality also implies
the isominimality assertion (3). This existence proof is classical. -/
theorem exists_minimal_ordinal_copy (P : Str ℚ) (hP : P.IsPattern)
    (hcov : Str.Covered P) :
    ∃ h : ℚ → Ordinal.{0},
      Str.IsIso P (Str.ofOrdinals (P.U.image h)) h ∧
      ∀ g : ℚ → Ordinal.{0}, Str.CoveringR P g → ∀ x ∈ P.U, h x ≤ g x := by
  obtain ⟨S, hzero, _, ⟨R⟩⟩ := exists_fair_ordinalRealization P hP hcov
  refine ⟨R.label, ?_, ?_⟩
  · simpa only [OrdinalRealization.stagePattern, hzero] using R.stage_isIso 0
  · intro g hg x hx
    have hg₀ : Str.CoveringR (S.stage 0) g := by simpa only [hzero] using hg
    exact R.label_le_covering 0 hg₀ (by simpa only [hzero] using hx)

end GeneratingSequence
end Alexander313.Carlson
