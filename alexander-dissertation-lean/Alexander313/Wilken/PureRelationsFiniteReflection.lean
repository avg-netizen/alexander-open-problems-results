import Alexander313.Wilken.PureRelationsFiniteDiagrams

/-!
# Actual expanded finite-pattern reflection from the constructed R1

The original upper structure uses the previously constructed pure relations.
The complete finite matrix reflects all positive AND negative facts and fixes
every existing label below alpha. The witnesses define an actual function on
the original finite set. This discharges finite expanded-pattern reflection
for the actual semantic R1/R2, without a supplied reflection function.

This ordinal-domain statement is the universe-correct counterpart of the
recorded syntax's small coded-label interface. Pullback to that actual public
code domain, recursive decisions, separated R2 room and cofinality remain
separate proofs. All proof candidates remain uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

def PreservesPattern (F : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Prop :=
  (∀ x ∈ F, ∀ y ∈ F, f x = f y ↔ x = y) ∧
  (∀ x ∈ F, ∀ y ∈ F, f x < f y ↔ x < y) ∧
  (∀ x ∈ F, ∀ y ∈ F, R1 (f x) (f y) ↔ R1 x y) ∧
  (∀ x ∈ F, ∀ y ∈ F, R2 (f x) (f y) ↔ R2 x y)

def FiniteReflection (α β : Ordinal.{0}) : Prop :=
  ∀ F : Finset Ordinal.{0}, (∀ x ∈ F, x < β) →
    ∃ f : Ordinal.{0} → Ordinal.{0}, (∀ x ∈ F, f x < α) ∧
      (∀ x ∈ F, x < α → f x = x) ∧ PreservesPattern F f

theorem actual_tuple_reflection {n : Nat} (α β : Ordinal.{0})
    (hR : R1 α β) (hαβ : α < β) (x : Fin n → Ordinal.{0}) (hx : TupleBelow β x) :
    ∃ w : Fin n → Ordinal.{0}, TupleBelow α w ∧
      (∀ i, x i < α → w i = x i) ∧
      (∀ i j, w i = w j ↔ x i = x j) ∧ (∀ i j, w i < w j ↔ x i < x j) ∧
      (∀ i j, R1 (w i) (w j) ↔ R1 (x i) (x j)) ∧
      (∀ i j, R2 (w i) (w j) ↔ R2 (x i) (x j)) := by
  obtain ⟨w, hw, fixed, heq, hle, h₁, h₂⟩ :=
    tuple_reflection (prefixFirst β) (prefixSecond β) α β hαβ ((R1_iff α β).mp hR).2 x hx
  have hwβ (i : Fin n) : w i < β := (hw i).trans hαβ
  refine ⟨w, hw, fixed, heq, ?_, ?_, ?_⟩
  · intro i j
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle i j, hle j i]
  · intro i j
    exact (prefixFirst_below (hwβ j)).symm.trans ((h₁ i j).trans (prefixFirst_below (hx j)))
  · intro i j
    exact (prefixSecond_below (hwβ j)).symm.trans ((h₂ i j).trans (prefixSecond_below (hx j)))

/-- Every actual R1 pair has finite reflection in the FULL expanded
language, including equality, order, R1, R2 and all prescribed lower labels. -/
theorem finiteLabelReflection (α β : Ordinal.{0}) (hR : R1 α β) :
    FiniteReflection α β := by
  intro F below
  by_cases hab : α = β
  · subst β
    refine ⟨id, below, (fun _ _ _ => rfl), ?_⟩
    exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
      fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
  · have hαβ : α < β := lt_of_le_of_ne (R1_le hR) hab
    let e : F ≃ Fin F.card := F.equivFin
    let x : Fin F.card → Ordinal.{0} := fun i => (e.symm i).val
    have xmem (i : Fin F.card) : x i ∈ F := (e.symm i).property
    have xindex (μ : Ordinal.{0}) (hμ : μ ∈ F) : x (e ⟨μ, hμ⟩) = μ :=
      congrArg Subtype.val (e.symm_apply_apply ⟨μ, hμ⟩)
    obtain ⟨w, hw, fixed, heq, hlt, h₁, h₂⟩ :=
      actual_tuple_reflection α β hR hαβ x (fun i => below (x i) (xmem i))
    let f : Ordinal.{0} → Ordinal.{0} := fun μ => if hμ : μ ∈ F then w (e ⟨μ, hμ⟩) else μ
    have fmem (μ : Ordinal.{0}) (hμ : μ ∈ F) : f μ = w (e ⟨μ, hμ⟩) := by
      simp only [f, dif_pos hμ]
    refine ⟨f, ?_, ?_, ?_⟩
    · intro μ hμ
      rw [fmem μ hμ]
      exact hw _
    · intro μ hμ hμα
      rw [fmem μ hμ]
      exact (fixed _ (by simpa only [xindex μ hμ] using hμα)).trans (xindex μ hμ)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          heq (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          hlt (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          h₁ (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          h₂ (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)

theorem finiteLabelReflection_of_R2 (α β : Ordinal.{0}) (hR : R2 α β) :
    FiniteReflection α β :=
  finiteLabelReflection α β (R2_R1 hR)

end Alexander313.Wilken.PureRelations
