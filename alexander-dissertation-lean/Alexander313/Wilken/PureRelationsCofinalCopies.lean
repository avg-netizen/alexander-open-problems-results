import Alexander313.Wilken.PureRelationsCofinalCopySupport
import Alexander313.Wilken.PureRelationsFiniteReflection
import Alexander313.Wilken.PureRelationsPi2Transfer

/-!
# Actual cofinally repeated finite copies in source Lemma1.7(1)

For every lower cutoff, the genuine first-relation reflection acts on the
original pattern AND that cutoff. It fixes all original lower points and
the cutoff, so every fresh point is genuinely copied above it. This proves
the lower universal-existential sentence for the literal complete diagram.
Actual R2 transfers that WHOLE sentence, constructing copies above ANY cutoff
below beta. All positive and negative equality/order/R1/R2 facts are retained.
No repeated-pattern, copy, cofinal room, reflection or realization oracle is
an input. These uncompiled drafts stay outside the checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.CofinalCopies

/-- Actual R1 reflection proves the ORIGINAL lower repeated-pattern
sentence; the arbitrary lower cut is included in the same finite pattern. -/
theorem lower_repetition {n : Nat} (α β : Ordinal.{0}) (hR : R1 α β) (hαβ : α < β)
    (x : Fin n → Ordinal.{0}) (hx : TupleBelow β x) :
    pi2Truth R1 R2 α n 1 n (diagram α R1 R2 x) (diagramParameters α x) := by
  intro z hz
  let F : Finset Ordinal.{0} := (List.ofFn x).toFinset ∪ {z 0}
  have xmem (i : Fin n) : x i ∈ F := Finset.mem_union.mpr
    (Or.inl (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have zmem : z 0 ∈ F := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
  have belowF : ∀ μ ∈ F, μ < β := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hμ)
      exact hx i
    · have he : μ = z 0 := Finset.mem_singleton.mp hμ
      simpa only [he] using (hz 0).trans hαβ
  obtain ⟨f, lower, fixed, pattern⟩ := PureRelations.finiteLabelReflection α β hR F belowF
  let w : Fin n → Ordinal.{0} := fun i => f (x i)
  refine ⟨w, fun i => lower (x i) (xmem i), ?_⟩
  apply (diagram_realize α R1 R2 x (diagramParameters α x) z w).mpr
  intro i
  refine ⟨?_, ?_, fun j => ⟨pattern.1 _ (xmem i) _ (xmem j), ?_,
    pattern.2.2.1 _ (xmem i) _ (xmem j), pattern.2.2.2 _ (xmem i) _ (xmem j)⟩⟩
  · intro hi
    simpa only [diagramParameters, hi, ↓reduceIte, w, fixed (x i) (xmem i) hi]
  · intro hi
    have hh := (pattern.2.1 (z 0) zmem (x i) (xmem i)).mpr ((hz 0).trans_le hi)
    simpa only [fixed (z 0) zmem (hz 0), w] using hh
  · simpa only [not_lt] using not_congr (pattern.2.1 _ (xmem j) _ (xmem i))

/-- Literal actual R2 transfers the complete repeated-pattern sentence.
Fresh points are above EVERY chosen beta cutoff, with all lower points fixed. -/
theorem tuple_cofinal {n : Nat} (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β)
    (x : Fin n → Ordinal.{0}) (hx : TupleBelow β x) (c : Ordinal.{0}) (hc : c < β) :
    ∃ w : Fin n → Ordinal.{0}, TupleBelow β w ∧
      (∀ i, x i < α → w i = x i) ∧ (∀ i, α ≤ x i → c < w i) ∧
      (∀ i j, w i = w j ↔ x i = x j) ∧ (∀ i j, w i < w j ↔ x i < x j) ∧
      (∀ i j, R1 (w i) (w j) ↔ R1 (x i) (x j)) ∧
      (∀ i j, R2 (w i) (w j) ↔ R2 (x i) (x j)) := by
  have h1 := R2_R1 hR
  have hα : 0 < α := sigma1_nonzero_lower _ _ α β ((R1_iff α β).mp h1).2
    ((bot_le : (0 : Ordinal.{0}) ≤ α).trans_lt hαβ)
  have hp := diagramParameters_below α hα x
  have hu := (R2_pi2Truth_iff α β hR n 1 n (diagram α R1 R2 x)
    (diagramParameters α x) hp).mp (lower_repetition α β h1 hαβ x hx)
  obtain ⟨w, hw, hd⟩ := hu (fun _ : Fin 1 => c) (fun _ => hc)
  have he := (diagram_realize α R1 R2 x (diagramParameters α x) (fun _ => c) w).mp hd
  have hle (i j : Fin n) : w i ≤ w j ↔ x i ≤ x j := ((he i).2.2 j).2.1
  refine ⟨w, hw, ?_, (fun i hi => (he i).2.1 hi),
    (fun i j => ((he i).2.2 j).1), ?_,
    (fun i j => ((he i).2.2 j).2.2.1), (fun i j => ((he i).2.2 j).2.2.2)⟩
  · intro i hi
    have hf := ((he i).1 hi).symm
    simpa only [diagramParameters, hi, ↓reduceIte] using hf
  · intro i j
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle i j, hle j i]

/-- The original finite-set cofinal-copy conclusion in Lemma1.7(1).
The nonempty upper pattern and ALL original lower points are retained. -/
theorem finite_cofinal_copy (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β)
    (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < α)
    (hY : ∀ y ∈ Y, α ≤ y ∧ y < β) (hYn : Y.Nonempty)
    (c : Ordinal.{0}) (hc : c < β) :
    ∃ f : Ordinal.{0} → Ordinal.{0}, PreservesPattern (X ∪ Y) f ∧
      (∀ x ∈ X, f x = x) ∧ (∀ y ∈ Y, c < f y ∧ f y < β) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x < f y) := by
  let F := X ∪ Y
  let e : F ≃ Fin F.card := F.equivFin
  let x : Fin F.card → Ordinal.{0} := fun i => (e.symm i).val
  have xmem (i : Fin F.card) : x i ∈ F := (e.symm i).property
  have xindex (μ : Ordinal.{0}) (hμ : μ ∈ F) : x (e ⟨μ, hμ⟩) = μ :=
    congrArg Subtype.val (e.symm_apply_apply ⟨μ, hμ⟩)
  have hx : TupleBelow β x := by
    intro i
    rcases Finset.mem_union.mp (xmem i) with hi | hi
    · exact (hX _ hi).trans hαβ
    · exact (hY _ hi).2
  obtain ⟨w, hw, fixed, above, heq, hlt, h₁, h₂⟩ := tuple_cofinal α β hR hαβ x hx c hc
  let f : Ordinal.{0} → Ordinal.{0} := fun μ => if hμ : μ ∈ F then w (e ⟨μ, hμ⟩) else μ
  have fmem (μ : Ordinal.{0}) (hμ : μ ∈ F) : f μ = w (e ⟨μ, hμ⟩) := by
    simp only [f, dif_pos hμ]
  have pattern : PreservesPattern F f := by
    refine ⟨?_, ?_, ?_, ?_⟩
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
  have fixedX (μ : Ordinal.{0}) (hμ : μ ∈ X) : f μ = μ := by
    have hm : μ ∈ F := Finset.mem_union.mpr (Or.inl hμ)
    rw [fmem μ hm]
    exact (fixed _ (by simpa only [xindex μ hm] using hX μ hμ)).trans (xindex μ hm)
  refine ⟨f, pattern, fixedX, ?_, ?_⟩
  · intro μ hμ
    have hm : μ ∈ F := Finset.mem_union.mpr (Or.inr hμ)
    rw [fmem μ hm]
    exact ⟨above _ (by simpa only [xindex μ hm] using (hY μ hμ).1), hw _⟩
  · intro μ hμ ν hν
    have hh := (pattern.2.1 μ (Finset.mem_union.mpr (Or.inl hμ))
      ν (Finset.mem_union.mpr (Or.inr hν))).mpr ((hX μ hμ).trans_le (hY ν hν).1)
    simpa only [fixedX μ hμ] using hh

end Alexander313.Wilken.PureRelations.CofinalCopies
