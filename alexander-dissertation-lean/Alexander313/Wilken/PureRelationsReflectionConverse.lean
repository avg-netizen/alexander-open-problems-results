import Alexander313.Wilken.PureRelationsFiniteReflection
import Alexander313.Wilken.PureRelationsTransitivity

/-!
# The actual finite-reflection criterion for the constructed first relation

Every literal matrix retains its truth under an actual full expanded pattern
map. For an upper existential statement, the finite set contains EVERY
original lower parameter and EVERY witness. Actual finite reflection fixes
the parameters and constructs lower witnesses with the same matrix truth.
Thus actual finite reflection implies actual R1, with the necessary ordinary
endpoint order. No elementarity or matrix-truth oracle is an extra premise.
These uncompiled source candidates remain outside the package checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

/-- The full actual expanded finite pattern transports every literal matrix,
including negative relations and both Boolean connectives. -/
theorem matrix_realize_pattern {n : Nat} (φ : Matrix n)
    (F : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (pattern : PreservesPattern F f) (v : Fin n → Ordinal.{0}) (hv : ∀ i, v i ∈ F) :
    φ.realize R1 R2 (fun i => f (v i)) ↔ φ.realize R1 R2 v := by
  induction φ with
  | falsum => rfl
  | equal i j => exact pattern.1 _ (hv i) _ (hv j)
  | lessEqual i j =>
    change f (v i) ≤ f (v j) ↔ v i ≤ v j
    simpa only [not_lt] using not_congr (pattern.2.1 _ (hv j) _ (hv i))
  | first i j => exact pattern.2.2.1 _ (hv i) _ (hv j)
  | second i j => exact pattern.2.2.2 _ (hv i) _ (hv j)
  | neg φ ih => exact not_congr ih
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | disj φ ψ ihφ ihψ => exact or_congr ihφ ihψ

/-- Genuine finite reflection constructs lower witnesses for ALL original
literal Sigma1 statements, with all original lower parameters unchanged. -/
theorem finiteReflection_sigma1Elementary (α β : Ordinal.{0}) (hαβ : α ≤ β)
    (reflection : FiniteReflection α β) : Sigma1Elementary R1 R2 α β := by
  intro p m φ v hv
  constructor
  · rintro ⟨w, hw, hφ⟩
    exact ⟨w, tupleBelow_mono hαβ hw, hφ⟩
  · rintro ⟨w, hw, hφ⟩
    let F : Finset Ordinal.{0} := (List.ofFn v).toFinset ∪ (List.ofFn w).toFinset
    have vmem (i : Fin p) : v i ∈ F := Finset.mem_union.mpr
      (Or.inl (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    have wmem (i : Fin m) : w i ∈ F := Finset.mem_union.mpr
      (Or.inr (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    have belowF : ∀ ξ ∈ F, ξ < β := by
      intro ξ hξ
      rcases Finset.mem_union.mp hξ with hξ | hξ
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hξ)
        exact (hv i).trans_le hαβ
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hξ)
        exact hw i
    obtain ⟨f, lower, fixed, pattern⟩ := reflection F belowF
    let w' : Fin m → Ordinal.{0} := fun i => f (w i)
    have hmem : ∀ i, Fin.append v w i ∈ F := by
      apply (Fin.forall_fin_add (fun i => Fin.append v w i ∈ F)).mpr
      constructor
      · intro i
        simpa only [Fin.append_left] using vmem i
      · intro i
        simpa only [Fin.append_right] using wmem i
    have he : (fun i => f (Fin.append v w i)) = Fin.append v w' := by
      apply funext
      apply (Fin.forall_fin_add
        (fun i => f (Fin.append v w i) = Fin.append v w' i)).mpr
      constructor
      · intro i
        simpa only [Fin.append_left] using fixed (v i) (vmem i) (hv i)
      · intro i
        simp only [Fin.append_right, w']
    refine ⟨w', fun i => lower (w i) (wmem i), ?_⟩
    simpa only [he] using (matrix_realize_pattern φ F f pattern (Fin.append v w) hmem).mpr hφ

/-- The converse criterion concerns the ACTUAL recursively constructed R1.
Its elementarity is proved from genuine finite reflection, not assumed. -/
theorem R1_of_finiteReflection (α β : Ordinal.{0}) (hαβ : α ≤ β)
    (reflection : FiniteReflection α β) : R1 α β :=
  (R1_actual_iff α β).mpr ⟨hαβ, finiteReflection_sigma1Elementary α β hαβ reflection⟩

/-- The full actual finite expanded-pattern criterion, with the original
ordinary endpoint order retained explicitly in the reflected direction. -/
theorem R1_iff_finiteReflection (α β : Ordinal.{0}) :
    R1 α β ↔ α ≤ β ∧ FiniteReflection α β :=
  ⟨fun h => ⟨R1_le h, finiteLabelReflection α β h⟩,
    fun h => R1_of_finiteReflection α β h.1 h.2⟩

theorem R1_iff_finiteReflection_of_le (α β : Ordinal.{0}) (hαβ : α ≤ β) :
    R1 α β ↔ FiniteReflection α β :=
  ⟨finiteLabelReflection α β, R1_of_finiteReflection α β hαβ⟩

end Alexander313.Wilken.PureRelations
