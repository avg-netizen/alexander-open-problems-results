import Alexander313.GenericityConstruction
import Alexander313.Effective.EmptyColumnProgram
import Alexander313.FinitePolicy

/-!
# Column-wise admissibility and core genericity

Core genericity needs exactly one effectivity fact about the outside owners:
every numerical parameter column of their raw predicates is recursively
enumerable. A joint program for the whole predicate family is not needed,
since a column fixes the owner and the argument skeleton. This makes the
reconstructed predicates of note 24 §7 admissible by a case split on their
literal skeleton, with each case an actual program column.

`ColumnAdmissible` is the admissibility notion of the whole-ideal genericity
induction. The source family, shape restrictions and skeleton selections are
column admissible. These declarations belong to the checked completion chain.
-/

namespace Alexander313

/-- Every numerical parameter column of every owner is an actual W column. -/
def ColumnRE (P : RawPredicates Nat) : Prop :=
  ∀ (a : Nat) (φ : Formula Nat) (x : Nat) (s : Assignment),
    ∃ c : Nat, ∀ n, W c n ↔ P a (φ.close (Function.update s x n))

def ColumnAdmissible (P : RawPredicates Nat) : Prop := RawAlphabetic P ∧ ColumnRE P

/-- An actual program column for any recognizer, any owner key and any
numerical parameter instance. The recognizer is queried on literal codes. -/
theorem program_parameter_column (prog : Program) (key : Nat) (φ : Formula Nat)
    (x : Nat) (s : Assignment) :
    ∃ c : Nat, ∀ n, W c n ↔
      prog.domain (Nat.pair key ((φ.close (Function.update s x n)).code id)) := by
  let p := unaryColumnCompiler (((prog, key), (φ.parameterInstance x s).code id), x)
  refine ⟨Encodable.encode p, fun n => ?_⟩
  have decode : Nat.Partrec.Code.ofNatCode (Encodable.encode p) = p :=
    Denumerable.ofNat_encode p
  rw [W, decode]
  dsimp only [p]
  rw [unaryColumnCompiler_eval, Formula.substCode_code, Formula.parameterInstance_subst]
  rfl

theorem column_of_false {Q : Nat → Prop} (h : ∀ n, ¬ Q n) : ∃ c, ∀ n, W c n ↔ Q n :=
  ⟨EmptyColumn.index, fun n =>
    ⟨fun hw => absurd hw (EmptyColumn.not_W n), fun hq => absurd hq (h n)⟩⟩

theorem column_congr {Q Q' : Nat → Prop} (h : ∀ n, Q n ↔ Q' n)
    (hc : ∃ c, ∀ n, W c n ↔ Q n) : ∃ c, ∀ n, W c n ↔ Q' n := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, fun n => (hc n).trans (h n)⟩

theorem MachineFamily.columnRE (F : MachineFamily) : ColumnRE F.effective.proves := by
  intro a φ x s
  exact F.effective.parameter_column_exists F.canonical_owners a φ x s

theorem MachineFamily.columnAdmissible (F : MachineFamily) :
    ColumnAdmissible F.effective.proves :=
  ⟨F.rawAlphabetic, F.columnRE⟩

/-- Restriction to owner/skeleton classes, with arbitrary (classical) classes. -/
theorem ColumnRE.restrict {P : RawPredicates Nat} (hP : ColumnRE P)
    (keep : Nat → Shape Nat → Prop) :
    ColumnRE (fun a θ => keep a θ.shape ∧ P a θ) := by
  intro a φ x s
  by_cases hk : keep a φ.shape
  · apply column_congr _ (hP a φ x s)
    intro n
    simp only [Formula.shape_close, hk, true_and]
  · apply column_of_false
    intro n hq
    exact hk (by simpa only [Formula.shape_close] using hq.1)

theorem RawAlphabetic.restrict {P : RawPredicates Nat} (hP : RawAlphabetic P)
    (keep : Nat → Shape Nat → Prop) :
    RawAlphabetic (fun a θ => keep a θ.shape ∧ P a θ) := by
  intro a φ ψ hφ hψ hα
  change (keep a φ.shape ∧ P a φ) ↔ (keep a ψ.shape ∧ P a ψ)
  rw [hα.shape_eq]
  exact and_congr Iff.rfl (hP a φ ψ hφ hψ hα)

theorem ColumnAdmissible.restrict {P : RawPredicates Nat} (hP : ColumnAdmissible P)
    (keep : Nat → Shape Nat → Prop) :
    ColumnAdmissible (fun a θ => keep a θ.shape ∧ P a θ) :=
  ⟨hP.1.restrict keep, hP.2.restrict keep⟩

/-- Selection between two predicates by owner and argument skeleton. -/
def selectPredicates (keep : Nat → Shape Nat → Prop) (P₁ P₂ : RawPredicates Nat) :
    RawPredicates Nat :=
  fun a θ => (keep a θ.shape ∧ P₁ a θ) ∨ (¬ keep a θ.shape ∧ P₂ a θ)

theorem selectPredicates_pos {keep : Nat → Shape Nat → Prop} {P₁ P₂ : RawPredicates Nat}
    {a : Nat} {θ : Formula Nat} (h : keep a θ.shape) :
    selectPredicates keep P₁ P₂ a θ ↔ P₁ a θ := by
  simp only [selectPredicates, h, true_and, not_true_eq_false, false_and, or_false]

theorem selectPredicates_neg {keep : Nat → Shape Nat → Prop} {P₁ P₂ : RawPredicates Nat}
    {a : Nat} {θ : Formula Nat} (h : ¬ keep a θ.shape) :
    selectPredicates keep P₁ P₂ a θ ↔ P₂ a θ := by
  simp only [selectPredicates, h, false_and, not_false_eq_true, true_and, false_or]

theorem ColumnRE.select (keep : Nat → Shape Nat → Prop) {P₁ P₂ : RawPredicates Nat}
    (h₁ : ColumnRE P₁) (h₂ : ColumnRE P₂) : ColumnRE (selectPredicates keep P₁ P₂) := by
  intro a φ x s
  by_cases hk : keep a φ.shape
  · apply column_congr _ (h₁ a φ x s)
    intro n
    exact (selectPredicates_pos (by simpa only [Formula.shape_close] using hk)).symm
  · apply column_congr _ (h₂ a φ x s)
    intro n
    exact (selectPredicates_neg (by simpa only [Formula.shape_close] using hk)).symm

theorem RawAlphabetic.select (keep : Nat → Shape Nat → Prop) {P₁ P₂ : RawPredicates Nat}
    (h₁ : RawAlphabetic P₁) (h₂ : RawAlphabetic P₂) :
    RawAlphabetic (selectPredicates keep P₁ P₂) := by
  intro a φ ψ hφ hψ hα
  have hs : φ.shape = ψ.shape := hα.shape_eq
  by_cases hk : keep a φ.shape
  · rw [selectPredicates_pos hk, selectPredicates_pos (hs ▸ hk)]
    exact h₁ a φ ψ hφ hψ hα
  · rw [selectPredicates_neg hk, selectPredicates_neg (hs ▸ hk)]
    exact h₂ a φ ψ hφ hψ hα

theorem ColumnAdmissible.select (keep : Nat → Shape Nat → Prop) {P₁ P₂ : RawPredicates Nat}
    (h₁ : ColumnAdmissible P₁) (h₂ : ColumnAdmissible P₂) :
    ColumnAdmissible (selectPredicates keep P₁ P₂) :=
  ⟨RawAlphabetic.select keep h₁.1 h₂.1, ColumnRE.select keep h₁.2 h₂.2⟩

/-- The empty predicate family. -/
def emptyPredicates : RawPredicates Nat := fun _ _ => False

theorem emptyPredicates_admissible : ColumnAdmissible emptyPredicates := by
  refine ⟨fun _ _ _ _ _ _ => Iff.rfl, ?_⟩
  intro a φ x s
  exact column_of_false (fun _ h => h)

theorem emptyPredicates_sound (a : Nat) : RawSound emptyPredicates a :=
  fun _ _ h => False.elim h

theorem rawShapeMask_columnAdmissible {P : RawPredicates Nat} (hP : ColumnAdmissible P)
    (full : Nat → Prop) (H : Finset (Nat × Shape Nat)) :
    ColumnAdmissible (rawShapeMask P full H) :=
  hP.restrict (fun a sh => full a ∨ (a, sh) ∈ H)

/-- The literal parameter-mechanicalness sentence from one column per
parameter assignment; no joint recognizer of the family is used. -/
theorem column_parameter_mechanical_truth (P : RawPredicates Nat) (hcol : ColumnRE P)
    (A : ArithmeticCoding Nat) (j x e : Nat) (φ : Formula Nat) (fresh : e ∉ φ.freeVars)
    (distinct : e ≠ x) (sound : RawSound P j) (s : Assignment) :
    filteredTruth P (parameterMechanicalSentence A j x e φ) s := by
  apply truth_universalClosure true P _ _ s
  intro t
  obtain ⟨c, column⟩ := hcol j φ x t
  refine ⟨c, ?_⟩
  intro n
  have knowColumn : filteredTruth P (.know j φ)
      (Function.update (Function.update t e c) x n) ↔ W c n := by
    rw [filtered_know_iff P sound,
      Formula.close_update_fresh_before φ x e n c t fresh]
    exact (column n).symm
  have memberColumn : filteredTruth P (A.member (.var e) (.var x))
      (Function.update (Function.update t e c) x n) ↔ W c n := by
    change truth true P (A.member (.var e) (.var x))
      (Function.update (Function.update t e c) x n) ↔ W c n
    rw [A.correct]
    simp only [Term.eval, Function.update_self, Function.update_of_ne distinct]
  exact ⟨fun h => memberColumn.mpr (knowColumn.mp h),
    fun h => knowColumn.mpr (memberColumn.mp h)⟩

/-- Note 26 §4, G_U, with column-wise admissible outside predicates. -/
theorem CommonCorePresentation.core_genericity_columns {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (P : RawPredicates Nat) (hP : ColumnAdmissible P)
    (retained : ∀ θ, P 0 θ ↔ C.family.effective.proves 0 θ)
    (outside : ∀ j, RawSound P (j + 1)) : RawSound P 0 := by
  apply sound_of_true_generators P (FilteredRealization.ofAlphabetic P hP.1) 0
    (CommonCoreGenerator R C.arithmetic C.family 0)
  · intro σ hσ n s
    exact (retained _).mpr (C.prefix_instance hσ n s)
  · intro θ hθ
    exact (retained θ).trans (C.proofs 0 θ hθ)
  · intro σ hσ s
    cases hσ with
    | background i h => exact C.background_true_in_core_extension P hP.1 retained h s
    | core_mechanical j x e φ fresh distinct =>
      exact column_parameter_mechanical_truth P hP.2 C.arithmetic (j + 1) x e φ
        fresh distinct (outside j) s

end Alexander313
