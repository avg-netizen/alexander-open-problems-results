import Alexander313.Wilken.PureRelationsSemantics

/-!
# Genuine finite expanded diagrams in the pure relational language

The matrix writes EVERY positive and negative equality, order, R1 and R2
fact on the displayed finite tuple. It also fixes every tuple entry already
below the target initial segment by an equality to an actual parameter.
Thus a reflected existential witness preserves the entire expanded pattern,
including negative facts and prescribed labels. No pattern map is supplied.
These proof candidates remain uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

def Matrix.literal {n : Nat} (p : Prop) (φ : Matrix n) : Matrix n :=
  @ite (Matrix n) p (Classical.propDecidable p) φ (.neg φ)

theorem literal_realize {n : Nat} (p : Prop) (φ : Matrix n)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (v : Fin n → Ordinal.{0}) :
    (Matrix.literal p φ).realize R₁ R₂ v ↔ (φ.realize R₁ R₂ v ↔ p) := by
  by_cases hp : p <;> simp [Matrix.literal, hp, Matrix.realize]

def Matrix.finiteConjunction {n : Nat} (fs : List (Matrix n)) : Matrix n :=
  fs.foldr Matrix.conj (.neg .falsum)

theorem finiteConjunction_realize {n : Nat} (fs : List (Matrix n))
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (v : Fin n → Ordinal.{0}) :
    (Matrix.finiteConjunction fs).realize R₁ R₂ v ↔ ∀ φ ∈ fs, φ.realize R₁ R₂ v := by
  induction fs with
  | nil => simp [Matrix.finiteConjunction, Matrix.realize]
  | cons φ fs ih =>
    change (φ.realize R₁ R₂ v ∧ (Matrix.finiteConjunction fs).realize R₁ R₂ v) ↔
      ∀ ψ ∈ φ :: fs, ψ.realize R₁ R₂ v
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem finiteConjunction_ofFn_realize {n m : Nat} (fs : Fin m → Matrix n)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (v : Fin n → Ordinal.{0}) :
    (Matrix.finiteConjunction (List.ofFn fs)).realize R₁ R₂ v ↔ ∀ i, (fs i).realize R₁ R₂ v := by
  rw [finiteConjunction_realize]
  constructor
  · intro h i
    exact h (fs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h φ hφ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hφ
    exact h i

def pairMatrix {n : Nat} (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) (i j : Fin n) : Matrix (n + n) :=
  .conj (Matrix.literal (x i = x j) (.equal (Fin.natAdd n i) (Fin.natAdd n j)))
    (.conj (Matrix.literal (x i ≤ x j) (.lessEqual (Fin.natAdd n i) (Fin.natAdd n j)))
      (.conj (Matrix.literal (R₁ (x i) (x j)) (.first (Fin.natAdd n i) (Fin.natAdd n j)))
        (Matrix.literal (R₂ (x i) (x j)) (.second (Fin.natAdd n i) (Fin.natAdd n j)))))

theorem pairMatrix_realize {n : Nat} (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x p w : Fin n → Ordinal.{0}) (i j : Fin n) :
    (pairMatrix R₁ R₂ x i j).realize R₁ R₂ (Fin.append p w) ↔
      (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
      (R₁ (w i) (w j) ↔ R₁ (x i) (x j)) ∧ (R₂ (w i) (w j) ↔ R₂ (x i) (x j)) := by
  simp only [pairMatrix, Matrix.realize, literal_realize, Fin.append_right]

def fixedMatrix {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0}) (i : Fin n) : Matrix (n + n) :=
  if x i < α then .equal (Fin.castAdd n i) (Fin.natAdd n i)
  else .equal (Fin.natAdd n i) (Fin.natAdd n i)

theorem fixedMatrix_realize {n : Nat} (α : Ordinal.{0})
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x p w : Fin n → Ordinal.{0}) (i : Fin n) :
    (fixedMatrix α x i).realize R₁ R₂ (Fin.append p w) ↔ (x i < α → p i = w i) := by
  by_cases hi : x i < α <;>
    simp only [fixedMatrix, hi, ↓reduceIte, Matrix.realize, Fin.append_left, Fin.append_right,
      true_implies, false_implies]

def diagram {n : Nat} (α : Ordinal.{0}) (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) : Matrix (n + n) :=
  Matrix.finiteConjunction (List.ofFn (fun i : Fin n =>
    Matrix.conj (fixedMatrix α x i)
      (Matrix.finiteConjunction (List.ofFn (fun j : Fin n => pairMatrix R₁ R₂ x i j)))))

theorem diagram_realize {n : Nat} (α : Ordinal.{0})
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x p w : Fin n → Ordinal.{0}) :
    (diagram α R₁ R₂ x).realize R₁ R₂ (Fin.append p w) ↔
      ∀ i, (x i < α → p i = w i) ∧ ∀ j,
        (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
        (R₁ (w i) (w j) ↔ R₁ (x i) (x j)) ∧ (R₂ (w i) (w j) ↔ R₂ (x i) (x j)) := by
  simp only [diagram, finiteConjunction_ofFn_realize, Matrix.realize,
    fixedMatrix_realize, pairMatrix_realize]

def diagramParameters {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0}) : Fin n → Ordinal.{0} :=
  fun i => if x i < α then x i else 0

theorem diagramParameters_below {n : Nat} (α : Ordinal.{0}) (hα : 0 < α)
    (x : Fin n → Ordinal.{0}) : TupleBelow α (diagramParameters α x) := by
  intro i
  by_cases hi : x i < α <;> simp only [diagramParameters, hi, ↓reduceIte] <;> assumption

/-- The original tuple satisfies the literal finite diagram in the upper
structure, with actual parameters only at the points that must stay fixed. -/
theorem diagram_original {n : Nat} (α : Ordinal.{0})
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0}) :
    (diagram α R₁ R₂ x).realize R₁ R₂ (Fin.append (diagramParameters α x) x) := by
  rw [diagram_realize]
  intro i
  refine ⟨?_, fun _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
  intro hi
  simp only [diagramParameters, hi, ↓reduceIte]

theorem sigma1_nonzero_lower (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (h : Sigma1Elementary R₁ R₂ α β) (hβ : 0 < β) : 0 < α := by
  let φ : Matrix (0 + 1) := .equal 0 0
  have hb : sigma1Truth R₁ R₂ β 0 1 φ Fin.elim0 :=
    ⟨fun _ => 0, fun _ => hβ, rfl⟩
  obtain ⟨w, hw, _⟩ := (h 0 1 φ Fin.elim0 (fun i => Fin.elim0 i)).mpr hb
  exact (bot_le : (0 : Ordinal.{0}) ≤ w 0).trans_lt (hw 0)

/-- Existential elementarity CONSTRUCTS a tuple preserving the entire
finite expanded pattern while fixing every original point below alpha. -/
theorem tuple_reflection {n : Nat} (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (hαβ : α < β) (h : Sigma1Elementary R₁ R₂ α β)
    (x : Fin n → Ordinal.{0}) (hx : TupleBelow β x) :
    ∃ w : Fin n → Ordinal.{0}, TupleBelow α w ∧
      (∀ i, x i < α → w i = x i) ∧
      (∀ i j, w i = w j ↔ x i = x j) ∧ (∀ i j, w i ≤ w j ↔ x i ≤ x j) ∧
      (∀ i j, R₁ (w i) (w j) ↔ R₁ (x i) (x j)) ∧
      (∀ i j, R₂ (w i) (w j) ↔ R₂ (x i) (x j)) := by
  have hα := sigma1_nonzero_lower R₁ R₂ α β h ((bot_le : (0 : Ordinal.{0}) ≤ α).trans_lt hαβ)
  have hp := diagramParameters_below α hα x
  have hu : sigma1Truth R₁ R₂ β n n (diagram α R₁ R₂ x) (diagramParameters α x) :=
    ⟨x, hx, diagram_original α R₁ R₂ x⟩
  obtain ⟨w, hw, hd⟩ := (h n n (diagram α R₁ R₂ x) (diagramParameters α x) hp).mpr hu
  have he := (diagram_realize α R₁ R₂ x (diagramParameters α x) w).mp hd
  refine ⟨w, hw, ?_, (fun i j => ((he i).2 j).1),
    (fun i j => ((he i).2 j).2.1), (fun i j => ((he i).2 j).2.2.1),
    (fun i j => ((he i).2 j).2.2.2)⟩
  intro i hi
  have hv := ((he i).1 hi).symm
  simpa only [diagramParameters, hi, ↓reduceIte] using hv

end Alexander313.Wilken.PureRelations
