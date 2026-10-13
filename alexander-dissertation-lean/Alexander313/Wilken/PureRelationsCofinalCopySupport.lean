import Alexander313.Wilken.PureRelationsFiniteDiagrams

/-!
# Literal repeated finite-pattern matrices

The original lower points are parameters. One universal point is the cut,
and the existential tuple is the whole copied pattern. The matrix fixes
every original lower point, writes ALL positive and negative pair facts in
the pure signature, and puts every original upper point above the cut.
No cofinal-copy or reflection proposition is an input to these definitions.
Uncompiled source draft outside the current checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.CofinalCopies

abbrev Arity (n : Nat) := (n + 1) + n

def parameterIndex (n : Nat) (i : Fin n) : Fin (Arity n) :=
  Fin.castAdd n (Fin.castAdd 1 i)

def cutIndex (n : Nat) : Fin (Arity n) :=
  Fin.castAdd n (Fin.natAdd n (0 : Fin 1))

def witnessIndex (n : Nat) (i : Fin n) : Fin (Arity n) :=
  Fin.natAdd (n + 1) i

def valuation {n : Nat} (p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) : Fin (Arity n) → Ordinal.{0} :=
  Fin.append (Fin.append p z) w

theorem parameter_value {n : Nat} (p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (i : Fin n) :
    valuation p z w (parameterIndex n i) = p i := by
  simp only [valuation, parameterIndex, Fin.append_left]

theorem cut_value {n : Nat} (p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) :
    valuation p z w (cutIndex n) = z 0 := by
  simp only [valuation, cutIndex, Fin.append_left, Fin.append_right]

theorem witness_value {n : Nat} (p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (i : Fin n) :
    valuation p z w (witnessIndex n i) = w i := by
  simp only [valuation, witnessIndex, Fin.append_right]

def pair {n : Nat} (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) (i j : Fin n) : Matrix (Arity n) :=
  .conj (Matrix.literal (x i = x j) (.equal (witnessIndex n i) (witnessIndex n j)))
    (.conj (Matrix.literal (x i ≤ x j) (.lessEqual (witnessIndex n i) (witnessIndex n j)))
      (.conj (Matrix.literal (S₁ (x i) (x j)) (.first (witnessIndex n i) (witnessIndex n j)))
        (Matrix.literal (S₂ (x i) (x j)) (.second (witnessIndex n i) (witnessIndex n j)))))

theorem pair_realize {n : Nat} (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x p : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (i j : Fin n) :
    (pair S₁ S₂ x i j).realize S₁ S₂ (valuation p z w) ↔
      (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
      (S₁ (w i) (w j) ↔ S₁ (x i) (x j)) ∧ (S₂ (w i) (w j) ↔ S₂ (x i) (x j)) := by
  simp only [pair, Matrix.realize, literal_realize, witness_value]

def fixed {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0}) (i : Fin n) : Matrix (Arity n) :=
  if x i < α then .equal (parameterIndex n i) (witnessIndex n i)
  else .equal (witnessIndex n i) (witnessIndex n i)

theorem fixed_realize {n : Nat} (α : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (i : Fin n) :
    (fixed α x i).realize S₁ S₂ (valuation p z w) ↔ (x i < α → p i = w i) := by
  by_cases hi : x i < α <;>
    simp only [fixed, hi, ↓reduceIte, Matrix.realize, parameter_value, witness_value,
      true_implies, false_implies]

def aboveCut {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0}) (i : Fin n) : Matrix (Arity n) :=
  if α ≤ x i then .neg (.lessEqual (witnessIndex n i) (cutIndex n))
  else .equal (witnessIndex n i) (witnessIndex n i)

theorem aboveCut_realize {n : Nat} (α : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (i : Fin n) :
    (aboveCut α x i).realize S₁ S₂ (valuation p z w) ↔ (α ≤ x i → z 0 < w i) := by
  by_cases hi : α ≤ x i <;>
    simp only [aboveCut, hi, ↓reduceIte, Matrix.realize, cut_value, witness_value,
      not_le, true_implies, false_implies]

def diagram {n : Nat} (α : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0}) : Matrix (Arity n) :=
  Matrix.finiteConjunction (List.ofFn (fun i : Fin n =>
    Matrix.conj (fixed α x i) (Matrix.conj (aboveCut α x i)
      (Matrix.finiteConjunction (List.ofFn (fun j : Fin n => pair S₁ S₂ x i j))))))

theorem diagram_realize {n : Nat} (α : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x p : Fin n → Ordinal.{0})
    (z : Fin 1 → Ordinal.{0}) (w : Fin n → Ordinal.{0}) :
    (diagram α S₁ S₂ x).realize S₁ S₂ (valuation p z w) ↔
      ∀ i, (x i < α → p i = w i) ∧ (α ≤ x i → z 0 < w i) ∧ ∀ j,
        (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
        (S₁ (w i) (w j) ↔ S₁ (x i) (x j)) ∧ (S₂ (w i) (w j) ↔ S₂ (x i) (x j)) := by
  simp only [diagram, finiteConjunction_ofFn_realize, Matrix.realize,
    fixed_realize, aboveCut_realize, pair_realize]

end Alexander313.Wilken.PureRelations.CofinalCopies
