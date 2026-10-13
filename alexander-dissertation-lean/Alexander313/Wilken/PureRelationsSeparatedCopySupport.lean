import Alexander313.Wilken.PureRelationsFiniteDiagrams

/-!
# Literal Sigma2 matrices for separated copies with endpoint links

The finite parameter tuple contains every original point already below the
lower endpoint and one prescribed cutoff. The existential tuple is the
whole copied finite pattern. A single universal ordinal tests all designated
R1 connections. No finite-copy map or endpoint-connection oracle is supplied.
This source-only draft remains outside the package during its checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SeparatedCopies

abbrev Arity (n : Nat) := ((n + 1) + n) + 1

def parameterIndex (n : Nat) (i : Fin n) : Fin (Arity n) :=
  Fin.castAdd 1 (Fin.castAdd n (Fin.castAdd 1 i))

def cutIndex (n : Nat) : Fin (Arity n) :=
  Fin.castAdd 1 (Fin.castAdd n (Fin.natAdd n (0 : Fin 1)))

def witnessIndex (n : Nat) (i : Fin n) : Fin (Arity n) :=
  Fin.castAdd 1 (Fin.natAdd (n + 1) i)

def universalIndex (n : Nat) : Fin (Arity n) :=
  Fin.natAdd ((n + 1) + n) (0 : Fin 1)

def valuation {n : Nat} (p : Fin (n + 1) → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) : Fin (Arity n) → Ordinal.{0} :=
  Fin.append (Fin.append p w) z

theorem parameter_value {n : Nat} (p : Fin (n + 1) → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) (i : Fin n) :
    valuation p w z (parameterIndex n i) = p (Fin.castAdd 1 i) := by
  simp only [valuation, parameterIndex, Fin.append_left]

theorem cut_value {n : Nat} (p : Fin (n + 1) → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) :
    valuation p w z (cutIndex n) = p (Fin.natAdd n (0 : Fin 1)) := by
  simp only [valuation, cutIndex, Fin.append_left]

theorem witness_value {n : Nat} (p : Fin (n + 1) → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) (i : Fin n) :
    valuation p w z (witnessIndex n i) = w i := by
  simp only [valuation, witnessIndex, Fin.append_left, Fin.append_right]

theorem universal_value {n : Nat} (p : Fin (n + 1) → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) :
    valuation p w z (universalIndex n) = z 0 := by
  simp only [valuation, universalIndex, Fin.append_right]

def pair {n : Nat} (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) (i j : Fin n) : Matrix (Arity n) :=
  .conj (Matrix.literal (x i = x j) (.equal (witnessIndex n i) (witnessIndex n j)))
    (.conj (Matrix.literal (x i ≤ x j) (.lessEqual (witnessIndex n i) (witnessIndex n j)))
      (.conj (Matrix.literal (S₁ (x i) (x j)) (.first (witnessIndex n i) (witnessIndex n j)))
        (Matrix.literal (S₂ (x i) (x j)) (.second (witnessIndex n i) (witnessIndex n j)))))

theorem pair_realize {n : Nat} (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) (p : Fin (n + 1) → Ordinal.{0})
    (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) (i j : Fin n) :
    (pair S₁ S₂ x i j).realize S₁ S₂ (valuation p w z) ↔
      (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
      (S₁ (w i) (w j) ↔ S₁ (x i) (x j)) ∧ (S₂ (w i) (w j) ↔ S₂ (x i) (x j)) := by
  simp only [pair, Matrix.realize, literal_realize, witness_value]

def fixed {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0}) (i : Fin n) : Matrix (Arity n) :=
  if x i < α then .equal (parameterIndex n i) (witnessIndex n i)
  else .equal (witnessIndex n i) (witnessIndex n i)

theorem fixed_realize {n : Nat} (α : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0})
    (p : Fin (n + 1) → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) (i : Fin n) :
    (fixed α x i).realize S₁ S₂ (valuation p w z) ↔
      (x i < α → p (Fin.castAdd 1 i) = w i) := by
  by_cases hi : x i < α <;>
    simp only [fixed, hi, ↓reduceIte, Matrix.realize, parameter_value, witness_value,
      true_implies, false_implies]

def aboveCut {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0}) (i : Fin n) : Matrix (Arity n) :=
  if α ≤ x i then .neg (.lessEqual (witnessIndex n i) (cutIndex n))
  else .equal (witnessIndex n i) (witnessIndex n i)

theorem aboveCut_realize {n : Nat} (α : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0})
    (p : Fin (n + 1) → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) (i : Fin n) :
    (aboveCut α x i).realize S₁ S₂ (valuation p w z) ↔
      (α ≤ x i → p (Fin.natAdd n (0 : Fin 1)) < w i) := by
  by_cases hi : α ≤ x i <;>
    simp only [aboveCut, hi, ↓reduceIte, Matrix.realize, cut_value, witness_value,
      not_le, true_implies, false_implies]

def linked {n : Nat} (β : Ordinal.{0}) (x : Fin n → Ordinal.{0}) (i : Fin n) : Matrix (Arity n) :=
  @ite (Matrix (Arity n)) (R1 (x i) β) (Classical.propDecidable (R1 (x i) β))
    (.disj (.neg (.lessEqual (witnessIndex n i) (universalIndex n)))
      (.first (witnessIndex n i) (universalIndex n)))
    (.equal (universalIndex n) (universalIndex n))

theorem linked_realize {n : Nat} (β : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0})
    (p : Fin (n + 1) → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) (i : Fin n) :
    (linked β x i).realize S₁ S₂ (valuation p w z) ↔
      (R1 (x i) β → w i ≤ z 0 → S₁ (w i) (z 0)) := by
  by_cases hi : R1 (x i) β
  · simp only [linked, hi, ↓reduceIte, Matrix.realize, witness_value, universal_value,
      true_implies]
    constructor
    · rintro (h | h) hle
      · exact False.elim (h hle)
      · exact h
    · intro h
      by_cases hle : w i ≤ z 0
      · exact Or.inr (h hle)
      · exact Or.inl hle
  · simp only [linked, hi, ↓reduceIte, Matrix.realize, universal_value, false_implies]

def diagram {n : Nat} (α β : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0}) : Matrix (Arity n) :=
  Matrix.finiteConjunction (List.ofFn (fun i : Fin n =>
    Matrix.conj (fixed α x i) (Matrix.conj (aboveCut α x i)
      (Matrix.conj (linked β x i)
        (Matrix.finiteConjunction (List.ofFn (fun j : Fin n => pair S₁ S₂ x i j)))))))

theorem diagram_realize {n : Nat} (α β : Ordinal.{0})
    (S₁ S₂ : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0})
    (p : Fin (n + 1) → Ordinal.{0}) (w : Fin n → Ordinal.{0}) (z : Fin 1 → Ordinal.{0}) :
    (diagram α β S₁ S₂ x).realize S₁ S₂ (valuation p w z) ↔
      ∀ i, (x i < α → p (Fin.castAdd 1 i) = w i) ∧
        (α ≤ x i → p (Fin.natAdd n (0 : Fin 1)) < w i) ∧
        (R1 (x i) β → w i ≤ z 0 → S₁ (w i) (z 0)) ∧ ∀ j,
          (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
          (S₁ (w i) (w j) ↔ S₁ (x i) (x j)) ∧ (S₂ (w i) (w j) ↔ S₂ (x i) (x j)) := by
  simp only [diagram, finiteConjunction_ofFn_realize, Matrix.realize,
    fixed_realize, aboveCut_realize, linked_realize, pair_realize]

def parameters {n : Nat} (α c : Ordinal.{0}) (x : Fin n → Ordinal.{0}) : Fin (n + 1) → Ordinal.{0} :=
  Fin.append (diagramParameters α x) (fun _ : Fin 1 => c)

theorem parameters_below {n : Nat} (α c : Ordinal.{0}) (hα : 0 < α) (hc : c < α)
    (x : Fin n → Ordinal.{0}) : TupleBelow α (parameters α c x) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [parameters, Fin.append_left] using diagramParameters_below α hα x j
  · simpa only [parameters, Fin.append_right] using hc

theorem parameters_original {n : Nat} (α c : Ordinal.{0}) (x : Fin n → Ordinal.{0})
    (i : Fin n) (hi : x i < α) : parameters α c x (Fin.castAdd 1 i) = x i := by
  simp only [parameters, Fin.append_left, diagramParameters, hi, ↓reduceIte]

theorem parameters_cut {n : Nat} (α c : Ordinal.{0}) (x : Fin n → Ordinal.{0}) :
    parameters α c x (Fin.natAdd n (0 : Fin 1)) = c := by
  simp only [parameters, Fin.append_right]

end Alexander313.Wilken.PureRelations.SeparatedCopies
