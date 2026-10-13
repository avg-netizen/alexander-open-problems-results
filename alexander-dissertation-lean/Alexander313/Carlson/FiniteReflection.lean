import Alexander313.Carlson.FinitePatterns
import Alexander313.Carlson.Downward
import Alexander313.Carlson.Upward

/-!
# Executable finite reflection

Downward and upward reflection are Boolean table constructions on a fixed
finite ambient order. Their interpretations are exactly the existing
propositional constructions. The finite hypothesis checkers decide all fields
of `DownData` and `UpData`, including the placement and matching conditions.

The table constructors and checkers use only computable decisions. In
particular, downward reflection uses a finite back map rather than evaluating
the classical back map in the original propositional definition.
-/

namespace Alexander313.Carlson

namespace Str

variable {α : Type*} [LinearOrder α] [Fintype α]

set_option synthInstance.maxSize 2048 in
/-- All hypotheses of downward reflection can be decided on a finite ambient
order with decidable relations. -/
instance instDecidableDownData (P : Str α) [DecidableRel P.r₁] [DecidableRel P.r₂]
    (k : Lvl) (a b : α) (X N : Finset α) (g : α → α) :
    Decidable (DownData P k a b X N g) := by
  refine decidable_of_iff
    (P.IsPattern ∧ a ∈ P.U ∧ b ∈ P.U ∧ a < b ∧ P.rel k a b ∧
      (∀ x ∈ X, x ∈ P.U ∧ a ≤ x ∧ x < b) ∧ X.Nonempty ∧
      (∀ n ∈ N, n ∉ P.U) ∧ (∀ n ∈ N, n < a) ∧
      (∀ n ∈ N, ∀ q ∈ P.U, q < a → q < n) ∧ N.image g = X ∧
      (∀ x ∈ N, ∀ y ∈ N, x < y → g x < g y)) ?_
  constructor
  · rintro ⟨pat, ha, hb, hab, hrel, hX, hXne, hNP, hNa, hNL, himage, hmono⟩
    exact ⟨pat, ha, hb, hab, hrel, hX, hXne, hNP, hNa, hNL, himage, hmono⟩
  · intro D
    exact ⟨D.pat, D.ha, D.hb, D.hab, D.hrel, D.hX, D.hXne, D.hNP, D.hNa,
      D.hNL, D.himage, D.hmono⟩

set_option synthInstance.maxSize 2048 in
/-- All hypotheses of upward reflection can be decided on a finite ambient
order with decidable relations. -/
instance instDecidableUpData (P Q : Str α)
    [DecidableRel P.r₁] [DecidableRel P.r₂]
    [DecidableRel Q.r₁] [DecidableRel Q.r₂]
    (a b : α) (N : Finset α) (g : α → α) :
    Decidable (UpData P Q a b N g) := by
  refine decidable_of_iff
    (Q.IsPattern ∧ Continuous P Q ∧ ExtensionAt P Q a ∧ b ∈ P.U ∧ a < b ∧
      P.r₂ a b ∧ (∀ n ∈ N, n ∉ P.U) ∧ (∀ n ∈ N, n < b) ∧
      (∀ n ∈ N, ∀ x ∈ P.U, x < b → x < n) ∧ N.image g = Q.U \ P.U ∧
      (∀ x ∈ N, ∀ y ∈ N, x < y → g x < g y)) ?_
  constructor
  · rintro ⟨pat, cont, ext, hb, hab, hrel, hNP, hNb, hNL, himage, hmono⟩
    exact ⟨pat, cont, ext, hb, hab, hrel, hNP, hNb, hNL, himage, hmono⟩
  · intro D
    exact ⟨D.pat, D.cont, D.ext, D.hb, D.hab, D.hrel, D.hNP, D.hNb,
      D.hNL, D.himage, D.hmono⟩

end Str

namespace Finite

variable {n : ℕ}

/-- Send new finite points to their originals and fix all other points. -/
def finiteBack (N : Finset (Fin n)) (g : Fin n → Fin n) (z : Fin n) : Fin n :=
  if z ∈ N then g z else z

/-- The executable back map agrees with the original propositional one. -/
@[simp] theorem finiteBack_eq_back (N : Finset (Fin n)) (g : Fin n → Fin n)
    (z : Fin n) : finiteBack N g z = Str.back N g z := by
  by_cases hz : z ∈ N
  · simp [finiteBack, Str.back, hz]
  · simp [finiteBack, Str.back, hz]

namespace PatternCode

/-- Boolean tables for downward reflection on the fixed finite order. -/
def downward (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) : PatternCode n where
  U := P.U ∪ N
  r₁ u v := decide <|
    (u ∈ P.U ∧ v ∈ P.U ∧ P.r₁ u v = true) ∨
    ((u ∈ N ∨ v ∈ N) ∧ (u ∈ N ∨ u < a) ∧ (v ∈ N ∨ v < a) ∧
      P.r₁ (finiteBack N g u) (finiteBack N g v) = true) ∨
    (k = .two ∧ u ∈ N ∧ v ∈ P.U ∧ a ≤ v ∧ P.r₁ (g u) b = true ∧ P.r₁ a v = true)
  r₂ u v := decide <|
    (u ∈ P.U ∧ v ∈ P.U ∧ P.r₂ u v = true) ∨
    ((u ∈ N ∨ v ∈ N) ∧ (u ∈ N ∨ u < a) ∧ (v ∈ N ∨ v < a) ∧
      P.r₂ (finiteBack N g u) (finiteBack N g v) = true)

/-- Interpreting the finite downward tables gives exactly the established
downward reflection construction, without any hypotheses on the input. -/
@[simp] theorem toStr_downward (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    (P.downward k a b N g).toStr = P.toStr.downward k a b N g := by
  simp only [toStr, downward, Str.downward, decide_eq_true_eq, finiteBack_eq_back]

/-- Boolean tables for upward reflection on the fixed finite order. -/
def upward (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) : PatternCode n where
  U := P.U ∪ N
  r₁ u v := decide <|
    (u ∈ P.U ∧ v ∈ P.U ∧ P.r₁ u v = true) ∨
    (u ∈ P.U ∧ v ∈ N ∧ u < b ∧ P.r₁ u b = true) ∨
    (u ∈ N ∧ v ∈ N ∧ Q.r₁ (g u) (g v) = true)
  r₂ u v := decide <|
    (u ∈ P.U ∧ v ∈ P.U ∧ P.r₂ u v = true) ∨
    (u ∈ P.U ∧ u < a ∧ v ∈ N ∧ Q.r₂ u (g v) = true) ∨
    (u ∈ N ∧ v ∈ N ∧ Q.r₂ (g u) (g v) = true)

/-- Interpreting the finite upward tables gives exactly the established
upward reflection construction, without any hypotheses on the input. -/
@[simp] theorem toStr_upward (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    (P.upward Q a b N g).toStr = P.toStr.upward Q.toStr a b N g := by
  simp only [toStr, upward, Str.upward, decide_eq_true_eq]

/-- Check the full downward-reflection hypotheses for the supplied copy. -/
def checkDownward (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (X N : Finset (Fin n)) (g : Fin n → Fin n) : Bool :=
  decide (Str.DownData P.toStr k a b X N g)

/-- The downward checker accepts exactly the original `DownData` predicate. -/
@[simp] theorem checkDownward_iff (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    P.checkDownward k a b X N g = true ↔ Str.DownData P.toStr k a b X N g := by
  simp only [checkDownward, decide_eq_true_eq]

theorem checkDownward_eq_true (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    P.checkDownward k a b X N g = true ↔ Str.DownData P.toStr k a b X N g :=
  checkDownward_iff P k a b X N g

/-- Check the full upward-reflection hypotheses for the supplied copy. -/
def checkUpward (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) : Bool :=
  decide (Str.UpData P.toStr Q.toStr a b N g)

/-- The upward checker accepts exactly the original `UpData` predicate. -/
@[simp] theorem checkUpward_iff (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    P.checkUpward Q a b N g = true ↔ Str.UpData P.toStr Q.toStr a b N g := by
  simp only [checkUpward, decide_eq_true_eq]

theorem checkUpward_eq_true (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    P.checkUpward Q a b N g = true ↔ Str.UpData P.toStr Q.toStr a b N g :=
  checkUpward_iff P Q a b N g

/-- An accepted downward step produces a genuine finite pattern. -/
theorem downward_isPattern_of_check (P : PatternCode n) (k : Lvl) (a b : Fin n)
    (X N : Finset (Fin n)) (g : Fin n → Fin n)
    (h : P.checkDownward k a b X N g = true) :
    (P.downward k a b N g).toStr.IsPattern := by
  rw [toStr_downward]
  exact ((checkDownward_iff P k a b X N g).mp h).isPattern

/-- An accepted upward step produces a genuine finite pattern. -/
theorem upward_isPattern_of_check (P Q : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n)
    (h : P.checkUpward Q a b N g = true) :
    (P.upward Q a b N g).toStr.IsPattern := by
  rw [toStr_upward]
  exact ((checkUpward_iff P Q a b N g).mp h).isPattern

end PatternCode
end Finite
end Alexander313.Carlson
