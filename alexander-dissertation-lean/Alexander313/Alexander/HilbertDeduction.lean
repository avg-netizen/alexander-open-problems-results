import Alexander313.Alexander.FirstOrderCalculus

/-!
# Closed-sentence deduction and derived native Hilbert rules

All proofs use the existing `LogicalAxiom` and `Derivation` constructors.
Deduction discharges a closed sentence, so its generalization case has a proved
vacuous antecedent. The classical and existential rules below are derived;
they do not add a logical axiom or an Alexander modal substitution principle.
-/

namespace Alexander313.FirstOrderCalculus

universe u v w

variable {L : FirstOrder.Language.{u, v}}

private theorem empty_relabel_term_freeVar {d n : Nat}
    (g : Empty → Nat ⊕ Fin d) (t : L.Term (Empty ⊕ Fin n)) :
    (t.relabel (FirstOrder.Language.BoundedFormula.relabelAux g n)).varFinsetLeft = ∅ := by
  induction t with
  | var a =>
    cases a with
    | inl e => exact Empty.elim e
    | inr i => simp [FirstOrder.Language.BoundedFormula.relabelAux]
  | func f ts ih => simp [ih, Finset.ext_iff]

private theorem empty_relabel_formula_freeVar {d n : Nat}
    (g : Empty → Nat ⊕ Fin d) (φ : L.BoundedFormula Empty n) :
    (φ.relabel g).freeVarFinset = ∅ := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    simp [FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, empty_relabel_term_freeVar]
  | rel r ts =>
    simp [FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, empty_relabel_term_freeVar,
      Finset.ext_iff]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => rw [FirstOrder.Language.BoundedFormula.relabel_all]; exact ih

@[simp] theorem sentenceFormula_freeVarFinset (σ : L.Sentence) :
    (sentenceFormula σ).freeVarFinset = ∅ := by
  exact empty_relabel_formula_freeVar (Sum.inl ∘ Empty.elim) σ

@[simp] theorem sentenceFormula_imp (σ τ : L.Sentence) :
    sentenceFormula (σ.imp τ) = (sentenceFormula σ).imp (sentenceFormula τ) := rfl

@[simp] theorem sentenceFormula_not (σ : L.Sentence) :
    sentenceFormula σ.not = (sentenceFormula σ).not := rfl

@[simp] theorem sentenceFormula_falsum :
    sentenceFormula (⊥ : L.Sentence) = (⊥ : L.Formula Nat) := rfl

namespace Derivation

variable {T U : L.Theory} {φ ψ χ : L.Formula Nat}

/-- Replace each closed theory premise by its actual derivation. -/
theorem replaceTheory (h : Derivation U φ)
    (premises : ∀ σ ∈ U, Derivation T (sentenceFormula σ)) : Derivation T φ := by
  induction h with
  | logical h => exact .logical h
  | theory σ hσ => exact premises σ hσ
  | mp hp hq ihp ihq => exact .mp ihp ihq
  | generalize x h ih => exact .generalize x ih

theorem mono (h : Derivation T φ) (hTU : T ⊆ U) : Derivation U φ :=
  h.replaceTheory (fun σ hσ => .theory σ (hTU hσ))

theorem impRefl (φ : L.Formula Nat) : Derivation T (φ.imp φ) :=
  .mp (.mp (.logical (.s φ (φ.imp φ) φ)) (.logical (.k φ (φ.imp φ))))
    (.logical (.k φ φ))

theorem impOf (h : Derivation T φ) (ψ : L.Formula Nat) : Derivation T (ψ.imp φ) :=
  .mp (.logical (.k φ ψ)) h

theorem mpUnder (h : Derivation T (φ.imp (ψ.imp χ)))
    (k : Derivation T (φ.imp ψ)) : Derivation T (φ.imp χ) :=
  .mp (.mp (.logical (.s φ ψ χ)) h) k

theorem impTrans (h : Derivation T (φ.imp ψ)) (k : Derivation T (ψ.imp χ)) :
    Derivation T (φ.imp χ) := mpUnder (k.impOf φ) h

theorem impMonotone (h : Derivation T (φ.imp ψ)) (χ : L.Formula Nat) :
    Derivation T ((χ.imp φ).imp (χ.imp ψ)) :=
  .mp (.logical (.s χ φ ψ)) (h.impOf χ)

theorem explosion (φ : L.Formula Nat) : Derivation T ((⊥ : L.Formula Nat).imp φ) := by
  have ht : Derivation T ((⊥ : L.Formula Nat).not) := impRefl _
  exact .mp (.logical (.classical φ (⊥ : L.Formula Nat))) (ht.impOf φ.not)

theorem contrapositive (h : Derivation T (φ.imp ψ)) :
    Derivation T (ψ.not.imp φ.not) := by
  have hs : Derivation T
      ((φ.imp ψ.not).imp ((φ.imp ψ).imp φ.not)) := .logical (.s φ ψ ⊥)
  have hk : Derivation T (ψ.not.imp (φ.imp ψ.not)) := .logical (.k ψ.not φ)
  exact mpUnder (mpUnder (hs.impOf ψ.not) hk) (h.impOf ψ.not)

theorem doubleNegIntro (φ : L.Formula Nat) : Derivation T (φ.imp φ.not.not) := by
  have hs : Derivation T ((φ.not.imp φ).imp φ.not.not) :=
    .mp (.logical (.s φ.not φ ⊥)) (impRefl φ.not)
  exact mpUnder (hs.impOf φ) (.logical (.k φ φ.not))

theorem doubleNegElim (φ : L.Formula Nat) : Derivation T (φ.not.not.imp φ) := by
  let top : L.Formula Nat := (⊥ : L.Formula Nat).not
  have ht : Derivation T top := impRefl _
  have h₁ : Derivation T (φ.not.not.imp (φ.not.imp top.not)) :=
    impTrans (impRefl φ.not.not) ((explosion top.not).impMonotone φ.not)
  have h₂ : Derivation T (φ.not.not.imp (top.imp φ)) :=
    impTrans h₁ (.logical (.classical φ top))
  exact mpUnder h₂ (ht.impOf φ.not.not)

theorem ofDoubleNeg (h : Derivation T φ.not.not) : Derivation T φ :=
  .mp (doubleNegElim φ) h

/-- Generalization across an implication with an actually fresh antecedent. -/
theorem generalizeImp (x : Nat) (h : Derivation T (φ.imp ψ))
    (hx : x ∉ φ.freeVarFinset) : Derivation T (φ.imp (allVariable x ψ)) := by
  have hd : Derivation T ((allVariable x φ).imp (allVariable x ψ)) :=
    .mp (.logical (.allDist x φ ψ)) (.generalize x h)
  exact impTrans (.logical (.vacuous x φ hx)) hd

theorem allMonotone (x : Nat) (h : Derivation T (φ.imp ψ)) :
    Derivation T ((allVariable x φ).imp (allVariable x ψ)) :=
  .mp (.logical (.allDist x φ ψ)) (.generalize x h)

theorem specialize (x : Nat) (t : L.Term Nat) (h : Derivation T (allVariable x φ)) :
    Derivation T (substituteVariable x t φ) := .mp (.logical (.allElim x t φ)) h

theorem deduction {σ : L.Sentence} (h : Derivation (insert σ T) φ) :
    Derivation T ((sentenceFormula σ).imp φ) := by
  induction h with
  | logical h => exact (Derivation.logical (T := T) h).impOf _
  | theory τ hτ =>
    rcases Set.mem_insert_iff.mp hτ with rfl | hτ
    · exact impRefl _
    · exact (Derivation.theory τ hτ).impOf _
  | mp hp hq ihp ihq => exact mpUnder ihp ihq
  | generalize x h ih =>
    exact generalizeImp x ih (by simp)

theorem deduction_iff (σ : L.Sentence) (φ : L.Formula Nat) :
    Derivation (insert σ T) φ ↔ Derivation T ((sentenceFormula σ).imp φ) := by
  refine ⟨deduction, fun h => ?_⟩
  exact .mp (h.mono (Set.subset_insert σ T)) (.theory σ (Set.mem_insert σ T))

end Derivation

/-- Native first-order existential quantification over a named free variable. -/
def existsVariable (x : Nat) (φ : L.Formula Nat) : L.Formula Nat :=
  (allVariable x φ.not).not

theorem existsVariable_realize {D : Type w} [L.Structure D]
    (x : Nat) (φ : L.Formula Nat) (s : Nat → D) :
    (existsVariable x φ).Realize s ↔ ∃ d, φ.Realize (Function.update s x d) := by
  classical
  change (¬(allVariable x φ.not).Realize s) ↔ _
  rw [allVariable_realize]
  simp only [FirstOrder.Language.Formula.realize_not, not_forall, Classical.not_not]

@[simp] theorem substituteVariable_not (x : Nat) (t : L.Term Nat) (φ : L.Formula Nat) :
    substituteVariable x t φ.not = (substituteVariable x t φ).not := rfl

namespace Derivation

variable {T : L.Theory} {φ ψ : L.Formula Nat}

theorem existsIntro (x : Nat) (t : L.Term Nat) (φ : L.Formula Nat) :
    Derivation T ((substituteVariable x t φ).imp (existsVariable x φ)) := by
  have h : Derivation T ((allVariable x φ.not).imp (substituteVariable x t φ).not) := by
    simpa only [substituteVariable_not] using
      (Derivation.logical (LogicalAxiom.allElim x t φ.not) : Derivation T _)
  exact impTrans (doubleNegIntro _) h.contrapositive

theorem existsMonotone (x : Nat) (h : Derivation T (φ.imp ψ)) :
    Derivation T ((existsVariable x φ).imp (existsVariable x ψ)) :=
  (allMonotone x h.contrapositive).contrapositive

/-- Derived existential elimination with the genuine free-variable condition. -/
theorem existsElim (x : Nat) (h : Derivation T (φ.imp ψ))
    (hx : x ∉ ψ.freeVarFinset) : Derivation T ((existsVariable x φ).imp ψ) := by
  have hx' : x ∉ ψ.not.freeVarFinset := by
    simpa only [FirstOrder.Language.BoundedFormula.not,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty] using hx
  have h₁ := generalizeImp x h.contrapositive hx'
  exact impTrans h₁.contrapositive (doubleNegElim ψ)

end Derivation

/-- Syntactic consistency for the literal, unchanged native calculus. -/
def Consistent (T : L.Theory) : Prop := ¬Derivation T (⊥ : L.Formula Nat)

namespace Consistent

theorem mono {T U : L.Theory} (hU : Consistent U) (hTU : T ⊆ U) : Consistent T :=
  fun h => hU (h.mono hTU)

theorem insert_of_derivable {T : L.Theory} (hT : Consistent T) (σ : L.Sentence)
    (hσ : Derivation T (sentenceFormula σ)) : Consistent (insert σ T) := by
  intro hfalse
  apply hT
  exact hfalse.replaceTheory (fun τ hτ => by
    rcases Set.mem_insert_iff.mp hτ with rfl | hτ
    · exact hσ
    · exact .theory τ hτ)

end Consistent

theorem consistent_insert_iff (T : L.Theory) (σ : L.Sentence) :
    Consistent (insert σ T) ↔ ¬Derivation T (sentenceFormula σ.not) := by
  change (¬Derivation (insert σ T) (⊥ : L.Formula Nat)) ↔
    ¬Derivation T ((sentenceFormula σ).imp ⊥)
  exact not_congr (Derivation.deduction_iff σ ⊥)

/-- The negated conclusion can actually be added when it is not derivable. -/
theorem consistent_insert_not_iff (T : L.Theory) (σ : L.Sentence) :
    Consistent (insert σ.not T) ↔ ¬Derivation T (sentenceFormula σ) := by
  rw [consistent_insert_iff]
  simp only [sentenceFormula_not]
  constructor
  · intro h hσ
    exact h (.mp (Derivation.doubleNegIntro _) hσ)
  · intro h hσ
    exact h hσ.ofDoubleNeg

end Alexander313.FirstOrderCalculus
