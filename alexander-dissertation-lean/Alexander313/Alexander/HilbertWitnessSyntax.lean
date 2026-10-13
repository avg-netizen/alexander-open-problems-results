import Alexander313.Alexander.HilbertFreshConstants

/-!
# Literal substitution rollback for the fresh witness argument

Replacing the named variable `x` by a genuinely fresh `y`, then replacing
`y` by `x`, returns the original native formula. The proof works on actual
terms and bounded formulas, leaving every bound-context slot unchanged.
The two propositional projections below are derived from the existing
Hilbert axioms and are used to refute a negated witness implication.
-/

namespace Alexander313.FirstOrderCalculus

universe u v

variable {L : FirstOrder.Language.{u, v}}

namespace WitnessSyntax

private def variableSubstitution (x y : Nat) : Nat → L.Term Nat :=
  fun z => if z = x then .var y else .var z

private def liftedVariableSubstitution (x y : Nat) (n : Nat) :
    Nat ⊕ Fin n → L.Term (Nat ⊕ Fin n) :=
  Sum.elim (fun z => (variableSubstitution x y z).relabel Sum.inl)
    (fun i => .var (.inr i))

private theorem term_rollback (x y : Nat) {n : Nat}
    (t : L.Term (Nat ⊕ Fin n)) (hy : y ∉ t.varFinsetLeft) :
    (t.subst (liftedVariableSubstitution x y n)).subst
      (liftedVariableSubstitution y x n) = t := by
  revert hy
  induction t with
  | var z =>
    intro hy
    cases z with
    | inl z =>
      have hzy : z ≠ y := by
        intro h
        subst z
        exact hy (Finset.mem_singleton_self y)
      by_cases hzx : z = x <;>
        simp [variableSubstitution, liftedVariableSubstitution,
          FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
          hzx, hzy]
    | inr i => rfl
  | func f ts ih =>
    intro hy
    change FirstOrder.Language.Term.func f (fun i =>
      ((ts i).subst (liftedVariableSubstitution x y n)).subst
        (liftedVariableSubstitution y x n)) = .func f ts
    congr 1
    funext i
    apply ih i
    intro h
    exact hy (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)

theorem substituteVariable_rollback (x y : Nat) {n : Nat}
    (φ : L.BoundedFormula Nat n) (hy : y ∉ φ.freeVarFinset) :
    (φ.subst (variableSubstitution x y)).subst
      (variableSubstitution y x) = φ := by
  revert hy
  induction φ with
  | falsum => intro _; rfl
  | equal t s =>
    intro hy
    have ht : y ∉ t.varFinsetLeft := fun h => hy (Finset.mem_union_left _ h)
    have hs : y ∉ s.varFinsetLeft := fun h => hy (Finset.mem_union_right _ h)
    change FirstOrder.Language.BoundedFormula.equal
      ((t.subst (liftedVariableSubstitution x y _)).subst
        (liftedVariableSubstitution y x _))
      ((s.subst (liftedVariableSubstitution x y _)).subst
        (liftedVariableSubstitution y x _)) = FirstOrder.Language.BoundedFormula.equal t s
    rw [term_rollback x y t ht, term_rollback x y s hs]
  | rel r ts =>
    intro hy
    change FirstOrder.Language.BoundedFormula.rel r (fun i =>
      ((ts i).subst (liftedVariableSubstitution x y _)).subst
        (liftedVariableSubstitution y x _)) = .rel r ts
    congr 1
    funext i
    apply term_rollback
    intro h
    exact hy (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
  | imp φ ψ ihφ ihψ =>
    intro hy
    have hφ : y ∉ φ.freeVarFinset := fun h => hy (Finset.mem_union_left _ h)
    have hψ : y ∉ ψ.freeVarFinset := fun h => hy (Finset.mem_union_right _ h)
    change (((φ.subst (variableSubstitution x y)).subst (variableSubstitution y x)).imp
      ((ψ.subst (variableSubstitution x y)).subst (variableSubstitution y x))) = φ.imp ψ
    rw [ihφ hφ, ihψ hψ]
  | all φ ih =>
    intro hy
    exact congrArg FirstOrder.Language.BoundedFormula.all (ih hy)

theorem rollback (x y : Nat) (φ : L.Formula Nat)
    (hy : y ∉ φ.freeVarFinset) :
    substituteVariable y (.var x) (substituteVariable x (.var y) φ) = φ :=
  substituteVariable_rollback x y φ hy

end WitnessSyntax

namespace Derivation

variable {T : L.Theory} {φ ψ : L.Formula Nat}

theorem ofNotImp_left (h : Derivation T (φ.imp ψ).not) : Derivation T φ :=
  (Derivation.mp ((Derivation.explosion ψ).impMonotone φ).contrapositive h).ofDoubleNeg

theorem ofNotImp_right (h : Derivation T (φ.imp ψ).not) : Derivation T ψ.not :=
  Derivation.mp (Derivation.logical (LogicalAxiom.k ψ φ)).contrapositive h

end Derivation

end Alexander313.FirstOrderCalculus
