import Alexander313.SourceColumns

/-!
# Actual program columns for arbitrary numerical parameter instances

Freeze all free numerical variables except the chosen input by literal numeral
substitution, and feed that actual syntax to the already constructed uniform
instance compiler. No exact-singleton free-variable assumption is necessary.
The resulting column represents the original source predicate at every input,
even if the displayed input does not occur. The program index may depend on
all parameter values. No source soundness or filtered-column oracle is used.
All proof terms remain uncompiled.
-/

namespace Alexander313

def Formula.parameterInstance (φ : Formula Nat) (x : Nat) (s : Assignment) :
    Formula Nat := φ.subst (NumericalSubstitution.remove (fun v => some (s v)) x)

theorem Formula.parameterInstance_subst (φ : Formula Nat) (x n : Nat)
    (s : Assignment) :
    (φ.parameterInstance x s).subst (singleNumeralSubstitution x n) =
      φ.close (Function.update s x n) := by
  rw [parameterInstance, Formula.subst_compose]
  unfold Formula.close
  apply congrArg (fun σ => φ.subst σ)
  funext v
  by_cases hv : v = x
  · subst v
    simp [NumericalSubstitution.remove, NumericalSubstitution.compose,
      singleNumeralSubstitution]
  · simp [NumericalSubstitution.remove, NumericalSubstitution.compose,
      singleNumeralSubstitution, hv]

theorem Formula.parameterInstance_freeVars (φ : Formula Nat) (x : Nat)
    (s : Assignment) : (φ.parameterInstance x s).freeVars ⊆ {x} := by
  intro v hv
  have h := (Formula.mem_freeVars_subst φ _ v).mp hv
  by_cases hvx : v = x
  · simpa only [Finset.mem_singleton] using hvx
  · simp [NumericalSubstitution.remove, hvx] at h

noncomputable def MachineFamily.parameterColumnProgram (F : MachineFamily)
    (j : Nat) (φ : Formula Nat) (x : Nat) (s : Assignment) : Program :=
  unaryColumnCompiler (((F.effective.recognizes, j),
    (φ.parameterInstance x s).code id), x)

theorem MachineFamily.parameterColumnProgram_eval (F : MachineFamily)
    (j : Nat) (φ : Formula Nat) (x : Nat) (s : Assignment) (n : Nat) :
    (F.parameterColumnProgram j φ x s).eval n =
      F.effective.recognizes.eval (Nat.pair j
        ((φ.close (Function.update s x n)).code id)) := by
  rw [parameterColumnProgram, unaryColumnCompiler_eval, Formula.substCode_code,
    Formula.parameterInstance_subst]

noncomputable def MachineFamily.parameterColumnIndex (F : MachineFamily)
    (j : Nat) (φ : Formula Nat) (x : Nat) (s : Assignment) : Nat :=
  Encodable.encode (unaryColumnCompiler (((F.effective.recognizes, j),
    (φ.parameterInstance x s).code id), x))

theorem MachineFamily.parameterColumnIndex_encode (F : MachineFamily)
    (j : Nat) (φ : Formula Nat) (x : Nat) (s : Assignment) :
    F.parameterColumnIndex j φ x s =
      Encodable.encode (F.parameterColumnProgram j φ x s) := rfl

theorem MachineFamily.parameterColumn_equation (F : MachineFamily)
    (j : Nat) (φ : Formula Nat) (x : Nat) (s : Assignment) (n : Nat) :
    W (F.parameterColumnIndex j φ x s) n ↔
      F.effective.proves j (φ.close (Function.update s x n)) := by
  have hdecode : Nat.Partrec.Code.ofNatCode (F.parameterColumnIndex j φ x s) =
      unaryColumnCompiler (((F.effective.recognizes, j),
        (φ.parameterInstance x s).code id), x) := Denumerable.ofNat_encode
          (unaryColumnCompiler (((F.effective.recognizes, j),
            (φ.parameterInstance x s).code id), x))
  rw [W, hdecode, unaryColumnCompiler_eval, Formula.substCode_code,
    Formula.parameterInstance_subst]
  have hownerFunction : F.effective.encodeOwner = id := funext F.canonical_owners
  have hformula : F.effective.encodeFormula (φ.close (Function.update s x n)) =
      (φ.close (Function.update s x n)).code id := by
    rw [F.effective.formula_coding, hownerFunction]
  simpa only [F.canonical_owners j, hformula, Program.domain] using
    F.effective.recognizes_correct j (φ.close (Function.update s x n))

theorem Formula.close_update_fresh_before {Owner : Type} (φ : Formula Owner)
    (x e n c : Nat) (s : Assignment) (fresh : e ∉ φ.freeVars) :
    φ.close (Function.update (Function.update s e c) x n) =
      φ.close (Function.update s x n) := by
  apply φ.close_eq_of_agree
  intro v hv
  have hve : v ≠ e := fun h => fresh (h ▸ hv)
  by_cases hvx : v = x
  · subst v
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hvx, Function.update_of_ne hve]

end Alexander313
