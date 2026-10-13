import Alexander313.Alexander.NativeFormulaOperations

/-!
# Literal naturality of the Alexander Δ translation

Native relabeling extends an existing bound context by a prefix. Alexander's
quantifiers append the newest bound level. The two actions commute, including
shadowed variable names. Consequently Δ can be formed from already translated
children using the actual native `allVariable` operation, with no changing
environment parameter in a primitive-recursion proof.
-/

namespace Alexander313.Delta

theorem term_relabel {Owner : Type} {d k : Nat}
    (ρ : Nat → Nat ⊕ Fin d) (σ : Nat → Nat ⊕ Fin k) (t : Term) :
    term (Owner := Owner)
      (FirstOrder.Language.BoundedFormula.relabelAux ρ k ∘ σ) t =
      (term σ t).relabel (FirstOrder.Language.BoundedFormula.relabelAux ρ k) := by
  induction t <;> simp_all [term, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.Functions.apply₁, FirstOrder.Language.Functions.apply₂,
    Function.comp_def] <;> funext i <;> fin_cases i <;> rfl

theorem bind_relabelAux {d k : Nat} (ρ : Nat → Nat ⊕ Fin d)
    (σ : Nat → Nat ⊕ Fin k) (x : Nat) :
    bind (FirstOrder.Language.BoundedFormula.relabelAux ρ k ∘ σ) x =
      FirstOrder.Language.BoundedFormula.relabelAux ρ (k + 1) ∘ bind σ x := by
  funext z
  by_cases hzx : z = x
  · subst z
    simp [bind, FirstOrder.Language.BoundedFormula.relabelAux, Function.comp_def,
      Fin.ext_iff]
  · cases hs : σ z with
    | inl y =>
      cases hr : ρ y <;> simp [bind, FirstOrder.Language.BoundedFormula.relabelAux,
        Function.comp_def, hzx, hs, hr, Fin.ext_iff]
    | inr i =>
      simp [bind, FirstOrder.Language.BoundedFormula.relabelAux,
        Function.comp_def, hzx, hs, Fin.ext_iff]

theorem formulaAux_relabel {Owner : Type} {d k : Nat}
    (ρ : Nat → Nat ⊕ Fin d) (σ : Nat → Nat ⊕ Fin k) (φ : Formula Owner) :
    formulaAux (FirstOrder.Language.BoundedFormula.relabelAux ρ k ∘ σ) φ =
      (formulaAux σ φ).relabel ρ := by
  induction φ generalizing k σ with
  | falsum => rfl
  | equal t u =>
    simp [formulaAux, FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, term_relabel]
  | imp φ ψ ihφ ihψ =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.relabel_imp, ihφ, ihψ]
  | conj φ ψ ihφ ihψ =>
    change ((formulaAux _ φ).imp (formulaAux _ ψ).not).not =
      (((formulaAux σ φ).imp (formulaAux σ ψ).not).not).relabel ρ
    simp only [FirstOrder.Language.BoundedFormula.relabel_not,
      FirstOrder.Language.BoundedFormula.relabel_imp, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    change (formulaAux _ φ).not.imp (formulaAux _ ψ) =
      ((formulaAux σ φ).not.imp (formulaAux σ ψ)).relabel ρ
    simp only [FirstOrder.Language.BoundedFormula.relabel_not,
      FirstOrder.Language.BoundedFormula.relabel_imp, ihφ, ihψ]
  | neg φ ih =>
    simp only [formulaAux, FirstOrder.Language.BoundedFormula.relabel_not, ih]
  | all x φ ih =>
    simpa only [formulaAux, FirstOrder.Language.BoundedFormula.relabel_all,
      bind_relabelAux] using
      congrArg FirstOrder.Language.BoundedFormula.all (ih (bind σ x))
  | ex x φ ih =>
    simpa only [formulaAux, FirstOrder.Language.BoundedFormula.relabel_ex,
      bind_relabelAux] using
      congrArg FirstOrder.Language.BoundedFormula.ex (ih (bind σ x))
  | know a φ ih =>
    simp [formulaAux, FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.Term.relabel, Function.comp_def]

theorem formulaAux_eq_relabel {Owner : Type} {n : Nat}
    (ρ : Nat → Nat ⊕ Fin n) (φ : Formula Owner) :
    formulaAux ρ φ = FirstOrder.Language.BoundedFormula.relabel ρ (formula φ) := by
  have hρ : FirstOrder.Language.BoundedFormula.relabelAux ρ 0 ∘ Sum.inl = ρ := by
    funext x
    cases h : ρ x <;> simp [FirstOrder.Language.BoundedFormula.relabelAux,
      Function.comp_def, h, Fin.ext_iff] <;> rfl
  simpa only [hρ, formula] using formulaAux_relabel (k := 0) ρ Sum.inl φ

private theorem bind_sumInl (x : Nat) : bind (n := 0) Sum.inl x = FirstOrderCalculus.bindVariable x := by
  funext y
  by_cases h : y = x <;> simp [bind, FirstOrderCalculus.bindVariable, h]

@[simp] theorem formula_all {Owner : Type} (x : Nat) (φ : Formula Owner) :
    formula (.all x φ) = FirstOrderCalculus.allVariable x (formula φ) := by
  change (formulaAux (bind Sum.inl x) φ).all =
    (FirstOrder.Language.BoundedFormula.relabel (FirstOrderCalculus.bindVariable x) (formula φ)).all
  rw [bind_sumInl, formulaAux_eq_relabel]

@[simp] theorem formula_ex {Owner : Type} (x : Nat) (φ : Formula Owner) :
    formula (.ex x φ) = (FirstOrderCalculus.allVariable x (formula φ).not).not := by
  change (formulaAux (bind Sum.inl x) φ).ex = _
  rw [bind_sumInl, formulaAux_eq_relabel]
  simp only [FirstOrder.Language.BoundedFormula.ex, FirstOrderCalculus.allVariable,
    FirstOrder.Language.BoundedFormula.relabel_not]

end Alexander313.Delta
