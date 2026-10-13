import Alexander313.Alexander.VariableOpening
import Alexander313.Alexander.RawAdmissibility
import Mathlib.Data.Set.Finite.Basic

/-!
# Alphabetic invariance of truth and finite consequence

The quantifier step renames its two compared binders to one fresh variable.
The fresh-variable opening identity comes from `VariableOpening`; semantic
invariance uses only the weak variable-substitution law and free independence.
The logical-size induction permits these variable instances as recursive
arguments. This establishes alphabetic closure of actual consequence
predicates, so their actual and filtered realizations are constructed rather
than accepted as model inputs.
-/

namespace Alexander313

theorem generalTruth_substVar_fresh {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (x z : Nat) (s : Nat → D) (d : D)
    (hfree : z ∉ φ.freeVars) (hbound : z ∉ φ.boundVars) :
    generalTruth M (φ.substVar x z) (Function.update s z d) ↔
      generalTruth M φ (Function.update s x d) := by
  have hs := generalTruth_substVar M φ x z (Function.update s z d)
    (φ.varSubstitutable_of_notMem_boundVars x z hbound)
  simp only [Function.update_self] at hs
  apply hs.trans
  apply generalTruth_eq_of_agree
  intro v hv
  have hvz : v ≠ z := fun h => hfree (h ▸ hv)
  by_cases hvx : v = x <;> simp [hvx, hvz]

theorem generalTruth_alpha {Owner D : Type} (M : ModalModel Owner D)
    (φ ψ : Formula Owner) (hα : φ.AlphaEquivalent ψ) (s : Nat → D) :
    generalTruth M φ s ↔ generalTruth M ψ s := by
  have main : ∀ k : Nat, ∀ φ ψ : Formula Owner, φ.logicalSize = k →
      φ.AlphaEquivalent ψ → ∀ s : Nat → D, (generalTruth M φ s ↔ generalTruth M ψ s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro φ ψ hk hα s
      cases φ with
      | falsum =>
        cases ψ <;> simp_all [Formula.AlphaEquivalent, Formula.alpha, generalTruth]
      | equal t u =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i v w
        have ht := Term.alpha_nil_injective hα.1
        have hu := Term.alpha_nil_injective hα.2
        subst v
        subst w
        rfl
      | imp φ χ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ η
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hχk : χ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have htφ := ih φ.logicalSize hφk φ ψ rfl hα.1 s
        have htχ := ih χ.logicalSize hχk χ η rfl hα.2 s
        simp only [generalTruth, htφ, htχ]
      | conj φ χ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ η
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hχk : χ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        exact and_congr (ih φ.logicalSize hφk φ ψ rfl hα.1 s)
          (ih χ.logicalSize hχk χ η rfl hα.2 s)
      | disj φ χ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ η
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hχk : χ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        exact or_congr (ih φ.logicalSize hφk φ ψ rfl hα.1 s)
          (ih χ.logicalSize hχk χ η rfl hα.2 s)
      | neg φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        exact not_congr (ih φ.logicalSize hφk φ ψ rfl hα s)
      | know a φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i b ψ
        obtain ⟨hab, hα⟩ := hα
        subst b
        exact M.alphabetic a φ ψ s hα
      | all x φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i y ψ
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        obtain ⟨z, hz⟩ := ((φ.freeVars ∪ φ.boundVars) ∪ (ψ.freeVars ∪ ψ.boundVars)).exists_notMem
        have hfφ : z ∉ φ.freeVars := fun h => hz
          (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hbφ : z ∉ φ.boundVars := fun h => hz
          (Finset.mem_union_left _ (Finset.mem_union_right _ h))
        have hfψ : z ∉ ψ.freeVars := fun h => hz
          (Finset.mem_union_right _ (Finset.mem_union_left _ h))
        have hbψ : z ∉ ψ.boundVars := fun h => hz
          (Finset.mem_union_right _ (Finset.mem_union_right _ h))
        have hn : (φ.substVar x z).AlphaEquivalent (ψ.substVar y z) := by
          unfold Formula.AlphaEquivalent
          rw [φ.alpha_substVar_fresh x z hbφ, ψ.alpha_substVar_fresh y z hbψ]
          exact congrArg (AlphaFormula.openVariable 0 z) hα
        apply forall_congr'
        intro d
        have ht := ih φ.logicalSize hφk (φ.substVar x z) (ψ.substVar y z)
          (φ.logicalSize_substVar x z) hn (Function.update s z d)
        exact (generalTruth_substVar_fresh M φ x z s d hfφ hbφ).symm.trans
          (ht.trans (generalTruth_substVar_fresh M ψ y z s d hfψ hbψ))
      | ex x φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i y ψ
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        obtain ⟨z, hz⟩ := ((φ.freeVars ∪ φ.boundVars) ∪ (ψ.freeVars ∪ ψ.boundVars)).exists_notMem
        have hfφ : z ∉ φ.freeVars := fun h => hz
          (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hbφ : z ∉ φ.boundVars := fun h => hz
          (Finset.mem_union_left _ (Finset.mem_union_right _ h))
        have hfψ : z ∉ ψ.freeVars := fun h => hz
          (Finset.mem_union_right _ (Finset.mem_union_left _ h))
        have hbψ : z ∉ ψ.boundVars := fun h => hz
          (Finset.mem_union_right _ (Finset.mem_union_right _ h))
        have hn : (φ.substVar x z).AlphaEquivalent (ψ.substVar y z) := by
          unfold Formula.AlphaEquivalent
          rw [φ.alpha_substVar_fresh x z hbφ, ψ.alpha_substVar_fresh y z hbψ]
          exact congrArg (AlphaFormula.openVariable 0 z) hα
        apply exists_congr
        intro d
        have ht := ih φ.logicalSize hφk (φ.substVar x z) (ψ.substVar y z)
          (φ.logicalSize_substVar x z) hn (Function.update s z d)
        exact (generalTruth_substVar_fresh M φ x z s d hfφ hbφ).symm.trans
          (ht.trans (generalTruth_substVar_fresh M ψ y z s d hfψ hbψ))
  exact main φ.logicalSize φ ψ rfl hα s

theorem Formula.AlphaEquivalent.symm {Owner : Type} {φ ψ : Formula Owner}
    (h : φ.AlphaEquivalent ψ) : ψ.AlphaEquivalent φ := Eq.symm h

theorem Formula.AlphaEquivalent.chain {Owner : Type} {φ ψ : Formula Owner}
    (h : φ.AlphaEquivalent ψ) (Γ : List (Formula Owner)) :
    (Formula.chain Γ φ).AlphaEquivalent (Formula.chain Γ ψ) := by
  induction Γ with
  | nil => exact h
  | cons θ Γ ih =>
    change AlphaFormula.imp (θ.alpha []) ((Formula.chain Γ φ).alpha []) =
      AlphaFormula.imp (θ.alpha []) ((Formula.chain Γ ψ).alpha [])
    exact congrArg (AlphaFormula.imp (θ.alpha [])) ih

theorem Valid.alpha {Owner : Type} {φ ψ : Formula Owner} (hφ : Valid φ)
    (hα : φ.AlphaEquivalent ψ) : Valid ψ := by
  intro D hD M s
  exact (generalTruth_alpha M φ ψ hα s).mp (hφ D hD M s)

def Certificate.alpha {Owner : Type} {axioms : Formula Owner → Prop}
    {φ ψ : Formula Owner} (c : Certificate axioms φ) (hα : φ.AlphaEquivalent ψ) :
    Certificate axioms ψ where
  premises := c.premises
  admitted := c.admitted
  validity := c.validity.alpha (hα.chain c.premises)

theorem Provable.alpha {Owner : Type} {axioms : Formula Owner → Prop}
    {φ ψ : Formula Owner} (h : Provable axioms φ) (hα : φ.AlphaEquivalent ψ) :
    Provable axioms ψ := by
  obtain ⟨c⟩ := h
  exact ⟨c.alpha hα⟩

theorem consequence_rawAlphabetic {Owner : Type}
    (axioms : Owner → Formula Owner → Prop) :
    RawAlphabetic (fun a φ => Provable (axioms a) φ) := by
  intro a φ ψ _ _ hα
  exact ⟨fun h => h.alpha hα, fun h => h.alpha hα.symm⟩

def ActualRealization.consequence {Owner : Type} (axioms : Owner → Formula Owner → Prop) :
    ActualRealization (fun a φ => Provable (axioms a) φ) :=
  .ofAlphabetic _ (consequence_rawAlphabetic axioms)

def FilteredRealization.consequence {Owner : Type} (axioms : Owner → Formula Owner → Prop) :
    FilteredRealization (fun a φ => Provable (axioms a) φ) :=
  .ofAlphabetic _ (consequence_rawAlphabetic axioms)

end Alexander313
