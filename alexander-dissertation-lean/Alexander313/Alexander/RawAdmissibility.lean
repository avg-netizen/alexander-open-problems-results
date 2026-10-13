import Alexander313.Alexander.AlphaOpening
import Alexander313.Alexander.FilteredModel

/-!
# Actual and filtered admissibility from alphabetic sentence predicates

The only predicate property used is invariance on closed alpha-equivalent
sentences. Free independence and capture-safe weak variable substitution
are proved for the recursive evaluations. The recursive filtered evaluation
also preserves alphabetic variants; its quantifier step opens the alpha
binder with a numeral and uses induction on logical formula size. There is
no soundness premise and no term-substitution validity principle.
-/

namespace Alexander313

theorem truth_substVar {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (φ : Formula Owner) (x y : Nat) (s : Assignment) (h : φ.VarSubstitutable x y) :
    truth filtered P (φ.substVar x y) s ↔
      truth filtered P φ (Function.update s x (s y)) := by
  calc
    truth filtered P (φ.substVar x y) s ↔
        truth filtered P ((φ.substVar x y).close s) s := (truth_close filtered P _ s s).symm
    _ ↔ truth filtered P (φ.close (Function.update s x (s y))) s := by
      rw [φ.close_substVar x y s h]
    _ ↔ truth filtered P φ (Function.update s x (s y)) := truth_close filtered P _ _ _

theorem truth_alpha_closed {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (hP : RawAlphabetic P) (φ ψ : Formula Owner)
    (hφ : φ.Closed) (hψ : ψ.Closed) (hα : φ.AlphaEquivalent ψ) (s : Assignment) :
    truth filtered P φ s ↔ truth filtered P ψ s := by
  have main : ∀ k : Nat, ∀ φ ψ : Formula Owner, φ.logicalSize = k →
      φ.Closed → ψ.Closed → φ.AlphaEquivalent ψ → ∀ s : Assignment,
      (truth filtered P φ s ↔ truth filtered P ψ s) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro φ ψ hk hc hd hα s
      cases φ with
      | falsum =>
        cases ψ <;> simp_all [Formula.AlphaEquivalent, Formula.alpha, truth]
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
        have hc' : φ.Closed ∧ χ.Closed := by
          simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hc
        have hd' : ψ.Closed ∧ η.Closed := by
          simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hd
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hχk : χ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have htφ := ih φ.logicalSize hφk φ ψ rfl hc'.1 hd'.1 hα.1 s
        have htχ := ih χ.logicalSize hχk χ η rfl hc'.2 hd'.2 hα.2 s
        simp only [truth, htφ, htχ]
      | conj φ χ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ η
        have hc' : φ.Closed ∧ χ.Closed := by
          simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hc
        have hd' : ψ.Closed ∧ η.Closed := by
          simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hd
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hχk : χ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        exact and_congr
          (ih φ.logicalSize hφk φ ψ rfl hc'.1 hd'.1 hα.1 s)
          (ih χ.logicalSize hχk χ η rfl hc'.2 hd'.2 hα.2 s)
      | disj φ χ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ η
        have hc' : φ.Closed ∧ χ.Closed := by
          simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hc
        have hd' : ψ.Closed ∧ η.Closed := by
          simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hd
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hχk : χ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        exact or_congr
          (ih φ.logicalSize hφk φ ψ rfl hc'.1 hd'.1 hα.1 s)
          (ih χ.logicalSize hχk χ η rfl hc'.2 hd'.2 hα.2 s)
      | neg φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i ψ
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        exact not_congr (ih φ.logicalSize hφk φ ψ rfl hc hd hα s)
      | know a φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i b ψ
        obtain ⟨hab, hα⟩ := hα
        subst b
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hp := hP a φ ψ hc hd hα
        have ht := ih φ.logicalSize hφk φ ψ rfl hc hd hα s
        change (P a (φ.close s) ∧ (if filtered = true then truth filtered P φ s else True)) ↔
          (P a (ψ.close s) ∧ (if filtered = true then truth filtered P ψ s else True))
        rw [φ.close_eq_self_of_closed hc s, ψ.close_eq_self_of_closed hd s]
        cases filtered <;> simp only [Bool.false_eq_true, ↓reduceIte, hp, ht]
      | all x φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i y ψ
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hfx := φ.freeVars_subset_singleton_of_all_closed x hc
        have hfy := ψ.freeVars_subset_singleton_of_all_closed y hd
        apply forall_congr'
        intro n
        have hn : (φ.close (Function.update s x n)).AlphaEquivalent
            (ψ.close (Function.update s y n)) := by
          unfold Formula.AlphaEquivalent
          rw [φ.close_singleton x n s hfx, ψ.close_singleton y n s hfy,
            Formula.alpha_numericalAt, Formula.alpha_numericalAt]
          exact congrArg (AlphaFormula.instantiate 0 n) hα
        have ht := ih φ.logicalSize hφk (φ.close (Function.update s x n))
          (ψ.close (Function.update s y n)) (φ.logicalSize_close _)
          (φ.close_closed _) (ψ.close_closed _) hn s
        exact (truth_close filtered P φ (Function.update s x n) s).symm.trans
          (ht.trans (truth_close filtered P ψ (Function.update s y n) s))
      | ex x φ =>
        cases ψ <;> simp [Formula.AlphaEquivalent, Formula.alpha] at hα
        rename_i y ψ
        have hφk : φ.logicalSize < k := by simp only [Formula.logicalSize] at hk; omega
        have hfx := φ.freeVars_subset_singleton_of_ex_closed x hc
        have hfy := ψ.freeVars_subset_singleton_of_ex_closed y hd
        apply exists_congr
        intro n
        have hn : (φ.close (Function.update s x n)).AlphaEquivalent
            (ψ.close (Function.update s y n)) := by
          unfold Formula.AlphaEquivalent
          rw [φ.close_singleton x n s hfx, ψ.close_singleton y n s hfy,
            Formula.alpha_numericalAt, Formula.alpha_numericalAt]
          exact congrArg (AlphaFormula.instantiate 0 n) hα
        have ht := ih φ.logicalSize hφk (φ.close (Function.update s x n))
          (ψ.close (Function.update s y n)) (φ.logicalSize_close _)
          (φ.close_closed _) (ψ.close_closed _) hn s
        exact (truth_close filtered P φ (Function.update s x n) s).symm.trans
          (ht.trans (truth_close filtered P ψ (Function.update s y n) s))
  exact main φ.logicalSize φ ψ rfl hφ hψ hα s

theorem truth_alpha {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (hP : RawAlphabetic P) (φ ψ : Formula Owner) (hα : φ.AlphaEquivalent ψ)
    (s : Assignment) : truth filtered P φ s ↔ truth filtered P ψ s := by
  exact (truth_close filtered P φ s s).symm.trans
    ((truth_alpha_closed filtered P hP (φ.close s) (ψ.close s)
      (φ.close_closed s) (ψ.close_closed s) (hα.close s) s).trans
      (truth_close filtered P ψ s s))

def filteredModelOfAlphabetic {Owner : Type} (P : RawPredicates Owner)
    (hP : RawAlphabetic P) : ModalModel Owner Nat where
  zero := 0
  succ := fun n => n + 1
  add := Nat.add
  mul := Nat.mul
  modal := fun a φ s => filteredTruth P (.know a φ) s
  free_independence := fun a φ s t h => truth_eq_of_agree true P (.know a φ) s t h
  alphabetic := by
    intro a φ ψ s h
    have hknow : (Formula.know a φ).AlphaEquivalent (.know a ψ) :=
      congrArg (AlphaFormula.know a) h
    exact truth_alpha true P hP (.know a φ) (.know a ψ) hknow s
  weak_substitution := fun a φ x y s h => truth_substVar true P (.know a φ) x y s h

def FilteredRealization.ofAlphabetic {Owner : Type} (P : RawPredicates Owner)
    (hP : RawAlphabetic P) : FilteredRealization P where
  model := filteredModelOfAlphabetic P hP
  zero_correct := rfl
  succ_correct := fun _ => rfl
  add_correct := fun _ _ => rfl
  mul_correct := fun _ _ => rfl
  modal_correct := fun _ _ _ => Iff.rfl

end Alexander313
