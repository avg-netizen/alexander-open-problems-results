import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Finset.Sort

/-!
# A concrete closed universal sentence for a native first-order formula

Variables are natural numbers. We restrict to the finite free-variable set,
sort that set increasingly, and bind its indexed variables with `alls`.
The syntax construction uses no choice and no supplied closure witness.
-/

namespace Alexander313.FirstOrderClosure

universe u v w

variable {L : FirstOrder.Language.{u, v}}

def universalSentence (σ : L.Formula Nat) : L.Sentence :=
  (FirstOrder.Language.BoundedFormula.relabel
    (fun x : σ.freeVarFinset =>
      (Sum.inr ((σ.freeVarFinset.orderIsoOfFin rfl).symm x) :
        Empty ⊕ Fin σ.freeVarFinset.card)) (σ.restrictFreeVar id)).alls

theorem universalSentence_realize {D : Type w} [L.Structure D] [Nonempty D]
    (σ : L.Formula Nat) :
    (universalSentence σ).Realize D ↔ ∀ s : Nat → D, σ.Realize s := by
  classical
  let e : Fin σ.freeVarFinset.card ≃o σ.freeVarFinset :=
    σ.freeVarFinset.orderIsoOfFin rfl
  unfold universalSentence
  rw [FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.BoundedFormula.realize_alls]
  constructor
  · intro h s
    have hx := h (fun i => s (e i))
    rw [FirstOrder.Language.BoundedFormula.realize_relabel] at hx
    have hr : FirstOrder.Language.Formula.Realize (σ.restrictFreeVar id)
        (fun x : σ.freeVarFinset => s x) := by
      apply (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize _ _ _).mp
      simpa only [Fin.castAdd_zero, Fin.cast_eq_self, Function.comp_def, Sum.elim_inr,
        e, OrderIso.apply_symm_apply] using hx
    have ht := (FirstOrder.Language.BoundedFormula.realize_restrictFreeVar
      (φ := σ) (f := id) (v := fun x : σ.freeVarFinset => s x) (xs := default)
      s (fun _ => rfl)).mp hr
    exact (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize _ _ _).mp ht
  · intro h xs
    rw [FirstOrder.Language.BoundedFormula.realize_relabel]
    let values : σ.freeVarFinset → D := fun x => xs (e.symm x)
    let assignment : Nat → D := fun x =>
      if hx : x ∈ σ.freeVarFinset then values ⟨x, hx⟩
      else Classical.choice (inferInstance : Nonempty D)
    have hv : ∀ x : σ.freeVarFinset, values x = assignment x := by
      intro x
      simp only [assignment, dif_pos x.property]
    have ht : FirstOrder.Language.BoundedFormula.Realize σ assignment
        (xs ∘ Fin.natAdd σ.freeVarFinset.card) :=
      (FirstOrder.Language.Formula.boundedFormula_realize_eq_realize _ _ _).mpr
        (h assignment)
    have hr := (FirstOrder.Language.BoundedFormula.realize_restrictFreeVar
      (φ := σ) (f := id) (v := values) assignment hv).mpr ht
    simpa only [Fin.castAdd_zero, Fin.cast_eq_self, Function.comp_def, Sum.elim_inr, values, e] using hr

end Alexander313.FirstOrderClosure
