import Alexander313.RecordedBackground

/-!
# Literal numerical substitution through a recorded one-hole context

The substitution at the hole loses exactly the variables bound on its context
path. Fixed surrounding formulas receive the substitution at their own depth.
Thus the construction preserves the actual terms, binder names and modal heads;
it proves a syntax identity and introduces no modal numeral-substitution rule.
Numerically closing two contextual fillings therefore gives a new actual
contextual-collapse row whenever its usual admissibility checks hold.
-/

namespace Alexander313
namespace Formula

theorem recordedAdmissible_imp_iff {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (φ ψ : Formula (RecordedHead Nat Label)) :
    (Formula.imp φ ψ).RecordedAdmissible A E ↔
      φ.RecordedAdmissible A E ∧ ψ.RecordedAdmissible A E := by
  simp only [RecordedAdmissible, HeadsAllowed, GloballyStratified]
  tauto

theorem recordedAdmissible_conj_iff {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (φ ψ : Formula (RecordedHead Nat Label)) :
    (Formula.conj φ ψ).RecordedAdmissible A E ↔
      φ.RecordedAdmissible A E ∧ ψ.RecordedAdmissible A E := by
  simp only [RecordedAdmissible, HeadsAllowed, GloballyStratified]
  tauto

theorem recordedAdmissible_disj_iff {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (φ ψ : Formula (RecordedHead Nat Label)) :
    (Formula.disj φ ψ).RecordedAdmissible A E ↔
      φ.RecordedAdmissible A E ∧ ψ.RecordedAdmissible A E := by
  simp only [RecordedAdmissible, HeadsAllowed, GloballyStratified]
  tauto

theorem recordedAdmissible_iff_iff {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (φ ψ : Formula (RecordedHead Nat Label)) :
    (Formula.iff φ ψ).RecordedAdmissible A E ↔
      φ.RecordedAdmissible A E ∧ ψ.RecordedAdmissible A E := by
  simp only [Formula.iff, recordedAdmissible_conj_iff, recordedAdmissible_imp_iff]
  tauto

namespace Context

variable {Owner : Type}

def holeSubstitution (σ : NumericalSubstitution) : Context Owner → NumericalSubstitution
  | .hole => σ
  | .impLeft c _ => c.holeSubstitution σ
  | .impRight _ c => c.holeSubstitution σ
  | .conjLeft c _ => c.holeSubstitution σ
  | .conjRight _ c => c.holeSubstitution σ
  | .disjLeft c _ => c.holeSubstitution σ
  | .disjRight _ c => c.holeSubstitution σ
  | .neg c => c.holeSubstitution σ
  | .all x c => c.holeSubstitution (σ.remove x)
  | .ex x c => c.holeSubstitution (σ.remove x)
  | .know _ c => c.holeSubstitution σ

def subst (σ : NumericalSubstitution) : Context Owner → Context Owner
  | .hole => .hole
  | .impLeft c ψ => .impLeft (c.subst σ) (ψ.subst σ)
  | .impRight ψ c => .impRight (ψ.subst σ) (c.subst σ)
  | .conjLeft c ψ => .conjLeft (c.subst σ) (ψ.subst σ)
  | .conjRight ψ c => .conjRight (ψ.subst σ) (c.subst σ)
  | .disjLeft c ψ => .disjLeft (c.subst σ) (ψ.subst σ)
  | .disjRight ψ c => .disjRight (ψ.subst σ) (c.subst σ)
  | .neg c => .neg (c.subst σ)
  | .all x c => .all x (c.subst (σ.remove x))
  | .ex x c => .ex x (c.subst (σ.remove x))
  | .know a c => .know a (c.subst σ)

@[simp] theorem fill_subst (c : Context Owner) (φ : Formula Owner)
    (σ : NumericalSubstitution) :
    (c.fill φ).subst σ = (c.subst σ).fill (φ.subst (c.holeSubstitution σ)) := by
  induction c generalizing σ <;> simp_all [fill, Formula.subst, subst, holeSubstitution]

theorem fill_indexed_subst {Base Label : Type}
    (c : Context (RecordedHead Base Label)) (a : Base) (ν : Label)
    (φ : Formula (RecordedHead Base Label)) (σ : NumericalSubstitution) :
    (c.fill (.know (.indexed a ν) φ)).subst σ =
      (c.subst σ).fill (.know (.indexed a ν) (φ.subst (c.holeSubstitution σ))) := by
  rw [fill_subst]
  rfl

theorem erase_fill_indexed {Base Label : Type}
    (c : Context (RecordedHead Base Label)) (a : Base) (μ ν : Label)
    (φ : Formula (RecordedHead Base Label)) :
    (c.fill (.know (.indexed a μ) φ)).erase =
      (c.fill (.know (.indexed a ν) φ)).erase := by
  simp only [Formula.erase, mapOwner_fill, Formula.mapOwner, RecordedHead.erase]

theorem erase_close_fill_indexed {Base Label : Type}
    (c : Context (RecordedHead Base Label)) (a : Base) (μ ν : Label)
    (φ : Formula (RecordedHead Base Label)) (s : Assignment) :
    ((c.fill (.know (.indexed a μ) φ)).close s).erase =
      ((c.fill (.know (.indexed a ν) φ)).close s).erase := by
  simpa only [Formula.erase, Formula.mapOwner_close] using
    congrArg (fun θ => θ.close s) (erase_fill_indexed c a μ ν φ)

/-- The numerically closed equivalence is literally another contextual row.
The context's bound variables remain in its residual hole substitution. -/
theorem contextualCollapse_close_fill {Base Label : Type}
    (c : Context (RecordedHead Base Label)) (a : Base) (μ ν : Label)
    (φ : Formula (RecordedHead Base Label)) (s : Assignment) :
    Formula.contextualCollapse (c.subst (fun x => some (s x))) a μ ν
      (φ.subst (c.holeSubstitution (fun x => some (s x)))) =
      Formula.iff ((c.fill (.know (.indexed a μ) φ)).close s)
        ((c.fill (.know (.indexed a ν) φ)).close s) := by
  have hμ := fill_indexed_subst c a μ φ (fun x => some (s x))
  have hν := fill_indexed_subst c a ν φ (fun x => some (s x))
  have hcμ : ((c.fill (.know (.indexed a μ) φ)).close s).freeVars = ∅ :=
    (c.fill (.know (.indexed a μ) φ)).close_closed s
  have hcν : ((c.fill (.know (.indexed a ν) φ)).close s).freeVars = ∅ :=
    (c.fill (.know (.indexed a ν) φ)).close_closed s
  have hc : (Formula.iff ((c.fill (.know (.indexed a μ) φ)).close s)
      ((c.fill (.know (.indexed a ν) φ)).close s)).Closed := by
    simp only [Formula.iff, Closed, freeVars, hcμ, hcν, Finset.empty_union]
  rw [Formula.contextualCollapse, ← hμ, ← hν]
  exact Formula.universalClosure_eq_self_of_closed _ hc

end Context
end Formula
end Alexander313
