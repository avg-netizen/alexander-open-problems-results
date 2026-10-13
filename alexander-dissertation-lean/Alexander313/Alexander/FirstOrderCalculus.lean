import Alexander313.Alexander.NativeSyntaxCoding
import Mathlib.ModelTheory.Semantics

/-!
# An explicit first-order Hilbert calculus and finite proof checker

This is ordinary first-order logic on native mathlib formulas. Free-variable
term substitution here is a first-order operation after Δ translation; it is
not a substitution rule for Alexander modal formulas. Generalization applies
to globally true first-order derivations from closed sentence premises.

The checker is a terminating syntax computation. Its accepted proofs are
exactly derivations of the displayed calculus, and those derivations are sound.
The later native coding/checker and effective BL program modules construct
proof-witness effectivity. `HilbertDeduction` and `HilbertLindenbaum` derive
closed-sentence deduction and maximal syntactic consistency. Semantic
completeness still needs Henkin witnesses and a canonical model truth proof;
it is not a field or hypothesis of a replacement contract.
-/

namespace Alexander313.FirstOrderCalculus

universe u v w

variable {L : FirstOrder.Language.{u, v}}

def bindVariable (x y : Nat) : Nat ⊕ Fin 1 :=
  if y = x then .inr 0 else .inl y

def allVariable (x : Nat) (φ : L.Formula Nat) : L.Formula Nat :=
  (FirstOrder.Language.BoundedFormula.relabel (bindVariable x) φ).all

def substituteVariable (x : Nat) (t : L.Term Nat) (φ : L.Formula Nat) :
    L.Formula Nat :=
  φ.subst (fun y => if y = x then t else .var y)

def sentenceFormula (σ : L.Sentence) : L.Formula Nat :=
  FirstOrder.Language.Formula.relabel Empty.elim σ

theorem allVariable_realize {D : Type w} [L.Structure D]
    (x : Nat) (φ : L.Formula Nat) (s : Nat → D) :
    (allVariable x φ).Realize s ↔ ∀ d, φ.Realize (Function.update s x d) := by
  change (FirstOrder.Language.BoundedFormula.relabel (bindVariable x) φ).all.Realize
    s (default : Fin 0 → D) ↔ _
  rw [FirstOrder.Language.BoundedFormula.realize_all]
  apply forall_congr'
  intro d
  rw [FirstOrder.Language.BoundedFormula.realize_relabel]
  have heq : (Sum.elim s
      (Fin.snoc (default : Fin 0 → D) d ∘ Fin.castAdd 0)) ∘ bindVariable x =
      Function.update s x d := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [bindVariable, Fin.snoc_zero]
    · simp [bindVariable, hy, Function.comp_def]
  rw [heq]
  exact FirstOrder.Language.Formula.boundedFormula_realize_eq_realize _ _ _

theorem substituteVariable_realize {D : Type w} [L.Structure D]
    (x : Nat) (t : L.Term Nat) (φ : L.Formula Nat) (s : Nat → D) :
    (substituteVariable x t φ).Realize s ↔
      φ.Realize (Function.update s x (t.realize s)) := by
  unfold substituteVariable
  change (φ.subst (fun y => if y = x then t else .var y)).Realize
    s (default : Fin 0 → D) ↔ _
  rw [FirstOrder.Language.BoundedFormula.realize_subst]
  have heq : (fun y => ((if y = x then t else .var y) : L.Term Nat).realize s) =
      Function.update s x (t.realize s) := by
    funext y
    by_cases hy : y = x <;> simp [hy, Function.update_apply,
      FirstOrder.Language.Term.realize]
  rw [heq]
  rfl

theorem formula_realize_eq_of_agree {D : Type w} [L.Structure D]
    (φ : L.Formula Nat) (s t : Nat → D)
    (h : ∀ x ∈ φ.freeVarFinset, s x = t x) : φ.Realize s ↔ φ.Realize t := by
  have hs := FirstOrder.Language.BoundedFormula.realize_restrictFreeVar
    (φ := φ) (f := id) (v := fun x : φ.freeVarFinset => s x)
    (xs := default) s (fun _ => rfl)
  have ht := FirstOrder.Language.BoundedFormula.realize_restrictFreeVar
    (φ := φ) (f := id) (v := fun x : φ.freeVarFinset => s x)
    (xs := default) t (fun x => h x x.property)
  exact hs.symm.trans ht

theorem sentenceFormula_realize {D : Type w} [L.Structure D]
    (σ : L.Sentence) (s : Nat → D) :
    (sentenceFormula σ).Realize s ↔ σ.Realize D := by
  rw [sentenceFormula, FirstOrder.Language.Formula.realize_relabel,
    FirstOrder.Language.Sentence.Realize]
  rw [Subsingleton.elim (s ∘ Empty.elim) (default : Empty → D)]

inductive LogicalAxiom : L.Formula Nat → Prop
  | k (φ ψ : L.Formula Nat) : LogicalAxiom (φ.imp (ψ.imp φ))
  | s (φ ψ χ : L.Formula Nat) : LogicalAxiom
      ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | classical (φ ψ : L.Formula Nat) : LogicalAxiom ((φ.not.imp ψ.not).imp (ψ.imp φ))
  | allElim (x : Nat) (t : L.Term Nat) (φ : L.Formula Nat) : LogicalAxiom
      ((allVariable x φ).imp (substituteVariable x t φ))
  | allDist (x : Nat) (φ ψ : L.Formula Nat) : LogicalAxiom
      ((allVariable x (φ.imp ψ)).imp ((allVariable x φ).imp (allVariable x ψ)))
  | vacuous (x : Nat) (φ : L.Formula Nat) (h : x ∉ φ.freeVarFinset) :
      LogicalAxiom (φ.imp (allVariable x φ))
  | eqRefl (t : L.Term Nat) : LogicalAxiom (t.equal t)
  | eqSubst (x : Nat) (t u : L.Term Nat) (φ : L.Formula Nat) : LogicalAxiom
      ((t.equal u).imp ((substituteVariable x t φ).imp (substituteVariable x u φ)))

theorem LogicalAxiom.sound {D : Type w} [L.Structure D] {φ : L.Formula Nat}
    (h : LogicalAxiom φ) (v : Nat → D) : φ.Realize v := by
  classical
  cases h with
  | k φ ψ => exact fun hφ _ => hφ
  | s φ ψ χ => exact fun h₁ h₂ hφ => h₁ hφ (h₂ hφ)
  | classical φ ψ =>
    intro h hψ
    by_contra hφ
    exact h hφ hψ
  | allElim x t φ =>
    intro h
    exact (substituteVariable_realize x t φ v).mpr
      ((allVariable_realize x φ v).mp h (t.realize v))
  | allDist x φ ψ =>
    intro h hp
    apply (allVariable_realize x ψ v).mpr
    intro d
    exact ((allVariable_realize x (φ.imp ψ) v).mp h d)
      ((allVariable_realize x φ v).mp hp d)
  | vacuous x φ hx =>
    intro h
    apply (allVariable_realize x φ v).mpr
    intro d
    apply (formula_realize_eq_of_agree φ v (Function.update v x d) ?_).mp h
    intro y hy
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    simp [Function.update_apply, hyx]
  | eqRefl t => exact (FirstOrder.Language.Formula.realize_equal).mpr rfl
  | eqSubst x t u φ =>
    intro heq ht
    have heq' : t.realize v = u.realize v :=
      (FirstOrder.Language.Formula.realize_equal).mp heq
    apply (substituteVariable_realize x u φ v).mpr
    rw [← heq']
    exact (substituteVariable_realize x t φ v).mp ht

inductive Derivation (T : L.Theory) : L.Formula Nat → Prop
  | logical {φ : L.Formula Nat} : LogicalAxiom φ → Derivation T φ
  | theory (σ : L.Sentence) : σ ∈ T → Derivation T (sentenceFormula σ)
  | mp {φ ψ : L.Formula Nat} : Derivation T (φ.imp ψ) → Derivation T φ → Derivation T ψ
  | generalize (x : Nat) {φ : L.Formula Nat} : Derivation T φ → Derivation T (allVariable x φ)

theorem Derivation.sound {T : L.Theory} {φ : L.Formula Nat}
    (h : Derivation T φ) {D : Type w} [L.Structure D]
    [FirstOrder.Language.Theory.Model D T] : ∀ v : Nat → D, φ.Realize v := by
  induction h with
  | logical h => exact h.sound
  | theory σ hσ =>
    intro v
    exact (sentenceFormula_realize σ v).mpr
      (FirstOrder.Language.Theory.realize_sentence_of_mem T hσ)
  | mp _ _ ih₁ ih₂ => exact fun v => ih₁ v (ih₂ v)
  | generalize x _ ih =>
    intro v
    exact (allVariable_realize x _ v).mpr (fun d => ih (Function.update v x d))

inductive ProofTree (L : FirstOrder.Language.{u, v})
  | assumption : L.Sentence → ProofTree L
  | k : L.Formula Nat → L.Formula Nat → ProofTree L
  | s : L.Formula Nat → L.Formula Nat → L.Formula Nat → ProofTree L
  | classical : L.Formula Nat → L.Formula Nat → ProofTree L
  | allElim : Nat → L.Term Nat → L.Formula Nat → ProofTree L
  | allDist : Nat → L.Formula Nat → L.Formula Nat → ProofTree L
  | vacuous : Nat → L.Formula Nat → ProofTree L
  | eqRefl : L.Term Nat → ProofTree L
  | eqSubst : Nat → L.Term Nat → L.Term Nat → L.Formula Nat → ProofTree L
  | mp : L.Formula Nat → L.Formula Nat → ProofTree L → ProofTree L → ProofTree L
  | generalize : Nat → L.Formula Nat → ProofTree L → ProofTree L

variable [DecidableEq (L.Formula Nat)]

def check (accept : L.Sentence → Bool) : ProofTree L → Option (L.Formula Nat)
  | .assumption σ => if accept σ then some (sentenceFormula σ) else none
  | .k φ ψ => some (φ.imp (ψ.imp φ))
  | .s φ ψ χ => some ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | .classical φ ψ => some ((φ.not.imp ψ.not).imp (ψ.imp φ))
  | .allElim x t φ => some ((allVariable x φ).imp (substituteVariable x t φ))
  | .allDist x φ ψ => some
      ((allVariable x (φ.imp ψ)).imp ((allVariable x φ).imp (allVariable x ψ)))
  | .vacuous x φ => if x ∉ φ.freeVarFinset then some (φ.imp (allVariable x φ)) else none
  | .eqRefl t => some (t.equal t)
  | .eqSubst x t u φ => some
      ((t.equal u).imp ((substituteVariable x t φ).imp (substituteVariable x u φ)))
  | .mp φ ψ p q =>
      if check accept p = some (φ.imp ψ) ∧ check accept q = some φ then some ψ else none
  | .generalize x φ p =>
      if check accept p = some φ then some (allVariable x φ) else none

def CheckedProof (accept : L.Sentence → Bool) (φ : L.Formula Nat) : Prop :=
  ∃ p, check accept p = some φ

theorem check_derivation (accept : L.Sentence → Bool) (p : ProofTree L) :
    ∀ φ, check accept p = some φ → Derivation {σ | accept σ = true} φ := by
  induction p with
  | assumption σ =>
    intro φ h
    simp only [check] at h
    split at h
    next ha =>
      cases Option.some.inj h
      exact .theory σ ha
    next => cases h
  | k φ ψ =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.k φ ψ)
  | s φ ψ χ =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.s φ ψ χ)
  | classical φ ψ =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.classical φ ψ)
  | allElim x t φ =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.allElim x t φ)
  | allDist x φ ψ =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.allDist x φ ψ)
  | vacuous x φ =>
    intro θ h
    simp only [check] at h
    split at h
    next hx =>
      cases Option.some.inj h
      exact .logical (.vacuous x φ hx)
    next => cases h
  | eqRefl t =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.eqRefl t)
  | eqSubst x t u φ =>
    intro θ h
    cases Option.some.inj h
    exact .logical (.eqSubst x t u φ)
  | mp φ ψ p q ihp ihq =>
    intro θ h
    simp only [check] at h
    split at h
    next hpq =>
      cases Option.some.inj h
      exact .mp (ihp _ hpq.1) (ihq _ hpq.2)
    next => cases h
  | generalize x φ p ih =>
    intro θ h
    simp only [check] at h
    split at h
    next hp =>
      cases Option.some.inj h
      exact .generalize x (ih _ hp)
    next => cases h

theorem Derivation.checked {accept : L.Sentence → Bool} {φ : L.Formula Nat}
    (h : Derivation {σ | accept σ = true} φ) : CheckedProof accept φ := by
  induction h with
  | logical h =>
    cases h with
    | k φ ψ => exact ⟨.k φ ψ, rfl⟩
    | s φ ψ χ => exact ⟨.s φ ψ χ, rfl⟩
    | classical φ ψ => exact ⟨.classical φ ψ, rfl⟩
    | allElim x t φ => exact ⟨.allElim x t φ, rfl⟩
    | allDist x φ ψ => exact ⟨.allDist x φ ψ, rfl⟩
    | vacuous x φ hx => exact ⟨.vacuous x φ, by simp [check, hx]⟩
    | eqRefl t => exact ⟨.eqRefl t, rfl⟩
    | eqSubst x t u φ => exact ⟨.eqSubst x t u φ, rfl⟩
  | theory σ hσ =>
    have ha : accept σ = true := hσ
    exact ⟨.assumption σ, by simp [check, ha]⟩
  | @mp φ ψ _ _ ihp ihq =>
    obtain ⟨p, hp⟩ := ihp
    obtain ⟨q, hq⟩ := ihq
    exact ⟨.mp φ ψ p q, by simp [check, hp, hq]⟩
  | @generalize x φ _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.generalize x φ p, by simp [check, hp]⟩

theorem checked_iff_derivation (accept : L.Sentence → Bool) (φ : L.Formula Nat) :
    CheckedProof accept φ ↔ Derivation {σ | accept σ = true} φ :=
  ⟨fun ⟨p, hp⟩ => check_derivation accept p φ hp, Derivation.checked⟩

theorem CheckedProof.sound {accept : L.Sentence → Bool} {φ : L.Formula Nat}
    (h : CheckedProof accept φ) {D : Type w} [L.Structure D]
    [FirstOrder.Language.Theory.Model D {σ | accept σ = true}] :
    ∀ v : Nat → D, φ.Realize v :=
  ((checked_iff_derivation accept φ).mp h).sound

end Alexander313.FirstOrderCalculus
