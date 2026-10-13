import Alexander313.Alexander.HilbertLindenbaum

/-!
# Literal language maps and native Hilbert proof transport

An arity-preserving map of function and relation symbols constructs actual
native term, bounded-formula, sentence and theory maps. The maps commute with
the existing free-variable substitution and binding operations. Every logical
axiom and every derivation is transported by its existing constructor; no
logical rule, semantic completeness premise or model input is added.
-/

namespace Alexander313.FirstOrderCalculus

universe u v u' v' w

structure SymbolMap (L : FirstOrder.Language.{u, v})
    (M : FirstOrder.Language.{u', v'}) where
  onFunction : ∀ n, L.Functions n → M.Functions n
  onRelation : ∀ n, L.Relations n → M.Relations n

namespace SymbolMap

variable {L : FirstOrder.Language.{u, v}} {M : FirstOrder.Language.{u', v'}}

def termMap (m : SymbolMap L M) {α : Type w} : L.Term α → M.Term α
  | .var x => .var x
  | .func f ts => .func (m.onFunction _ f) (fun i => termMap m (ts i))

def formulaMap (m : SymbolMap L M) {α : Type w} :
    {n : Nat} → L.BoundedFormula α n → M.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t s => .equal (termMap m t) (termMap m s)
  | _, .rel r ts => .rel (m.onRelation _ r) (fun i => termMap m (ts i))
  | _, .imp φ ψ => .imp (formulaMap m φ) (formulaMap m ψ)
  | _, .all φ => .all (formulaMap m φ)

def theoryMap (m : SymbolMap L M) (T : L.Theory) : M.Theory :=
  formulaMap m '' T

@[simp] theorem termMap_relabel (m : SymbolMap L M) {α β : Type w}
    (f : α → β) (t : L.Term α) :
    termMap m (t.relabel f) = (termMap m t).relabel f := by
  induction t <;> simp_all [termMap, FirstOrder.Language.Term.relabel]

@[simp] theorem termMap_subst (m : SymbolMap L M) {α β : Type w}
    (f : α → L.Term β) (t : L.Term α) :
    termMap m (t.subst f) = (termMap m t).subst (fun x => termMap m (f x)) := by
  induction t <;> simp_all [termMap, FirstOrder.Language.Term.subst]

@[simp] theorem formulaMap_relabel (m : SymbolMap L M) {α β : Type w}
    {n d : Nat} (f : α → β ⊕ Fin d) (φ : L.BoundedFormula α n) :
    formulaMap m (φ.relabel f) = (formulaMap m φ).relabel f := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp [formulaMap, FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel]
  | rel r ts =>
    simp [formulaMap, FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, Function.comp_def]
  | imp φ ψ ihφ ihψ =>
    simp [formulaMap, FirstOrder.Language.BoundedFormula.relabel_imp, ihφ, ihψ]
  | all φ ih =>
    rw [FirstOrder.Language.BoundedFormula.relabel_all]
    simp [formulaMap, FirstOrder.Language.BoundedFormula.relabel_all, ih]

@[simp] theorem formulaMap_subst (m : SymbolMap L M) {α β : Type w}
    {n : Nat} (f : α → L.Term β) (φ : L.BoundedFormula α n) :
    formulaMap m (φ.subst f) = (formulaMap m φ).subst (fun x => termMap m (f x)) := by
  have hlift (k : Nat) :
      (fun a : α ⊕ Fin k => termMap m
        (Sum.elim (FirstOrder.Language.Term.relabel Sum.inl ∘ f)
          (FirstOrder.Language.Term.var ∘ Sum.inr) a)) =
      Sum.elim (FirstOrder.Language.Term.relabel Sum.inl ∘ (fun x => termMap m (f x)))
        (FirstOrder.Language.Term.var ∘ Sum.inr) := by
    funext a
    cases a <;> simp [termMap, Function.comp_def]
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp [formulaMap, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, hlift]
  | rel r ts =>
    simp [formulaMap, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, hlift]
  | imp φ ψ ihφ ihψ =>
    exact congrArg₂ FirstOrder.Language.BoundedFormula.imp ihφ ihψ
  | all φ ih =>
    exact congrArg FirstOrder.Language.BoundedFormula.all ih

@[simp] theorem termMap_varFinsetLeft (m : SymbolMap L M) {n : Nat}
    (t : L.Term (Nat ⊕ Fin n)) : (termMap m t).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var a => cases a <;> rfl
  | func F ts ih => simp_all [termMap]

@[simp] theorem formulaMap_freeVarFinset (m : SymbolMap L M) {n : Nat}
    (φ : L.BoundedFormula Nat n) : (formulaMap m φ).freeVarFinset = φ.freeVarFinset := by
  induction φ <;> simp_all [formulaMap, FirstOrder.Language.BoundedFormula.freeVarFinset]

@[simp] theorem formulaMap_falsum (m : SymbolMap L M) {α : Type w} {n : Nat} :
    formulaMap m (⊥ : L.BoundedFormula α n) = (⊥ : M.BoundedFormula α n) := rfl

@[simp] theorem formulaMap_equal (m : SymbolMap L M) {α : Type w} {n : Nat}
    (t s : L.Term (α ⊕ Fin n)) :
    formulaMap m (.equal t s) = .equal (termMap m t) (termMap m s) := rfl

@[simp] theorem formulaMap_termEqual (m : SymbolMap L M) {α : Type w}
    (t s : L.Term α) :
    formulaMap m (t.equal s) = (termMap m t).equal (termMap m s) := by
  change FirstOrder.Language.BoundedFormula.equal
      (termMap m (t.relabel Sum.inl)) (termMap m (s.relabel Sum.inl)) =
    FirstOrder.Language.BoundedFormula.equal
      ((termMap m t).relabel Sum.inl) ((termMap m s).relabel Sum.inl)
  rw [termMap_relabel, termMap_relabel]

@[simp] theorem formulaMap_imp (m : SymbolMap L M) {α : Type w} {n : Nat}
    (φ ψ : L.BoundedFormula α n) :
    formulaMap m (φ.imp ψ) = (formulaMap m φ).imp (formulaMap m ψ) := rfl

@[simp] theorem formulaMap_not (m : SymbolMap L M) {α : Type w} {n : Nat}
    (φ : L.BoundedFormula α n) : formulaMap m φ.not = (formulaMap m φ).not := rfl

@[simp] theorem formulaMap_allVariable (m : SymbolMap L M) (x : Nat)
    (φ : L.Formula Nat) :
    formulaMap m (allVariable x φ) = allVariable x (formulaMap m φ) := by
  simp only [allVariable, formulaMap, formulaMap_relabel]

@[simp] theorem formulaMap_substituteVariable (m : SymbolMap L M) (x : Nat)
    (t : L.Term Nat) (φ : L.Formula Nat) :
    formulaMap m (substituteVariable x t φ) =
      substituteVariable x (termMap m t) (formulaMap m φ) := by
  unfold substituteVariable
  rw [formulaMap_subst]
  congr 1
  funext y
  split_ifs <;> rfl

@[simp] theorem formulaMap_existsVariable (m : SymbolMap L M) (x : Nat)
    (φ : L.Formula Nat) :
    formulaMap m (existsVariable x φ) = existsVariable x (formulaMap m φ) := by
  simp only [existsVariable, formulaMap_not, formulaMap_allVariable]

@[simp] theorem sentenceFormula_map (m : SymbolMap L M) (σ : L.Sentence) :
    sentenceFormula (formulaMap m σ) = formulaMap m (sentenceFormula σ) := by
  unfold sentenceFormula FirstOrder.Language.Formula.relabel
  exact (formulaMap_relabel m _ σ).symm

theorem mem_theoryMap (m : SymbolMap L M) (T : L.Theory) (σ : M.Sentence) :
    σ ∈ theoryMap m T ↔ ∃ τ ∈ T, formulaMap m τ = σ := Iff.rfl

end SymbolMap

namespace LogicalAxiom

variable {L : FirstOrder.Language.{u, v}} {M : FirstOrder.Language.{u', v'}}

theorem map {φ : L.Formula Nat} (h : LogicalAxiom φ) (m : SymbolMap L M) :
    LogicalAxiom (m.formulaMap φ) := by
  cases h with
  | k φ ψ => exact .k _ _
  | s φ ψ χ => exact .s _ _ _
  | classical φ ψ => exact .classical _ _
  | allElim x t φ =>
    simpa only [SymbolMap.formulaMap_imp, SymbolMap.formulaMap_allVariable,
      SymbolMap.formulaMap_substituteVariable] using
      (LogicalAxiom.allElim x (m.termMap t) (m.formulaMap φ))
  | allDist x φ ψ =>
    simpa only [SymbolMap.formulaMap_imp, SymbolMap.formulaMap_allVariable] using
      (LogicalAxiom.allDist x (m.formulaMap φ) (m.formulaMap ψ))
  | vacuous x φ hx =>
    simpa only [SymbolMap.formulaMap_imp, SymbolMap.formulaMap_allVariable] using
      (LogicalAxiom.vacuous x (m.formulaMap φ) (by simpa using hx))
  | eqRefl t =>
    simpa only [SymbolMap.formulaMap_termEqual] using LogicalAxiom.eqRefl (m.termMap t)
  | eqSubst x t s φ =>
    simpa only [SymbolMap.formulaMap_imp, SymbolMap.formulaMap_termEqual,
      SymbolMap.formulaMap_substituteVariable] using
      (LogicalAxiom.eqSubst x (m.termMap t) (m.termMap s) (m.formulaMap φ))

end LogicalAxiom

namespace Derivation

variable {L : FirstOrder.Language.{u, v}} {M : FirstOrder.Language.{u', v'}}

theorem map {T : L.Theory} {φ : L.Formula Nat} (h : Derivation T φ)
    (m : SymbolMap L M) : Derivation (m.theoryMap T) (m.formulaMap φ) := by
  induction h with
  | logical h => exact .logical (h.map m)
  | theory σ hσ =>
    simpa only [SymbolMap.sentenceFormula_map] using
      (Derivation.theory (m.formulaMap σ) ⟨σ, hσ, rfl⟩ :
        Derivation (m.theoryMap T) _)
  | mp hp hq ihp ihq => exact .mp ihp ihq
  | generalize x h ih =>
    simpa only [SymbolMap.formulaMap_allVariable] using Derivation.generalize x ih

end Derivation

end Alexander313.FirstOrderCalculus
