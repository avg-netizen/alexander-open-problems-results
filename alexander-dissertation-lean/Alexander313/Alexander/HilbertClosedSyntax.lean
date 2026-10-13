import Alexander313.Alexander.HilbertDeduction

/-!
# Literal closed native syntax for the Henkin construction

Restriction to the actual finite free-variable support constructs sentences
without choosing a default closed term. Its syntactic inverse is proved, so
packaging a closed formula changes neither the formula nor the Hilbert rules.
Closed-term embeddings and named quantification/substitution closure laws
provide the actual sentence boundary used by witness and quotient proofs.
-/

namespace Alexander313.FirstOrderCalculus

universe u v

variable {L : FirstOrder.Language.{u, v}}

namespace ClosedTerm

def embed (t : L.Term Empty) : L.Term Nat := t.relabel Empty.elim

@[simp] theorem embed_subst (t : L.Term Empty) (f : Nat → L.Term Nat) :
    (embed t).subst f = embed t := by
  induction t with
  | var x => exact x.elim
  | func F ts ih =>
    simp only [embed] at ih
    simp [embed, FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst, ih]

@[simp] theorem embed_varFinset (t : L.Term Empty) : (embed t).varFinset = ∅ := by
  induction t with
  | var x => exact x.elim
  | func F ts ih =>
    simp only [embed] at ih
    simp [embed, FirstOrder.Language.Term.relabel, ih, Finset.ext_iff]

@[simp] theorem embed_func {n : Nat} (f : L.Functions n) (ts : Fin n → L.Term Empty) :
    embed (.func f ts) = .func f (fun i => embed (ts i)) := rfl

end ClosedTerm

namespace ClosedFormula

def mapFree {α β : Type} (f : α → β) {n : Nat} (φ : L.BoundedFormula α n) :
    L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)

private theorem relabelAux_free {α β : Type} (f : α → β) (n : Nat) :
    FirstOrder.Language.BoundedFormula.relabelAux
      (Sum.inl ∘ f : α → β ⊕ Fin 0) n = Sum.map f (Fin.natAdd 0) := by
  funext x
  cases x <;> simp [FirstOrder.Language.BoundedFormula.relabelAux, Function.comp_def]

theorem relabel_mapFree {α β : Type} (f : α → β) {n : Nat}
    (φ : L.BoundedFormula α n) :
    φ.relabel (Sum.inl ∘ f : α → β ⊕ Fin 0) =
      (mapFree f φ).castLE (ge_of_eq (Nat.zero_add n)) := by
  simp only [FirstOrder.Language.BoundedFormula.relabel, relabelAux_free]
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp [mapFree, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.castLE, Fin.natAdd_zero]
    constructor <;> rfl
  | rel r ts =>
    simp [mapFree, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.castLE, Fin.natAdd_zero]
    funext i
    simp only [Function.comp_apply, FirstOrder.Language.Term.relabel_relabel]
    congr 1
    funext a
    cases a <;> rfl
  | imp φ ψ ihφ ihψ =>
    simp_all [mapFree, FirstOrder.Language.BoundedFormula.mapTermRel]
  | all φ ih => simp_all [mapFree, FirstOrder.Language.BoundedFormula.mapTermRel]

theorem sentenceFormula_eq_mapFree (σ : L.Sentence) :
    sentenceFormula σ = mapFree Empty.elim σ := by
  simpa only [sentenceFormula, FirstOrder.Language.Formula.relabel,
    FirstOrder.Language.BoundedFormula.castLE_rfl] using relabel_mapFree Empty.elim σ

private theorem map_restrictTerm {α β : Type} [DecidableEq α]
    {n : Nat} (t : L.Term (α ⊕ Fin n)) (f : t.varFinsetLeft → β) (g : β → α)
    (hf : ∀ x, g (f x) = x.val) :
    (t.restrictVarLeft f).relabel (Sum.map g id) = t := by
  revert f
  induction t with
  | var a =>
    intro f hf
    cases a with
    | inl a => simp [FirstOrder.Language.Term.restrictVarLeft, hf]
    | inr i => rfl
  | func F ts ih =>
    intro f hf
    simp only [FirstOrder.Language.Term.restrictVarLeft, FirstOrder.Language.Term.relabel]
    congr 1
    funext i
    apply ih i
    intro x
    exact hf _

theorem mapFree_restrictFreeVar {α β : Type} [DecidableEq α] {n : Nat}
    (φ : L.BoundedFormula α n) (f : φ.freeVarFinset → β) (g : β → α)
    (hf : ∀ x, g (f x) = x.val) : mapFree g (φ.restrictFreeVar f) = φ := by
  revert f
  induction φ with
  | falsum => intro _ _; rfl
  | equal t s =>
    intro f hf
    simp only [FirstOrder.Language.BoundedFormula.restrictFreeVar, mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel]
    congr 1 <;> apply map_restrictTerm <;> intro x <;> exact hf _
  | rel r ts =>
    intro f hf
    simp only [FirstOrder.Language.BoundedFormula.restrictFreeVar, mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel]
    congr 1
    funext i
    apply map_restrictTerm
    intro x
    exact hf _
  | imp φ ψ ihφ ihψ =>
    intro f hf
    simp only [FirstOrder.Language.BoundedFormula.restrictFreeVar, mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel]
    congr 1
    · apply ihφ; intro x; exact hf _
    · apply ihψ; intro x; exact hf _
  | all φ ih =>
    intro f hf
    exact congrArg FirstOrder.Language.BoundedFormula.all (ih f hf)

def sentence (φ : L.Formula Nat) (h : φ.freeVarFinset = ∅) : L.Sentence :=
  φ.restrictFreeVar (fun x => False.elim (Finset.notMem_empty x.val (h ▸ x.property)))

@[simp] theorem sentenceFormula_sentence (φ : L.Formula Nat)
    (h : φ.freeVarFinset = ∅) : sentenceFormula (sentence φ h) = φ := by
  rw [sentenceFormula_eq_mapFree]
  apply mapFree_restrictFreeVar
  intro x
  exact False.elim (Finset.notMem_empty x.val (h ▸ x.property))

theorem exists_sentence_iff (φ : L.Formula Nat) :
    (∃ σ : L.Sentence, sentenceFormula σ = φ) ↔ φ.freeVarFinset = ∅ := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact sentenceFormula_freeVarFinset σ
  · intro h
    exact ⟨sentence φ h, sentenceFormula_sentence φ h⟩

@[simp] theorem sentenceFormula_equal (t s : L.Term Empty) :
    sentenceFormula (t.equal s) = (ClosedTerm.embed t).equal (ClosedTerm.embed s) := by
  rw [sentenceFormula_eq_mapFree]
  simp [mapFree, ClosedTerm.embed, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.Term.relabel_relabel, Function.comp_def]

def relation {n : Nat} (r : L.Relations n) (ts : Fin n → L.Term Empty) : L.Sentence :=
  .rel r (fun i => (ts i).relabel Sum.inl)

@[simp] theorem sentenceFormula_relation {n : Nat} (r : L.Relations n)
    (ts : Fin n → L.Term Empty) :
    sentenceFormula (relation r ts) =
      .rel r (fun i => (ClosedTerm.embed (ts i)).relabel Sum.inl) := by
  rw [sentenceFormula_eq_mapFree]
  simp [relation, mapFree, ClosedTerm.embed,
    FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.Term.relabel_relabel, Function.comp_def]

private theorem relabelLeft_varFinset (t : L.Term Nat) {n : Nat} :
    (t.relabel (Sum.inl : Nat → Nat ⊕ Fin n)).varFinsetLeft = t.varFinset := by
  induction t <;> simp_all

private theorem substTerm_closed {n : Nat} (t : L.Term (Nat ⊕ Fin n))
    (f : Nat → L.Term Nat) (h : ∀ x ∈ t.varFinsetLeft, (f x).varFinset = ∅) :
    (t.subst (Sum.elim (fun x => (f x).relabel Sum.inl)
      (fun i => .var (.inr i)))).varFinsetLeft = ∅ := by
  revert h
  induction t with
  | var a =>
    intro h
    cases a with
    | inl x => exact (relabelLeft_varFinset (f x)).trans (h x (by simp))
    | inr i => rfl
  | func F ts ih =>
    intro h
    have ht (i) : ((ts i).subst
        (Sum.elim (fun x => (f x).relabel Sum.inl) (fun j => .var (.inr j)))
        ).varFinsetLeft = ∅ := by
      apply ih i
      intro x hx
      exact h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
    simp [ht, Finset.ext_iff]

theorem subst_closed {n : Nat} (φ : L.BoundedFormula Nat n) (f : Nat → L.Term Nat)
    (h : ∀ x ∈ φ.freeVarFinset, (f x).varFinset = ∅) :
    (φ.subst f).freeVarFinset = ∅ := by
  revert h
  induction φ with
  | falsum => intro _; rfl
  | equal t s =>
    intro h
    have ht := substTerm_closed t f (fun x hx => h x (Finset.mem_union_left _ hx))
    have hs := substTerm_closed s f (fun x hx => h x (Finset.mem_union_right _ hx))
    simp [FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Function.comp_def, ht, hs]
  | rel r ts =>
    intro h
    have ht (i) := substTerm_closed (ts i) f
      (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩))
    simp [FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Function.comp_def, ht, Finset.ext_iff]
  | imp φ ψ ihφ ihψ =>
    intro h
    have hφ := ihφ (fun x hx => h x (Finset.mem_union_left _ hx))
    have hψ := ihψ (fun x hx => h x (Finset.mem_union_right _ hx))
    change (φ.subst f).freeVarFinset ∪ (ψ.subst f).freeVarFinset = ∅
    rw [hφ, hψ]
    simp
  | all φ ih => intro h; exact ih h

theorem substituteVariable_closed (x : Nat) (t : L.Term Nat) (ht : t.varFinset = ∅)
    (φ : L.Formula Nat) (hφ : φ.freeVarFinset ⊆ {x}) :
    (substituteVariable x t φ).freeVarFinset = ∅ := by
  apply subst_closed
  intro y hy
  have hyx : y = x := Finset.mem_singleton.mp (hφ hy)
  subst y
  simpa using ht

private theorem bindTerm_closed {n : Nat} (x : Nat) (t : L.Term (Nat ⊕ Fin n))
    (h : t.varFinsetLeft ⊆ {x}) :
    (t.relabel (FirstOrder.Language.BoundedFormula.relabelAux
      (bindVariable x) n)).varFinsetLeft = ∅ := by
  revert h
  induction t with
  | var a =>
    intro h
    cases a with
    | inl y =>
      have hyx : y = x := Finset.mem_singleton.mp (h (by simp))
      subst y
      simp [FirstOrder.Language.BoundedFormula.relabelAux, bindVariable]
    | inr i => simp [FirstOrder.Language.BoundedFormula.relabelAux]
  | func F ts ih =>
    intro h
    have ht (i) := ih i (fun y hy => h
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩))
    simp [ht, Finset.ext_iff]

private theorem bind_closed {n : Nat} (x : Nat) (φ : L.BoundedFormula Nat n)
    (h : φ.freeVarFinset ⊆ {x}) : (φ.relabel (bindVariable x)).freeVarFinset = ∅ := by
  revert h
  induction φ with
  | falsum => intro _; rfl
  | equal t s =>
    intro h
    have ht := bindTerm_closed x t (fun y hy => h (Finset.mem_union_left _ hy))
    have hs := bindTerm_closed x s (fun y hy => h (Finset.mem_union_right _ hy))
    simp [FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.freeVarFinset, ht, hs]
  | rel r ts =>
    intro h
    have ht (i) := bindTerm_closed x (ts i) (fun y hy => h
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩))
    simp [FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.freeVarFinset, ht, Finset.ext_iff]
  | imp φ ψ ihφ ihψ =>
    intro h
    have hφ := ihφ (fun y hy => h (Finset.mem_union_left _ hy))
    have hψ := ihψ (fun y hy => h (Finset.mem_union_right _ hy))
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hφ, hψ]
  | all φ ih =>
    intro h
    rw [FirstOrder.Language.BoundedFormula.relabel_all]
    exact ih h

theorem allVariable_closed (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) : (allVariable x φ).freeVarFinset = ∅ :=
  bind_closed x φ hφ

theorem existsVariable_closed (x : Nat) (φ : L.Formula Nat)
    (hφ : φ.freeVarFinset ⊆ {x}) : (existsVariable x φ).freeVarFinset = ∅ := by
  have hn : φ.not.freeVarFinset ⊆ {x} := by
    simpa only [FirstOrder.Language.BoundedFormula.not,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty] using hφ
  simpa only [existsVariable, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty] using
    allVariable_closed x φ.not hn

end ClosedFormula
end Alexander313.FirstOrderCalculus
