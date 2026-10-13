import Alexander313.Alexander.HilbertConstants

/-!
# Finite-proof elimination of genuinely fresh constants

The new nullary symbols are replaced by one free variable. Replacement
commutes with a named quantifier or substitution when that name differs from
the replacement variable. Induction over the actual Hilbert proof constructs
a finite numerical bound avoiding every relevant rule variable. Original
sentence premises are unchanged, so the proof returns to the original theory.

Consequently adding constants is syntactically conservative even when the
original language has no closed term. This is fresh-parameter elimination;
it does not yet assert consistency after adding an existential witness axiom.
-/

namespace Alexander313.FirstOrderCalculus.ConstantExtension

universe u v w z

variable {L : FirstOrder.Language.{u, v}} {C : Type w}

def replaceTerm {α : Type z} (p : α) : (language L C).Term α → L.Term α
  | .var x => .var x
  | .func (.inl f) ts => .func f (fun i => replaceTerm p (ts i))
  | .func (.inr (.constant _)) _ => .var p

def replaceFormula (y : Nat) :
    {n : Nat} → (language L C).BoundedFormula Nat n → L.BoundedFormula Nat n
  | _, .falsum => .falsum
  | _, .equal t s => .equal (replaceTerm (.inl y) t) (replaceTerm (.inl y) s)
  | _, .rel r ts => .rel r (fun i => replaceTerm (.inl y) (ts i))
  | _, .imp φ ψ => .imp (replaceFormula y φ) (replaceFormula y ψ)
  | _, .all φ => .all (replaceFormula y φ)

@[simp] theorem replaceTerm_relabel {α β : Type z} (p : α) (f : α → β)
    (t : (language L C).Term α) :
    replaceTerm (f p) (t.relabel f) = (replaceTerm p t).relabel f := by
  induction t with
  | var x => rfl
  | func a ts ih =>
    cases a with
    | inl a => simp_all [replaceTerm, FirstOrder.Language.Term.relabel]
    | inr a => cases a; rfl

theorem replaceTerm_subst {α β : Type z} (p : α) (q : β)
    (f : α → (language L C).Term β) (t : (language L C).Term α)
    (hf : replaceTerm q (f p) = .var q) :
    replaceTerm q (t.subst f) =
      (replaceTerm p t).subst (fun x => replaceTerm q (f x)) := by
  induction t with
  | var x => rfl
  | func a ts ih =>
    cases a with
    | inl a => simp_all [replaceTerm, FirstOrder.Language.Term.subst]
    | inr a => cases a; exact hf.symm

private theorem replaceTerm_substLift (y : Nat)
    (f : Nat → (language L C).Term Nat)
    (hf : replaceTerm y (f y) = .var y) {n : Nat}
    (t : (language L C).Term (Nat ⊕ Fin n)) :
    replaceTerm (.inl y)
        (t.subst (Sum.elim (fun x => (f x).relabel Sum.inl) (fun i => .var (.inr i)))) =
      (replaceTerm (.inl y) t).subst
        (Sum.elim (fun x => (replaceTerm y (f x)).relabel Sum.inl)
          (fun i => .var (.inr i))) := by
  have hfix : replaceTerm (Sum.inl y : Nat ⊕ Fin n) ((f y).relabel Sum.inl) =
      .var (.inl y) := by
    rw [replaceTerm_relabel]
    simp only [hf, FirstOrder.Language.Term.relabel]
  have h := replaceTerm_subst (Sum.inl y : Nat ⊕ Fin n) (.inl y)
    (Sum.elim (fun x => (f x).relabel Sum.inl) (fun i => .var (.inr i))) t hfix
  have haction :
      (fun x : Nat ⊕ Fin n => replaceTerm (.inl y)
        (Sum.elim (fun z => (f z).relabel Sum.inl) (fun i => .var (.inr i)) x)) =
      Sum.elim (fun x => (replaceTerm y (f x)).relabel Sum.inl)
        (fun i => .var (.inr i)) := by
    funext x
    cases x with
    | inl x => exact replaceTerm_relabel y Sum.inl (f x)
    | inr i => rfl
  rw [haction] at h
  exact h

theorem replaceFormula_subst (y : Nat) (f : Nat → (language L C).Term Nat)
    (hf : replaceTerm y (f y) = .var y) {n : Nat}
    (φ : (language L C).BoundedFormula Nat n) :
    replaceFormula y (φ.subst f) =
      (replaceFormula y φ).subst (fun x => replaceTerm y (f x)) := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp [replaceFormula, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, Function.comp_def,
      replaceTerm_substLift y f hf]
  | rel r ts =>
    simp [replaceFormula, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel, replaceTerm_substLift y f hf,
      Function.comp_def]
  | imp φ ψ ihφ ihψ =>
    exact congrArg₂ FirstOrder.Language.BoundedFormula.imp ihφ ihψ
  | all φ ih =>
    exact congrArg FirstOrder.Language.BoundedFormula.all ih

theorem replaceFormula_relabel (y : Nat) {n d : Nat}
    (f : Nat → Nat ⊕ Fin d) (hf : f y = .inl y)
    (φ : (language L C).BoundedFormula Nat n) :
    replaceFormula y (φ.relabel f) = (replaceFormula y φ).relabel f := by
  have ht {k : Nat} (t : (language L C).Term (Nat ⊕ Fin k)) :
      replaceTerm (.inl y)
          (t.relabel (FirstOrder.Language.BoundedFormula.relabelAux f k)) =
        (replaceTerm (.inl y) t).relabel
          (FirstOrder.Language.BoundedFormula.relabelAux f k) := by
    have h := replaceTerm_relabel (Sum.inl y : Nat ⊕ Fin k)
      (FirstOrder.Language.BoundedFormula.relabelAux f k) t
    simpa [FirstOrder.Language.BoundedFormula.relabelAux, Function.comp_def, hf] using h
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp [replaceFormula, FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, ht]
  | rel r ts =>
    simp [replaceFormula, FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel, ht, Function.comp_def]
  | imp φ ψ ihφ ihψ =>
    simp [replaceFormula, FirstOrder.Language.BoundedFormula.relabel_imp, ihφ, ihψ]
  | all φ ih =>
    rw [FirstOrder.Language.BoundedFormula.relabel_all]
    simp [replaceFormula, FirstOrder.Language.BoundedFormula.relabel_all, ih]

@[simp] theorem replaceFormula_falsum (y : Nat) {n : Nat} :
    replaceFormula y (⊥ : (language L C).BoundedFormula Nat n) =
      (⊥ : L.BoundedFormula Nat n) := rfl

@[simp] theorem replaceFormula_imp (y : Nat) {n : Nat}
    (φ ψ : (language L C).BoundedFormula Nat n) :
    replaceFormula y (φ.imp ψ) = (replaceFormula y φ).imp (replaceFormula y ψ) := rfl

@[simp] theorem replaceFormula_not (y : Nat) {n : Nat}
    (φ : (language L C).BoundedFormula Nat n) :
    replaceFormula y φ.not = (replaceFormula y φ).not := rfl

@[simp] theorem replaceFormula_termEqual (y : Nat)
    (t s : (language L C).Term Nat) :
    replaceFormula y (t.equal s) = (replaceTerm y t).equal (replaceTerm y s) := by
  change FirstOrder.Language.BoundedFormula.equal (replaceTerm (.inl y) (t.relabel Sum.inl))
      (replaceTerm (.inl y) (s.relabel Sum.inl)) =
    FirstOrder.Language.BoundedFormula.equal
      ((replaceTerm y t).relabel Sum.inl) ((replaceTerm y s).relabel Sum.inl)
  rw [replaceTerm_relabel, replaceTerm_relabel]

theorem replaceFormula_allVariable (y x : Nat) (hxy : x ≠ y)
    (φ : (language L C).Formula Nat) :
    replaceFormula y (allVariable x φ) = allVariable x (replaceFormula y φ) := by
  unfold allVariable
  change (replaceFormula y
    (FirstOrder.Language.BoundedFormula.relabel (bindVariable x) φ)).all = _
  rw [replaceFormula_relabel y (bindVariable x)
    (by simp [bindVariable, Ne.symm hxy])]

theorem replaceFormula_substituteVariable (y x : Nat) (hxy : x ≠ y)
    (t : (language L C).Term Nat) (φ : (language L C).Formula Nat) :
    replaceFormula y (substituteVariable x t φ) =
      substituteVariable x (replaceTerm y t) (replaceFormula y φ) := by
  unfold substituteVariable
  rw [replaceFormula_subst y _ (by simp [Ne.symm hxy, replaceTerm])]
  congr 1
  funext z
  split_ifs <;> rfl

theorem replaceTerm_not_mem (y x : Nat) (hxy : x ≠ y) {n : Nat}
    (t : (language L C).Term (Nat ⊕ Fin n)) (hx : x ∉ t.varFinsetLeft) :
    x ∉ (replaceTerm (.inl y) t).varFinsetLeft := by
  revert hx
  induction t with
  | var a =>
    intro hx
    cases a <;> simpa only [replaceTerm, FirstOrder.Language.Term.varFinsetLeft] using hx
  | func a ts ih =>
    intro hx
    cases a with
    | inl a =>
      have ht (i) : x ∉ (ts i).varFinsetLeft := fun h =>
        hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
      simpa only [replaceTerm] using
        (show x ∉ (FirstOrder.Language.Term.func a
          (fun i => replaceTerm (.inl y) (ts i))).varFinsetLeft from by
            simp [fun i => ih i (ht i)])
    | inr a => cases a; simp [replaceTerm, hxy]

theorem replaceFormula_not_mem (y x : Nat) (hxy : x ≠ y) {n : Nat}
    (φ : (language L C).BoundedFormula Nat n) (hx : x ∉ φ.freeVarFinset) :
    x ∉ (replaceFormula y φ).freeVarFinset := by
  revert hx
  induction φ with
  | falsum => intro _; simp [replaceFormula]
  | equal t s =>
    intro hx
    have ht : x ∉ t.varFinsetLeft := fun h => hx (Finset.mem_union_left _ h)
    have hs : x ∉ s.varFinsetLeft := fun h => hx (Finset.mem_union_right _ h)
    simp [replaceFormula, replaceTerm_not_mem y x hxy t ht,
      replaceTerm_not_mem y x hxy s hs]
  | rel r ts =>
    intro hx
    have ht (i) : x ∉ (ts i).varFinsetLeft := fun h =>
      hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
    simp [replaceFormula, fun i => replaceTerm_not_mem y x hxy (ts i) (ht i)]
  | imp φ ψ ihφ ihψ =>
    intro hx
    have hφ : x ∉ φ.freeVarFinset := fun h => hx (Finset.mem_union_left _ h)
    have hψ : x ∉ ψ.freeVarFinset := fun h => hx (Finset.mem_union_right _ h)
    simp [replaceFormula, ihφ hφ, ihψ hψ]
  | all φ ih => intro hx; exact ih hx

@[simp] theorem replaceTerm_embed (p : Nat) {n : Nat} (t : L.Term (Nat ⊕ Fin n)) :
    replaceTerm (.inl p) (embedTerm (C := C) t) = t := by
  induction t <;> simp_all [embedTerm, inclusion, SymbolMap.termMap, replaceTerm]

@[simp] theorem replaceFormula_embed (y : Nat) {n : Nat} (φ : L.BoundedFormula Nat n) :
    replaceFormula y (embed (C := C) φ) = φ := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    exact congrArg₂ FirstOrder.Language.BoundedFormula.equal
      (replaceTerm_embed y t) (replaceTerm_embed y s)
  | rel r ts =>
    change FirstOrder.Language.BoundedFormula.rel r
      (fun i => replaceTerm (.inl y) (embedTerm (ts i))) = .rel r ts
    congr 1
    funext i
    exact replaceTerm_embed y (ts i)
  | imp φ ψ ihφ ihψ => exact congrArg₂ FirstOrder.Language.BoundedFormula.imp ihφ ihψ
  | all φ ih => exact congrArg FirstOrder.Language.BoundedFormula.all ih

theorem logical_replacement_bound {φ : (language L C).Formula Nat}
    (h : LogicalAxiom φ) :
    ∃ N : Nat, ∀ y, N ≤ y → LogicalAxiom (replaceFormula y φ) := by
  cases h with
  | k φ ψ => exact ⟨0, fun _ _ => .k _ _⟩
  | s φ ψ χ => exact ⟨0, fun _ _ => .s _ _ _⟩
  | classical φ ψ => exact ⟨0, fun _ _ => .classical _ _⟩
  | allElim x t φ =>
    refine ⟨x + 1, ?_⟩
    intro y hy
    have hxy : x ≠ y := by omega
    simpa only [replaceFormula_imp, replaceFormula_allVariable y x hxy,
      replaceFormula_substituteVariable y x hxy] using
      LogicalAxiom.allElim x (replaceTerm y t) (replaceFormula y φ)
  | allDist x φ ψ =>
    refine ⟨x + 1, ?_⟩
    intro y hy
    have hxy : x ≠ y := by omega
    simpa only [replaceFormula_imp, replaceFormula_allVariable y x hxy] using
      LogicalAxiom.allDist x (replaceFormula y φ) (replaceFormula y ψ)
  | vacuous x φ hx =>
    refine ⟨x + 1, ?_⟩
    intro y hy
    have hxy : x ≠ y := by omega
    simpa only [replaceFormula_imp, replaceFormula_allVariable y x hxy] using
      LogicalAxiom.vacuous x (replaceFormula y φ) (replaceFormula_not_mem y x hxy φ hx)
  | eqRefl t =>
    refine ⟨0, ?_⟩
    intro y _
    simpa only [replaceFormula_termEqual] using
      (LogicalAxiom.eqRefl (replaceTerm y t))
  | eqSubst x t s φ =>
    refine ⟨x + 1, ?_⟩
    intro y hy
    have hxy : x ≠ y := by omega
    simpa only [replaceFormula_imp, replaceFormula_termEqual,
      replaceFormula_substituteVariable y x hxy] using
      LogicalAxiom.eqSubst x (replaceTerm y t) (replaceTerm y s) (replaceFormula y φ)

/-- The fresh-variable bound is constructed from the finite proof itself. -/
theorem derivation_replacement_bound {T : L.Theory}
    {φ : (language L C).Formula Nat} (h : Derivation (embedTheory T) φ) :
    ∃ N : Nat, ∀ y, N ≤ y → Derivation T (replaceFormula y φ) := by
  induction h with
  | logical h =>
    obtain ⟨N, hN⟩ := logical_replacement_bound h
    exact ⟨N, fun y hy => .logical (hN y hy)⟩
  | theory σ hσ =>
    obtain ⟨τ, hτ, rfl⟩ := hσ
    refine ⟨0, ?_⟩
    intro y _
    change Derivation T (replaceFormula y (sentenceFormula (embed τ)))
    rw [← embed_sentenceFormula, replaceFormula_embed]
    exact .theory τ hτ
  | mp hp hq ihp ihq =>
    obtain ⟨N, hN⟩ := ihp
    obtain ⟨M, hM⟩ := ihq
    exact ⟨max N M, fun y hy => .mp
      (hN y (le_trans (Nat.le_max_left _ _) hy))
      (hM y (le_trans (Nat.le_max_right _ _) hy))⟩
  | generalize x h ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max N (x + 1), ?_⟩
    intro y hy
    have hxy : x ≠ y := by have := le_trans (Nat.le_max_right N (x + 1)) hy; omega
    rw [replaceFormula_allVariable y x hxy]
    exact .generalize x (hN y (le_trans (Nat.le_max_left _ _) hy))

theorem derivation_freshConstants_iff (T : L.Theory) (φ : L.Formula Nat) :
    Derivation (embedTheory (C := C) T) (embed φ) ↔ Derivation T φ := by
  refine ⟨fun h => ?_, derivation_embed⟩
  obtain ⟨N, hN⟩ := derivation_replacement_bound h
  simpa only [replaceFormula_embed] using hN N le_rfl

theorem consistent_freshConstants_iff (T : L.Theory) :
    Consistent (embedTheory (C := C) T) ↔ Consistent T := by
  change (¬Derivation (embedTheory T) (embed (⊥ : L.Formula Nat))) ↔
    ¬Derivation T (⊥ : L.Formula Nat)
  exact not_congr (derivation_freshConstants_iff T ⊥)

end Alexander313.FirstOrderCalculus.ConstantExtension
