import Alexander313.Alexander.HilbertTermQuotient

/-!
# Literal bounded-formula instances for the Hilbert term model

The first `n` bound-context slots become free variables. Slots introduced by
inner quantifiers remain bound, in their original order. Substituting actual
closed terms then constructs an actual native sentence. The unary opening
and binding theorem is a syntactic equality, rather than a semantic premise.
-/

namespace Alexander313.FirstOrderCalculus.HilbertHenkinSyntax

universe u v w

variable {L : FirstOrder.Language.{u, v}} {α : Type}

def formulaSize : {n : Nat} → L.BoundedFormula α n → Nat
  | _, .falsum => 1
  | _, .equal _ _ => 1
  | _, .rel _ _ => 1
  | _, .imp φ ψ => formulaSize φ + formulaSize ψ + 1
  | _, .all φ => formulaSize φ + 1

@[simp] theorem formulaSize_subst {β : Type} {n : Nat}
    (φ : L.BoundedFormula α n) (f : α → L.Term β) :
    formulaSize (φ.subst f) = formulaSize φ := by
  induction φ <;> simp_all [formulaSize, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]

@[simp] theorem formulaSize_mapFree {β : Type} {n : Nat}
    (φ : L.BoundedFormula α n) (f : α → β) :
    formulaSize (ClosedFormula.mapFree f φ) = formulaSize φ := by
  induction φ <;> simp_all [formulaSize, ClosedFormula.mapFree,
    FirstOrder.Language.BoundedFormula.mapTermRel]

@[simp] theorem formulaSize_sentenceFormula (σ : L.Sentence) :
    formulaSize (sentenceFormula σ) = formulaSize σ := by
  rw [ClosedFormula.sentenceFormula_eq_mapFree, formulaSize_mapFree]

@[simp] theorem formulaSize_sentence (φ : L.Formula Nat) (h : φ.freeVarFinset = ∅) :
    formulaSize (ClosedFormula.sentence φ h) = formulaSize φ := by
  rw [← formulaSize_sentenceFormula, ClosedFormula.sentenceFormula_sentence]

def openVariable (n m : Nat) : α ⊕ Fin (n + m) → (α ⊕ Fin n) ⊕ Fin m
  | .inl a => .inl (.inl a)
  | .inr i => if h : i.val < n then .inl (.inr ⟨i.val, h⟩) else
      .inr ⟨i.val - n, by have hi := i.isLt; omega⟩

def openTerm (n : Nat) {m : Nat} (t : L.Term (α ⊕ Fin (n + m))) :
    L.Term ((α ⊕ Fin n) ⊕ Fin m) := t.relabel (openVariable n m)

def openBoundsAux (n : Nat) : {m : Nat} → L.BoundedFormula α (n + m) →
    L.BoundedFormula (α ⊕ Fin n) m
  | _, .falsum => .falsum
  | _, .equal t s => .equal (openTerm n t) (openTerm n s)
  | _, .rel r ts => .rel r (fun i => openTerm n (ts i))
  | _, .imp φ ψ => (openBoundsAux n φ).imp (openBoundsAux n ψ)
  | m, .all φ => (openBoundsAux n (m := m + 1) φ).all

@[simp] theorem formulaSize_openBoundsAux (n : Nat) {m : Nat}
    (φ : L.BoundedFormula α (n + m)) :
    formulaSize (openBoundsAux n φ) = formulaSize φ := by
  cases φ with
  | falsum => simp only [openBoundsAux, formulaSize]
  | equal _ _ => simp only [openBoundsAux, formulaSize]
  | rel _ _ => simp only [openBoundsAux, formulaSize]
  | imp φ ψ =>
    rw [openBoundsAux]
    exact congrArg₂ (fun a b => a + b + 1)
      (formulaSize_openBoundsAux n φ) (formulaSize_openBoundsAux n ψ)
  | all φ =>
    rw [openBoundsAux]
    exact congrArg (fun a => a + 1) (formulaSize_openBoundsAux n (m := m + 1) φ)
termination_by formulaSize φ
decreasing_by all_goals simp_all [formulaSize] <;> omega

def appendAssignment {D : Type w} {n m : Nat} (xs : Fin n → D) (ys : Fin m → D) :
    Fin (n + m) → D := fun i =>
  if h : i.val < n then xs ⟨i.val, h⟩ else
    ys ⟨i.val - n, by have hi := i.isLt; omega⟩

@[simp] theorem appendAssignment_zero {D : Type w} {n : Nat} (xs : Fin n → D) :
    appendAssignment xs (default : Fin 0 → D) = xs := by
  funext i
  simp [appendAssignment, i.isLt]

theorem appendAssignment_snoc {D : Type w} {n m : Nat}
    (xs : Fin n → D) (ys : Fin m → D) (d : D) :
    appendAssignment xs (Fin.snoc ys d) = Fin.snoc (appendAssignment xs ys) d := by
  funext i
  refine Fin.lastCases (n := n + m) ?_ (fun j => ?_) i
  · have h : ¬n + m < n := by omega
    have hm : (⟨n + m - n, by omega⟩ : Fin (m + 1)) = Fin.last m := by
      apply Fin.ext
      simp
    simp only [appendAssignment, Fin.val_last, dif_neg h, hm, Fin.snoc_last]
    exact (Fin.snoc_last (n := n + m) (α := fun _ => D)
      (p := appendAssignment xs ys) (x := d)).symm
  · by_cases h : j.val < n
    · simp [appendAssignment, h, Fin.snoc_castSucc]
    · have hj : j.val - n < m := by have hi := j.isLt; omega
      have he : (⟨j.val - n, by have hi := j.isLt; omega⟩ : Fin (m + 1)) =
          Fin.castSucc (⟨j.val - n, hj⟩ : Fin m) := rfl
      simp only [Fin.snoc_castSucc, appendAssignment, Fin.val_castSucc, dif_neg h, he]

theorem openTerm_realize {D : Type w} [L.Structure D] (n : Nat) {m : Nat}
    (t : L.Term (α ⊕ Fin (n + m))) (s : α → D) (xs : Fin n → D) (ys : Fin m → D) :
    (openTerm n t).realize (Sum.elim (Sum.elim s xs) ys) =
      t.realize (Sum.elim s (appendAssignment xs ys)) := by
  induction t with
  | var a =>
    cases a with
    | inl a => rfl
    | inr i =>
      by_cases h : i.val < n <;>
        simp [openTerm, openVariable, appendAssignment, FirstOrder.Language.Term.relabel,
          FirstOrder.Language.Term.realize, h]
  | func f ts ih =>
    change FirstOrder.Language.Structure.funMap f
      (fun i => (openTerm n (ts i)).realize (Sum.elim (Sum.elim s xs) ys)) = _
    congr 1
    exact funext ih

theorem openBoundsAux_realize {D : Type w} [L.Structure D] (n : Nat) {m : Nat}
    (φ : L.BoundedFormula α (n + m)) (s : α → D) (xs : Fin n → D) (ys : Fin m → D) :
    (openBoundsAux n φ).Realize (Sum.elim s xs) ys ↔
      φ.Realize s (appendAssignment xs ys) := by
  cases φ with
  | falsum => simp only [openBoundsAux, FirstOrder.Language.BoundedFormula.Realize]
  | equal t u => simp [openBoundsAux, FirstOrder.Language.BoundedFormula.Realize,
      openTerm_realize]
  | rel r ts => simp [openBoundsAux, FirstOrder.Language.BoundedFormula.Realize,
      openTerm_realize]
  | imp φ ψ =>
    simp only [openBoundsAux, FirstOrder.Language.BoundedFormula.realize_imp]
    exact imp_congr (openBoundsAux_realize n φ s xs ys)
      (openBoundsAux_realize n ψ s xs ys)
  | all φ =>
    simp only [openBoundsAux, FirstOrder.Language.BoundedFormula.realize_all]
    apply forall_congr'
    intro d
    exact (openBoundsAux_realize n φ s xs (Fin.snoc ys d)).trans
      (by rw [appendAssignment_snoc])
termination_by formulaSize φ
decreasing_by all_goals simp_all [formulaSize] <;> omega

private theorem mapFreeTerm_realize {β : Type} {D : Type w} [L.Structure D]
    {m : Nat} (f : α → β) (t : L.Term (α ⊕ Fin m)) (s : β → D) (ys : Fin m → D) :
    (t.relabel (Sum.map f id)).realize (Sum.elim s ys) =
      t.realize (Sum.elim (s ∘ f) ys) := by
  induction t with
  | var a => cases a <;> rfl
  | func F ts ih =>
    change FirstOrder.Language.Structure.funMap F
      (fun i => ((ts i).relabel (Sum.map f id)).realize (Sum.elim s ys)) = _
    congr 1
    exact funext ih

theorem mapFree_realize {β : Type} {D : Type w} [L.Structure D]
    {m : Nat} (f : α → β) (φ : L.BoundedFormula α m) (s : β → D) (ys : Fin m → D) :
    (ClosedFormula.mapFree f φ).Realize s ys ↔ φ.Realize (s ∘ f) ys := by
  induction φ with
  | falsum => rfl
  | equal t u => simp only [ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.Realize, mapFreeTerm_realize]
  | rel r ts => simp only [ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.Realize, mapFreeTerm_realize, id_eq]
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ ys) (ihψ ys)
  | all φ ih => exact forall_congr' (fun d => ih (Fin.snoc ys d))

def instanceFormula {n : Nat} (φ : L.BoundedFormula α n)
    (s : α → L.Term Empty) (ts : Fin n → L.Term Empty) : L.Sentence :=
  (openBoundsAux n (m := 0) φ).subst (Sum.elim s ts)

theorem instanceFormula_realize (T : L.Theory) {n : Nat} (φ : L.BoundedFormula α n)
    (s : α → L.Term Empty) (ts : Fin n → L.Term Empty) :
    (instanceFormula φ s ts).Realize (HilbertTermQuotient.Domain T) ↔
      φ.Realize (fun a => HilbertTermQuotient.classOf T (s a))
        (fun i => HilbertTermQuotient.classOf T (ts i)) := by
  change ((openBoundsAux n (m := 0) φ).subst (Sum.elim s ts)).Realize
    (default : Empty → HilbertTermQuotient.Domain T)
    (default : Fin 0 → HilbertTermQuotient.Domain T) ↔ _
  rw [FirstOrder.Language.BoundedFormula.realize_subst]
  have henv : (fun a => (Sum.elim s ts a).realize
      (default : Empty → HilbertTermQuotient.Domain T)) =
      Sum.elim (fun a => HilbertTermQuotient.classOf T (s a))
        (fun i => HilbertTermQuotient.classOf T (ts i)) := by
    funext a
    cases a <;> simp only [Sum.elim_inl, Sum.elim_inr,
      HilbertTermQuotient.closedTerm_realize]
  rw [henv]
  simpa only [appendAssignment_zero] using
    openBoundsAux_realize n φ (fun a => HilbertTermQuotient.classOf T (s a))
      (fun i => HilbertTermQuotient.classOf T (ts i))
      (default : Fin 0 → HilbertTermQuotient.Domain T)

def unaryName (x : Nat) : Empty ⊕ Fin 1 → Nat := Sum.elim Empty.elim (fun _ => x)

def openUnary (x : Nat) (φ : L.BoundedFormula Empty 1) : L.Formula Nat :=
  ClosedFormula.mapFree (unaryName x) (openBoundsAux 1 (m := 0) φ)

private theorem bind_openTerm (x : Nat) {m : Nat} (t : L.Term (Empty ⊕ Fin (1 + m))) :
    ((openTerm 1 t).relabel (Sum.map (unaryName x) id)).relabel
      (FirstOrder.Language.BoundedFormula.relabelAux (bindVariable x) m) =
      t.relabel (Sum.map (Empty.elim : Empty → Nat) id) := by
  induction t with
  | var a =>
    cases a with
    | inl e => exact Empty.elim e
    | inr i =>
      by_cases h : i.val < 1
      · have hi : i.val = 0 := by omega
        simp [openTerm, openVariable, unaryName, FirstOrder.Language.Term.relabel,
          FirstOrder.Language.BoundedFormula.relabelAux, bindVariable, h, hi,
          Fin.ext_iff]
      · have hi : 1 + (i.val - 1) = i.val := by omega
        simp [openTerm, openVariable, unaryName, FirstOrder.Language.Term.relabel,
          FirstOrder.Language.BoundedFormula.relabelAux, h, hi, Fin.ext_iff]
  | func f ts ih =>
    simp only [openTerm, FirstOrder.Language.Term.relabel]
    congr 1
    exact funext ih

private theorem bind_openBoundsAux (x : Nat) {m : Nat}
    (φ : L.BoundedFormula Empty (1 + m)) :
    (ClosedFormula.mapFree (unaryName x) (openBoundsAux 1 φ)).relabel (bindVariable x) =
      ClosedFormula.mapFree (Empty.elim : Empty → Nat) φ := by
  cases φ with
  | falsum => simp only [openBoundsAux, ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel]
  | equal t s =>
    simp only [openBoundsAux, ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel]
    rw [bind_openTerm, bind_openTerm]
  | rel r ts =>
    simp only [openBoundsAux, ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.relabel,
      FirstOrder.Language.BoundedFormula.mapTermRel]
    congr 1
    exact funext (fun i => bind_openTerm x (ts i))
  | imp φ ψ =>
    rw [openBoundsAux]
    simpa only [ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabel_imp] using
      congrArg₂ FirstOrder.Language.BoundedFormula.imp
        (bind_openBoundsAux x φ) (bind_openBoundsAux x ψ)
  | all φ =>
    rw [openBoundsAux, ClosedFormula.mapFree, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabel_all]
    exact congrArg FirstOrder.Language.BoundedFormula.all
      (bind_openBoundsAux x (m := m + 1) φ)
termination_by formulaSize φ
decreasing_by all_goals simp_all [formulaSize] <;> omega

theorem allVariable_openUnary (x : Nat) (φ : L.BoundedFormula Empty 1) :
    allVariable x (openUnary x φ) = sentenceFormula φ.all := by
  rw [ClosedFormula.sentenceFormula_eq_mapFree]
  exact congrArg FirstOrder.Language.BoundedFormula.all (bind_openBoundsAux x (m := 0) φ)

private theorem openUnaryTerm_freeVar (x : Nat) {m : Nat}
    (t : L.Term (Empty ⊕ Fin (1 + m))) :
    ((openTerm 1 t).relabel (Sum.map (unaryName x) id)).varFinsetLeft ⊆ {x} := by
  induction t with
  | var a =>
    cases a with
    | inl e => exact Empty.elim e
    | inr i =>
      by_cases h : i.val < 1 <;>
        simp [openTerm, openVariable, unaryName, FirstOrder.Language.Term.relabel, h]
  | func f ts ih =>
    intro y hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact ih i hi

private theorem openUnaryAux_freeVar (x : Nat) {m : Nat}
    (φ : L.BoundedFormula Empty (1 + m)) :
    (ClosedFormula.mapFree (unaryName x) (openBoundsAux 1 φ)).freeVarFinset ⊆ {x} := by
  cases φ with
  | falsum => simp only [openBoundsAux, ClosedFormula.mapFree,
      FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.empty_subset]
  | equal t s =>
    rw [openBoundsAux]
    exact Finset.union_subset (openUnaryTerm_freeVar x t) (openUnaryTerm_freeVar x s)
  | rel r ts =>
    rw [openBoundsAux]
    intro y hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact openUnaryTerm_freeVar x (ts i) hi
  | imp φ ψ =>
    rw [openBoundsAux]
    exact Finset.union_subset (openUnaryAux_freeVar x φ)
      (openUnaryAux_freeVar x ψ)
  | all φ =>
    rw [openBoundsAux]
    exact openUnaryAux_freeVar x (m := m + 1) φ
termination_by formulaSize φ
decreasing_by all_goals simp_all [formulaSize] <;> omega

theorem openUnary_freeVar (x : Nat) (φ : L.BoundedFormula Empty 1) :
    (openUnary x φ).freeVarFinset ⊆ {x} := openUnaryAux_freeVar x (m := 0) φ

@[simp] theorem formulaSize_openUnary (x : Nat) (φ : L.BoundedFormula Empty 1) :
    formulaSize (openUnary x φ) = formulaSize φ := by
  simp only [openUnary, formulaSize_mapFree, formulaSize_openBoundsAux]

theorem openUnary_realize {D : Type w} [L.Structure D] (x : Nat)
    (φ : L.BoundedFormula Empty 1) (s : Nat → D) (d : D) :
    (openUnary x φ).Realize (Function.update s x d) ↔
      φ.Realize (default : Empty → D) (fun _ => d) := by
  change (ClosedFormula.mapFree (unaryName x) (openBoundsAux 1 (m := 0) φ)).Realize
    (Function.update s x d) (default : Fin 0 → D) ↔ _
  rw [mapFree_realize]
  have he : (Function.update s x d) ∘ unaryName x =
      Sum.elim (default : Empty → D) (fun _ : Fin 1 => d) := by
    funext a
    cases a with
    | inl e => exact Empty.elim e
    | inr i => simp [unaryName, Function.comp_def]
  rw [he]
  simpa only [appendAssignment_zero] using openBoundsAux_realize 1 φ
    (default : Empty → D) (fun _ : Fin 1 => d) (default : Fin 0 → D)

end Alexander313.FirstOrderCalculus.HilbertHenkinSyntax
