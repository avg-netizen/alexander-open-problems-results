import Alexander313.Alexander.WeakSemantics

/-!
# Alphabetic invariance after literal numeral closure

Alpha forms retain free variable names and use de Bruijn indices only for
bound occurrences. Numerical closure commutes with this representation.
Weak, capture-safe variable substitution commutes literally with numerical
closure. These are syntax proofs, independent of predicate soundness.
-/

namespace Alexander313

namespace AlphaTerm

def numeral : Nat → AlphaTerm
  | 0 => .zero
  | n + 1 => .succ (numeral n)

def freeVars : AlphaTerm → Finset Nat
  | .free x => {x}
  | .bound _ => ∅
  | .zero => ∅
  | .succ t => t.freeVars
  | .add t u => t.freeVars ∪ u.freeVars
  | .mul t u => t.freeVars ∪ u.freeVars

def substFree (σ : NumericalSubstitution) : AlphaTerm → AlphaTerm
  | .free x => match σ x with
    | none => .free x
    | some n => numeral n
  | .bound i => .bound i
  | .zero => .zero
  | .succ t => .succ (t.substFree σ)
  | .add t u => .add (t.substFree σ) (u.substFree σ)
  | .mul t u => .mul (t.substFree σ) (u.substFree σ)

theorem substFree_eq_of_agree (t : AlphaTerm) (σ τ : NumericalSubstitution)
    (h : ∀ x ∈ t.freeVars, σ x = τ x) : t.substFree σ = t.substFree τ := by
  induction t with
  | free x => simp only [substFree, h x (Finset.mem_singleton_self x)]
  | bound i => rfl
  | zero => rfl
  | succ t ih => exact congrArg AlphaTerm.succ (ih h)
  | add t u iht ihu =>
    simp only [substFree, iht (fun x hx => h x (Finset.mem_union_left _ hx)),
      ihu (fun x hx => h x (Finset.mem_union_right _ hx))]
  | mul t u iht ihu =>
    simp only [substFree, iht (fun x hx => h x (Finset.mem_union_left _ hx)),
      ihu (fun x hx => h x (Finset.mem_union_right _ hx))]

end AlphaTerm

namespace AlphaFormula

variable {Owner : Type}

def freeVars : AlphaFormula Owner → Finset Nat
  | .falsum => ∅
  | .equal t u => t.freeVars ∪ u.freeVars
  | .imp φ ψ => φ.freeVars ∪ ψ.freeVars
  | .conj φ ψ => φ.freeVars ∪ ψ.freeVars
  | .disj φ ψ => φ.freeVars ∪ ψ.freeVars
  | .neg φ => φ.freeVars
  | .all φ => φ.freeVars
  | .ex φ => φ.freeVars
  | .know _ φ => φ.freeVars

def substFree (σ : NumericalSubstitution) : AlphaFormula Owner → AlphaFormula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.substFree σ) (u.substFree σ)
  | .imp φ ψ => .imp (φ.substFree σ) (ψ.substFree σ)
  | .conj φ ψ => .conj (φ.substFree σ) (ψ.substFree σ)
  | .disj φ ψ => .disj (φ.substFree σ) (ψ.substFree σ)
  | .neg φ => .neg (φ.substFree σ)
  | .all φ => .all (φ.substFree σ)
  | .ex φ => .ex (φ.substFree σ)
  | .know a φ => .know a (φ.substFree σ)

theorem substFree_eq_of_agree (φ : AlphaFormula Owner) (σ τ : NumericalSubstitution)
    (h : ∀ x ∈ φ.freeVars, σ x = τ x) : φ.substFree σ = φ.substFree τ := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    simp only [substFree,
      AlphaTerm.substFree_eq_of_agree t σ τ (fun x hx => h x (Finset.mem_union_left _ hx)),
      AlphaTerm.substFree_eq_of_agree u σ τ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | imp φ ψ ihφ ihψ =>
    simp only [substFree, ihφ (fun x hx => h x (Finset.mem_union_left _ hx)),
      ihψ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | conj φ ψ ihφ ihψ =>
    simp only [substFree, ihφ (fun x hx => h x (Finset.mem_union_left _ hx)),
      ihψ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | disj φ ψ ihφ ihψ =>
    simp only [substFree, ihφ (fun x hx => h x (Finset.mem_union_left _ hx)),
      ihψ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | neg φ ih => exact congrArg AlphaFormula.neg (ih h)
  | all φ ih => exact congrArg AlphaFormula.all (ih h)
  | ex φ ih => exact congrArg AlphaFormula.ex (ih h)
  | know a φ ih => exact congrArg (AlphaFormula.know a) (ih h)

end AlphaFormula

namespace Term

@[simp] theorem alpha_numeral (n : Nat) (bound : List Nat) :
    (numeral n).alpha bound = AlphaTerm.numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [numeral, alpha, AlphaTerm.numeral] using congrArg AlphaTerm.succ ih

theorem mem_freeVars_alpha (t : Term) (bound : List Nat) (v : Nat) :
    v ∈ (t.alpha bound).freeVars ↔ v ∈ t.freeVars ∧ v ∉ bound := by
  induction t with
  | var x =>
    by_cases hx : x ∈ bound <;> simp_all [alpha, freeVars, AlphaTerm.freeVars]
  | zero => simp [alpha, freeVars, AlphaTerm.freeVars]
  | succ t ih => simpa only [alpha, freeVars, AlphaTerm.freeVars] using ih
  | add t u iht ihu =>
    simp only [alpha, freeVars, AlphaTerm.freeVars, Finset.mem_union, iht, ihu]
    tauto
  | mul t u iht ihu =>
    simp only [alpha, freeVars, AlphaTerm.freeVars, Finset.mem_union, iht, ihu]
    tauto

theorem alpha_subst (t : Term) (bound : List Nat) (σ : NumericalSubstitution)
    (h : ∀ x ∈ bound, σ x = none) :
    (t.subst σ).alpha bound = (t.alpha bound).substFree σ := by
  induction t with
  | var x =>
    by_cases hx : x ∈ bound
    · simp [subst, alpha, hx, h x hx, AlphaTerm.substFree]
    · cases hσ : σ x <;> simp [subst, alpha, hx, hσ, AlphaTerm.substFree]
  | zero => rfl
  | succ t ih => simp only [subst, alpha, AlphaTerm.substFree, ih]
  | add t u iht ihu => simp only [subst, alpha, AlphaTerm.substFree, iht, ihu]
  | mul t u iht ihu => simp only [subst, alpha, AlphaTerm.substFree, iht, ihu]

theorem substTerm_var_subst (t : Term) (x y : Nat) (σ : NumericalSubstitution)
    (n : Nat) (hy : σ y = some n) :
    (Term.substTerm x (.var y) t).subst σ = t.subst (Function.update σ x (some n)) := by
  induction t with
  | var z =>
    by_cases hzx : z = x <;> simp [substTerm, subst, hzx, hy]
  | zero => rfl
  | succ t ih => simp only [substTerm, subst, ih]
  | add t u iht ihu => simp only [substTerm, subst, iht, ihu]
  | mul t u iht ihu => simp only [substTerm, subst, iht, ihu]

end Term

namespace Formula

variable {Owner : Type}

theorem mem_freeVars_alpha (φ : Formula Owner) (bound : List Nat) (v : Nat) :
    v ∈ (φ.alpha bound).freeVars ↔ v ∈ φ.freeVars ∧ v ∉ bound := by
  induction φ generalizing bound with
  | falsum => simp [alpha, freeVars, AlphaFormula.freeVars]
  | equal t u =>
    simp only [alpha, freeVars, AlphaFormula.freeVars, Finset.mem_union, Term.mem_freeVars_alpha]
    tauto
  | imp φ ψ ihφ ihψ =>
    simp only [alpha, freeVars, AlphaFormula.freeVars, Finset.mem_union, ihφ, ihψ]
    tauto
  | conj φ ψ ihφ ihψ =>
    simp only [alpha, freeVars, AlphaFormula.freeVars, Finset.mem_union, ihφ, ihψ]
    tauto
  | disj φ ψ ihφ ihψ =>
    simp only [alpha, freeVars, AlphaFormula.freeVars, Finset.mem_union, ihφ, ihψ]
    tauto
  | neg φ ih => simpa only [alpha, freeVars, AlphaFormula.freeVars] using ih bound
  | know a φ ih => simpa only [alpha, freeVars, AlphaFormula.freeVars] using ih bound
  | all x φ ih =>
    simp only [alpha, freeVars, AlphaFormula.freeVars, ih, Finset.mem_erase, List.mem_cons]
    tauto
  | ex x φ ih =>
    simp only [alpha, freeVars, AlphaFormula.freeVars, ih, Finset.mem_erase, List.mem_cons]
    tauto

@[simp] theorem freeVars_alpha_nil (φ : Formula Owner) :
    (φ.alpha []).freeVars = φ.freeVars := by
  ext v
  simp [mem_freeVars_alpha]

theorem AlphaEquivalent.freeVars_eq {φ ψ : Formula Owner}
    (h : φ.AlphaEquivalent ψ) : φ.freeVars = ψ.freeVars := by
  simpa only [freeVars_alpha_nil] using congrArg AlphaFormula.freeVars h

theorem alpha_subst (φ : Formula Owner) (bound : List Nat) (σ : NumericalSubstitution)
    (h : ∀ x ∈ bound, σ x = none) :
    (φ.subst σ).alpha bound = (φ.alpha bound).substFree σ := by
  induction φ generalizing bound σ with
  | falsum => rfl
  | equal t u =>
    simp only [subst, alpha, AlphaFormula.substFree,
      Term.alpha_subst t bound σ h, Term.alpha_subst u bound σ h]
  | imp φ ψ ihφ ihψ => simp only [subst, alpha, AlphaFormula.substFree, ihφ bound σ h, ihψ bound σ h]
  | conj φ ψ ihφ ihψ => simp only [subst, alpha, AlphaFormula.substFree, ihφ bound σ h, ihψ bound σ h]
  | disj φ ψ ihφ ihψ => simp only [subst, alpha, AlphaFormula.substFree, ihφ bound σ h, ihψ bound σ h]
  | neg φ ih => simp only [subst, alpha, AlphaFormula.substFree, ih bound σ h]
  | know a φ ih => simp only [subst, alpha, AlphaFormula.substFree, ih bound σ h]
  | all x φ ih =>
    have hr : ∀ v ∈ x :: bound, σ.remove x v = none := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [NumericalSubstitution.remove]
      · by_cases hvx : v = x <;> simp [NumericalSubstitution.remove, hvx, h v hv]
    have ha : (φ.alpha (x :: bound)).substFree (σ.remove x) =
        (φ.alpha (x :: bound)).substFree σ := by
      apply AlphaFormula.substFree_eq_of_agree
      intro v hv
      have hnot := (mem_freeVars_alpha φ (x :: bound) v).mp hv
      have hvx : v ≠ x := fun heq => hnot.2 (List.mem_cons.mpr (Or.inl heq))
      simp [NumericalSubstitution.remove, hvx]
    simp only [subst, alpha, AlphaFormula.substFree, ih (x :: bound) (σ.remove x) hr, ha]
  | ex x φ ih =>
    have hr : ∀ v ∈ x :: bound, σ.remove x v = none := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [NumericalSubstitution.remove]
      · by_cases hvx : v = x <;> simp [NumericalSubstitution.remove, hvx, h v hv]
    have ha : (φ.alpha (x :: bound)).substFree (σ.remove x) =
        (φ.alpha (x :: bound)).substFree σ := by
      apply AlphaFormula.substFree_eq_of_agree
      intro v hv
      have hnot := (mem_freeVars_alpha φ (x :: bound) v).mp hv
      have hvx : v ≠ x := fun heq => hnot.2 (List.mem_cons.mpr (Or.inl heq))
      simp [NumericalSubstitution.remove, hvx]
    simp only [subst, alpha, AlphaFormula.substFree, ih (x :: bound) (σ.remove x) hr, ha]

theorem AlphaEquivalent.subst {φ ψ : Formula Owner} (h : φ.AlphaEquivalent ψ)
    (σ : NumericalSubstitution) : (φ.subst σ).AlphaEquivalent (ψ.subst σ) := by
  unfold AlphaEquivalent at h ⊢
  rw [alpha_subst φ [] σ (by simp), alpha_subst ψ [] σ (by simp)]
  exact congrArg (AlphaFormula.substFree σ) h

theorem AlphaEquivalent.close {φ ψ : Formula Owner} (h : φ.AlphaEquivalent ψ)
    (s : Assignment) : (φ.close s).AlphaEquivalent (ψ.close s) := h.subst _

theorem substVar_subst (φ : Formula Owner) (x y : Nat) (σ : NumericalSubstitution)
    (n : Nat) (hy : σ y = some n) (h : φ.VarSubstitutable x y) :
    (φ.substVar x y).subst σ = φ.subst (Function.update σ x (some n)) := by
  induction φ generalizing σ with
  | falsum => rfl
  | equal t u => simp only [substVar, substTerm, subst,
      Term.substTerm_var_subst t x y σ n hy, Term.substTerm_var_subst u x y σ n hy]
  | imp φ ψ ihφ ihψ => exact congrArg₂ Formula.imp (ihφ σ hy h.1) (ihψ σ hy h.2)
  | conj φ ψ ihφ ihψ => exact congrArg₂ Formula.conj (ihφ σ hy h.1) (ihψ σ hy h.2)
  | disj φ ψ ihφ ihψ => exact congrArg₂ Formula.disj (ihφ σ hy h.1) (ihψ σ hy h.2)
  | neg φ ih => exact congrArg Formula.neg (ih σ hy h)
  | know a φ ih => exact congrArg (Formula.know a) (ih σ hy h)
  | all z φ ih =>
    by_cases hzx : z = x
    · subst z
      simp only [substVar, substTerm, ite_true, subst, NumericalSubstitution.remove_update_self]
    · have hb := h.resolve_left hzx
      rcases hb.1 with hzy | hx
      · have hy' : σ.remove z y = some n := by
          simp [NumericalSubstitution.remove, Ne.symm hzy, hy]
        simp only [substVar, substTerm, if_neg hzx, subst,
          NumericalSubstitution.remove_update_of_ne σ x z _ (Ne.symm hzx)]
        exact congrArg (Formula.all z) (ih (σ.remove z) hy' hb.2)
      · have hwhole : x ∉ (Formula.all z φ).freeVars := fun hm =>
          hx (Finset.mem_erase.mp hm).2
        rw [substVar, substTerm_eq_self_of_notMem _ x (.var y) hwhole]
        apply subst_eq_of_agree
        intro v hv
        have hvx : v ≠ x := fun heq => hwhole (heq ▸ hv)
        simp [hvx]
  | ex z φ ih =>
    by_cases hzx : z = x
    · subst z
      simp only [substVar, substTerm, ite_true, subst, NumericalSubstitution.remove_update_self]
    · have hb := h.resolve_left hzx
      rcases hb.1 with hzy | hx
      · have hy' : σ.remove z y = some n := by
          simp [NumericalSubstitution.remove, Ne.symm hzy, hy]
        simp only [substVar, substTerm, if_neg hzx, subst,
          NumericalSubstitution.remove_update_of_ne σ x z _ (Ne.symm hzx)]
        exact congrArg (Formula.ex z) (ih (σ.remove z) hy' hb.2)
      · have hwhole : x ∉ (Formula.ex z φ).freeVars := fun hm =>
          hx (Finset.mem_erase.mp hm).2
        rw [substVar, substTerm_eq_self_of_notMem _ x (.var y) hwhole]
        apply subst_eq_of_agree
        intro v hv
        have hvx : v ≠ x := fun heq => hwhole (heq ▸ hv)
        simp [hvx]

theorem close_substVar (φ : Formula Owner) (x y : Nat) (s : Assignment)
    (h : φ.VarSubstitutable x y) :
    (φ.substVar x y).close s = φ.close (Function.update s x (s y)) := by
  have hσ : Function.update (fun v => some (s v)) x (some (s y)) =
      (fun v => some (Function.update s x (s y) v)) := by
    funext v
    by_cases hvx : v = x <;> simp [hvx]
  simpa only [close, hσ] using substVar_subst φ x y (fun v => some (s v)) (s y) rfl h

end Formula

/-- A natural property of consequence predicates on sentences. It is an
    explicit premise until established for the constructed source theories. -/
def RawAlphabetic {Owner : Type} (P : RawPredicates Owner) : Prop :=
  ∀ a φ ψ, φ.Closed → ψ.Closed → φ.AlphaEquivalent ψ → (P a φ ↔ P a ψ)

def actualModelOfAlphabetic {Owner : Type} (P : RawPredicates Owner)
    (hP : RawAlphabetic P) : ModalModel Owner Nat where
  zero := 0
  succ := fun n => n + 1
  add := Nat.add
  mul := Nat.mul
  modal := fun a φ s => P a (φ.close s)
  free_independence := by
    intro a φ s t h
    rw [φ.close_eq_of_agree s t h]
  alphabetic := fun a φ ψ s h =>
    hP a _ _ (φ.close_closed s) (ψ.close_closed s) (h.close s)
  weak_substitution := by
    intro a φ x y s h
    rw [φ.close_substVar x y s h]

def ActualRealization.ofAlphabetic {Owner : Type} (P : RawPredicates Owner)
    (hP : RawAlphabetic P) : ActualRealization P where
  model := actualModelOfAlphabetic P hP
  zero_correct := rfl
  succ_correct := fun _ => rfl
  add_correct := fun _ _ => rfl
  mul_correct := fun _ _ => rfl
  modal_correct := fun a φ s => by simp [actualModelOfAlphabetic, truth]

end Alexander313
