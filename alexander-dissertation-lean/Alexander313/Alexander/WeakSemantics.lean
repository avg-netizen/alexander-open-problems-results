import Alexander313.Alexander.BaseLogic
import Alexander313.FreeVariables

/-!
# Free assignments and the weak variable-substitution lemma

These statements hold in every admissible Alexander structure. Only a
variable is substituted in the modal substitution lemma, as required by
Definition 1.2.3. No arbitrary-term modal rule is asserted.
-/

namespace Alexander313

theorem generalTermEval_eq_of_agree {Owner D : Type} (M : ModalModel Owner D)
    (t : Term) (s u : Nat → D)
    (h : ∀ v ∈ t.freeVars, s v = u v) :
    generalTermEval M s t = generalTermEval M u t := by
  induction t with
  | var x => exact h x (by simp [Term.freeVars])
  | zero => rfl
  | succ t ih => exact congrArg M.succ (ih h)
  | add t u iht ihu =>
    exact congrArg₂ M.add
      (iht (fun v hv => h v (Finset.mem_union_left _ hv)))
      (ihu (fun v hv => h v (Finset.mem_union_right _ hv)))
  | mul t u iht ihu =>
    exact congrArg₂ M.mul
      (iht (fun v hv => h v (Finset.mem_union_left _ hv)))
      (ihu (fun v hv => h v (Finset.mem_union_right _ hv)))

theorem generalTruth_eq_of_agree {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (s t : Nat → D)
    (h : ∀ v ∈ φ.freeVars, s v = t v) :
    generalTruth M φ s ↔ generalTruth M φ t := by
  induction φ generalizing s t with
  | falsum => rfl
  | equal u v =>
    have hu := generalTermEval_eq_of_agree M u s t
      (fun x hx => h x (Finset.mem_union_left _ hx))
    have hv := generalTermEval_eq_of_agree M v s t
      (fun x hx => h x (Finset.mem_union_right _ hx))
    simp only [generalTruth, hu, hv]
  | imp φ ψ ihφ ihψ =>
    have hφ := ihφ s t (fun v hv => h v (Finset.mem_union_left _ hv))
    have hψ := ihψ s t (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [generalTruth, hφ, hψ]
  | conj φ ψ ihφ ihψ =>
    have hφ := ihφ s t (fun v hv => h v (Finset.mem_union_left _ hv))
    have hψ := ihψ s t (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [generalTruth, hφ, hψ]
  | disj φ ψ ihφ ihψ =>
    have hφ := ihφ s t (fun v hv => h v (Finset.mem_union_left _ hv))
    have hψ := ihψ s t (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [generalTruth, hφ, hψ]
  | neg φ ih => exact not_congr (ih s t h)
  | all x φ ih =>
    apply forall_congr'
    intro n
    apply ih
    intro v hv
    by_cases hvx : v = x
    · subst v
      simp
    · simpa only [Function.update_of_ne hvx] using
        h v (Finset.mem_erase.mpr ⟨hvx, hv⟩)
  | ex x φ ih =>
    apply exists_congr
    intro n
    apply ih
    intro v hv
    by_cases hvx : v = x
    · subst v
      simp
    · simpa only [Function.update_of_ne hvx] using
        h v (Finset.mem_erase.mpr ⟨hvx, hv⟩)
  | know a φ _ => exact M.free_independence a φ s t h

theorem Term.substTerm_eq_self_of_notMem (t : Term) (x : Nat) (u : Term)
    (hx : x ∉ t.freeVars) : Term.substTerm x u t = t := by
  induction t with
  | var z =>
    have hzx : z ≠ x := by
      intro h
      subst z
      exact hx (Finset.mem_singleton_self x)
    simp only [substTerm, if_neg hzx]
  | zero => rfl
  | succ t ih => exact congrArg Term.succ (ih hx)
  | add t v iht ihv =>
    have ht : x ∉ t.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hv : x ∉ v.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp only [substTerm, iht ht, ihv hv]
  | mul t v iht ihv =>
    have ht : x ∉ t.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hv : x ∉ v.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp only [substTerm, iht ht, ihv hv]

theorem Formula.substTerm_eq_self_of_notMem {Owner : Type} (φ : Formula Owner)
    (x : Nat) (u : Term) (hx : x ∉ φ.freeVars) : φ.substTerm x u = φ := by
  induction φ with
  | falsum => rfl
  | equal t v =>
    have ht : x ∉ t.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hv : x ∉ v.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp only [substTerm, Term.substTerm_eq_self_of_notMem t x u ht,
      Term.substTerm_eq_self_of_notMem v x u hv]
  | imp φ ψ ihφ ihψ =>
    have hφ : x ∉ φ.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hψ : x ∉ ψ.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp only [substTerm, ihφ hφ, ihψ hψ]
  | conj φ ψ ihφ ihψ =>
    have hφ : x ∉ φ.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hψ : x ∉ ψ.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp only [substTerm, ihφ hφ, ihψ hψ]
  | disj φ ψ ihφ ihψ =>
    have hφ : x ∉ φ.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hψ : x ∉ ψ.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp only [substTerm, ihφ hφ, ihψ hψ]
  | neg φ ih => exact congrArg Formula.neg (ih hx)
  | know a φ ih => exact congrArg (Formula.know a) (ih hx)
  | all z φ ih =>
    by_cases hzx : z = x
    · simp only [substTerm, if_pos hzx]
    · have hφ : x ∉ φ.freeVars := fun h =>
        hx (Finset.mem_erase.mpr ⟨Ne.symm hzx, h⟩)
      simp only [substTerm, if_neg hzx, ih hφ]
  | ex z φ ih =>
    by_cases hzx : z = x
    · simp only [substTerm, if_pos hzx]
    · have hφ : x ∉ φ.freeVars := fun h =>
        hx (Finset.mem_erase.mpr ⟨Ne.symm hzx, h⟩)
      simp only [substTerm, if_neg hzx, ih hφ]

theorem generalTermEval_substVar {Owner D : Type} (M : ModalModel Owner D)
    (t : Term) (x y : Nat) (s : Nat → D) :
    generalTermEval M s (Term.substTerm x (.var y) t) =
      generalTermEval M (Function.update s x (s y)) t := by
  induction t with
  | var z =>
    by_cases hzx : z = x <;> simp [Term.substTerm, generalTermEval, hzx]
  | zero => rfl
  | succ t ih => simp only [Term.substTerm, generalTermEval, ih]
  | add t u iht ihu => simp only [Term.substTerm, generalTermEval, iht, ihu]
  | mul t u iht ihu => simp only [Term.substTerm, generalTermEval, iht, ihu]

theorem generalTruth_substVar_of_notMem {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (x y : Nat) (s : Nat → D) (hx : x ∉ φ.freeVars) :
    generalTruth M (φ.substVar x y) s ↔
      generalTruth M φ (Function.update s x (s y)) := by
  rw [Formula.substVar, Formula.substTerm_eq_self_of_notMem φ x (.var y) hx]
  apply generalTruth_eq_of_agree
  intro v hv
  have hvx : v ≠ x := by
    intro h
    subst v
    exact hx hv
  simp [hvx]

theorem generalTruth_substVar {Owner D : Type} (M : ModalModel Owner D)
    (φ : Formula Owner) (x y : Nat) (s : Nat → D) (h : φ.VarSubstitutable x y) :
    generalTruth M (φ.substVar x y) s ↔
      generalTruth M φ (Function.update s x (s y)) := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u =>
    simp only [Formula.substVar, Formula.substTerm, generalTruth,
      generalTermEval_substVar]
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.VarSubstitutable] at h
    simp only [Formula.substVar, Formula.substTerm, generalTruth,
      show generalTruth M (φ.substTerm x (.var y)) s ↔
        generalTruth M φ (Function.update s x (s y)) from ihφ s h.1,
      show generalTruth M (ψ.substTerm x (.var y)) s ↔
        generalTruth M ψ (Function.update s x (s y)) from ihψ s h.2]
  | conj φ ψ ihφ ihψ =>
    simp only [Formula.VarSubstitutable] at h
    exact and_congr (ihφ s h.1) (ihψ s h.2)
  | disj φ ψ ihφ ihψ =>
    simp only [Formula.VarSubstitutable] at h
    exact or_congr (ihφ s h.1) (ihψ s h.2)
  | neg φ ih => exact not_congr (ih s h)
  | know a φ _ => exact M.weak_substitution a φ x y s h
  | all z φ ih =>
    by_cases hzx : z = x
    · subst z
      simp only [Formula.substVar, Formula.substTerm, ite_true,
        generalTruth, Function.update_idem]
    · have hb := h.resolve_left hzx
      rcases hb.1 with hzy | hx
      · simp only [Formula.substVar, Formula.substTerm, if_neg hzx, generalTruth]
        apply forall_congr'
        intro n
        have hi := ih (Function.update s z n) hb.2
        simpa only [Formula.substVar, Function.update_of_ne (Ne.symm hzy),
          Function.update_comm hzx n (s y) s] using hi
      · exact generalTruth_substVar_of_notMem M (.all z φ) x y s
          (fun hm => hx (Finset.mem_erase.mp hm).2)
  | ex z φ ih =>
    by_cases hzx : z = x
    · subst z
      simp only [Formula.substVar, Formula.substTerm, ite_true,
        generalTruth, Function.update_idem]
    · have hb := h.resolve_left hzx
      rcases hb.1 with hzy | hx
      · simp only [Formula.substVar, Formula.substTerm, if_neg hzx, generalTruth]
        apply exists_congr
        intro n
        have hi := ih (Function.update s z n) hb.2
        simpa only [Formula.substVar, Function.update_of_ne (Ne.symm hzy),
          Function.update_comm hzx n (s y) s] using hi
      · exact generalTruth_substVar_of_notMem M (.ex z φ) x y s
          (fun hm => hx (Finset.mem_erase.mp hm).2)

end Alexander313
