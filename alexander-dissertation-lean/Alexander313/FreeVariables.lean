import Alexander313.Semantics

/-!
# Numeral closure and irrelevant assignments

These are part of the free-variable condition in Alexander Definition
1.2.6 and the admissibility proof required by Lemma 1.2.22. They do not
prove alphabetic invariance or weak variable substitution of raw theories.
-/

namespace Alexander313

namespace Term

theorem mem_freeVars_subst (t : Term) (σ : NumericalSubstitution) (v : Nat) :
    v ∈ (t.subst σ).freeVars ↔ v ∈ t.freeVars ∧ σ v = none := by
  induction t with
  | var x => cases h : σ x <;> simp_all [subst, freeVars]
  | zero => simp [subst, freeVars]
  | succ t ih => simpa only [subst, freeVars] using ih
  | add t u iht ihu =>
    simp only [subst, freeVars, Finset.mem_union, iht, ihu]
    tauto
  | mul t u iht ihu =>
    simp only [subst, freeVars, Finset.mem_union, iht, ihu]
    tauto

theorem subst_eq_of_agree (t : Term) (σ τ : NumericalSubstitution)
    (h : ∀ v ∈ t.freeVars, σ v = τ v) : t.subst σ = t.subst τ := by
  induction t generalizing σ τ with
  | var x => simp only [subst, h x (by simp [freeVars])]
  | zero => rfl
  | succ t ih => exact congrArg Term.succ (ih σ τ h)
  | add t u iht ihu =>
    have ht := iht σ τ (fun v hv => h v (Finset.mem_union_left _ hv))
    have hu := ihu σ τ (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [subst, ht, hu]
  | mul t u iht ihu =>
    have ht := iht σ τ (fun v hv => h v (Finset.mem_union_left _ hv))
    have hu := ihu σ τ (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [subst, ht, hu]

end Term

namespace Formula

variable {Owner : Type}

theorem mem_freeVars_subst (φ : Formula Owner) (σ : NumericalSubstitution) (v : Nat) :
    v ∈ (φ.subst σ).freeVars ↔ v ∈ φ.freeVars ∧ σ v = none := by
  induction φ generalizing σ with
  | falsum => simp [subst, freeVars]
  | equal t u =>
    simp only [subst, freeVars, Finset.mem_union, Term.mem_freeVars_subst]
    tauto
  | imp φ ψ ihφ ihψ =>
    simp only [subst, freeVars, Finset.mem_union, ihφ, ihψ]
    tauto
  | conj φ ψ ihφ ihψ =>
    simp only [subst, freeVars, Finset.mem_union, ihφ, ihψ]
    tauto
  | disj φ ψ ihφ ihψ =>
    simp only [subst, freeVars, Finset.mem_union, ihφ, ihψ]
    tauto
  | neg φ ih => simpa only [subst, freeVars] using ih σ
  | all x φ ih =>
    simp only [subst, freeVars, Finset.mem_erase, ih]
    by_cases h : v = x <;> simp [NumericalSubstitution.remove, h] <;> tauto
  | ex x φ ih =>
    simp only [subst, freeVars, Finset.mem_erase, ih]
    by_cases h : v = x <;> simp [NumericalSubstitution.remove, h] <;> tauto
  | know a φ ih => simpa only [subst, freeVars] using ih σ

theorem close_closed (φ : Formula Owner) (s : Assignment) : (φ.close s).Closed := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := (mem_freeVars_subst φ (fun x => some (s x)) v).mp hv
  cases h.2

theorem subst_eq_of_agree (φ : Formula Owner) (σ τ : NumericalSubstitution)
    (h : ∀ v ∈ φ.freeVars, σ v = τ v) : φ.subst σ = φ.subst τ := by
  induction φ generalizing σ τ with
  | falsum => rfl
  | equal t u =>
    have ht := t.subst_eq_of_agree σ τ
      (fun v hv => h v (Finset.mem_union_left _ hv))
    have hu := u.subst_eq_of_agree σ τ
      (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [subst, ht, hu]
  | imp φ ψ ihφ ihψ =>
    have hφ := ihφ σ τ (fun v hv => h v (Finset.mem_union_left _ hv))
    have hψ := ihψ σ τ (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [subst, hφ, hψ]
  | conj φ ψ ihφ ihψ =>
    have hφ := ihφ σ τ (fun v hv => h v (Finset.mem_union_left _ hv))
    have hψ := ihψ σ τ (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [subst, hφ, hψ]
  | disj φ ψ ihφ ihψ =>
    have hφ := ihφ σ τ (fun v hv => h v (Finset.mem_union_left _ hv))
    have hψ := ihψ σ τ (fun v hv => h v (Finset.mem_union_right _ hv))
    simp only [subst, hφ, hψ]
  | neg φ ih => exact congrArg Formula.neg (ih σ τ h)
  | all x φ ih =>
    apply congrArg (Formula.all x)
    apply ih
    intro v hv
    by_cases hx : v = x
    · simp [NumericalSubstitution.remove, hx]
    · simp only [NumericalSubstitution.remove, if_neg hx]
      exact h v (Finset.mem_erase.mpr ⟨hx, hv⟩)
  | ex x φ ih =>
    apply congrArg (Formula.ex x)
    apply ih
    intro v hv
    by_cases hx : v = x
    · simp [NumericalSubstitution.remove, hx]
    · simp only [NumericalSubstitution.remove, if_neg hx]
      exact h v (Finset.mem_erase.mpr ⟨hx, hv⟩)
  | know a φ ih => exact congrArg (Formula.know a) (ih σ τ h)

theorem close_eq_of_agree (φ : Formula Owner) (s t : Assignment)
    (h : ∀ v ∈ φ.freeVars, s v = t v) : φ.close s = φ.close t :=
  subst_eq_of_agree φ _ _ (fun v hv => congrArg some (h v hv))

theorem subst_eq_self_of_closed (φ : Formula Owner) (h : φ.Closed)
    (σ : NumericalSubstitution) : φ.subst σ = φ := by
  calc
    φ.subst σ = φ.subst (fun _ => none) := subst_eq_of_agree φ _ _ (by
      intro v hv
      rw [h] at hv
      exact False.elim (Finset.notMem_empty v hv))
    _ = φ := subst_none φ

theorem close_eq_self_of_closed (φ : Formula Owner) (h : φ.Closed)
    (s : Assignment) : φ.close s = φ := subst_eq_self_of_closed φ h _

end Formula

theorem truth_eq_of_agree {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (φ : Formula Owner) (s t : Assignment)
    (h : ∀ v ∈ φ.freeVars, s v = t v) : truth filtered P φ s ↔ truth filtered P φ t := by
  have hc := φ.close_eq_of_agree s t h
  calc
    truth filtered P φ s ↔ truth filtered P (φ.close s) t :=
      (truth_close filtered P φ s t).symm
    _ ↔ truth filtered P (φ.close t) t := by rw [hc]
    _ ↔ truth filtered P φ t := truth_close filtered P φ t t

end Alexander313
