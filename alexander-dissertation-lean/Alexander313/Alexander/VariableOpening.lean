import Alexander313.Alexander.AlphaOpening

/-!
# Opening alpha binders with fresh variables

This is the syntactic part of alphabetic invariance for arbitrary-domain
Alexander models. Fresh-variable opening permits the weak variable rule;
it does not use substitution of a numeral or any other arithmetic term.
-/

namespace Alexander313

def Term.substVariables (σ : NumericalSubstitution) : Term → Term
  | .var x => match σ x with
    | none => .var x
    | some y => .var y
  | .zero => .zero
  | .succ t => .succ (t.substVariables σ)
  | .add t u => .add (t.substVariables σ) (u.substVariables σ)
  | .mul t u => .mul (t.substVariables σ) (u.substVariables σ)

def Formula.substVariables {Owner : Type} (σ : NumericalSubstitution) :
    Formula Owner → Formula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.substVariables σ) (u.substVariables σ)
  | .imp φ ψ => .imp (φ.substVariables σ) (ψ.substVariables σ)
  | .conj φ ψ => .conj (φ.substVariables σ) (ψ.substVariables σ)
  | .disj φ ψ => .disj (φ.substVariables σ) (ψ.substVariables σ)
  | .neg φ => .neg (φ.substVariables σ)
  | .all x φ => .all x (φ.substVariables (σ.remove x))
  | .ex x φ => .ex x (φ.substVariables (σ.remove x))
  | .know a φ => .know a (φ.substVariables σ)

@[simp] theorem Term.substVariables_none (t : Term) :
    t.substVariables (fun _ => none) = t := by
  induction t <;> simp_all [substVariables]

@[simp] theorem Formula.substVariables_none {Owner : Type} (φ : Formula Owner) :
    φ.substVariables (fun _ => none) = φ := by
  induction φ <;> simp_all [substVariables]

theorem numericalAt_remove_same (x z : Nat) :
    NumericalSubstitution.remove (numericalAt x z) x = fun _ => none := by
  funext v
  by_cases hvx : v = x <;> simp [numericalAt, NumericalSubstitution.remove, hvx]

theorem numericalAt_remove_ne (x z y : Nat) (hyx : y ≠ x) :
    NumericalSubstitution.remove (numericalAt x z) y = numericalAt x z := by
  funext v
  by_cases hvy : v = y
  · subst v
    simp [numericalAt, NumericalSubstitution.remove, hyx]
  · simp [NumericalSubstitution.remove, hvy]

theorem Term.substTerm_var_eq_substVariables (t : Term) (x z : Nat) :
    Term.substTerm x (.var z) t = t.substVariables (numericalAt x z) := by
  induction t <;> simp_all [substTerm, substVariables, numericalAt]
  split_ifs <;> rfl

theorem Formula.substVar_eq_substVariables {Owner : Type} (φ : Formula Owner) (x z : Nat) :
    φ.substVar x z = φ.substVariables (numericalAt x z) := by
  induction φ with
  | falsum => rfl
  | equal t u => simp only [substVar, substTerm, substVariables, Term.substTerm_var_eq_substVariables]
  | imp φ ψ ihφ ihψ => simp only [substVar, substTerm, substVariables] at *; rw [ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [substVar, substTerm, substVariables] at *; rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [substVar, substTerm, substVariables] at *; rw [ihφ, ihψ]
  | neg φ ih => simp only [substVar, substTerm, substVariables] at *; rw [ih]
  | know a φ ih => simp only [substVar, substTerm, substVariables] at *; rw [ih]
  | all y φ ih =>
    by_cases hyx : y = x
    · subst y
      simp only [substVar, substTerm, ite_true, substVariables,
        numericalAt_remove_same, substVariables_none]
    · simpa only [substVar, substTerm, if_neg hyx, substVariables,
        numericalAt_remove_ne x z y hyx] using congrArg (Formula.all y) ih
  | ex y φ ih =>
    by_cases hyx : y = x
    · subst y
      simp only [substVar, substTerm, ite_true, substVariables,
        numericalAt_remove_same, substVariables_none]
    · simpa only [substVar, substTerm, if_neg hyx, substVariables,
        numericalAt_remove_ne x z y hyx] using congrArg (Formula.ex y) ih

def Formula.boundVars {Owner : Type} : Formula Owner → Finset Nat
  | .falsum => ∅
  | .equal _ _ => ∅
  | .imp φ ψ => φ.boundVars ∪ ψ.boundVars
  | .conj φ ψ => φ.boundVars ∪ ψ.boundVars
  | .disj φ ψ => φ.boundVars ∪ ψ.boundVars
  | .neg φ => φ.boundVars
  | .all x φ => insert x φ.boundVars
  | .ex x φ => insert x φ.boundVars
  | .know _ φ => φ.boundVars

theorem Formula.varSubstitutable_of_notMem_boundVars {Owner : Type}
    (φ : Formula Owner) (x z : Nat) (hz : z ∉ φ.boundVars) : φ.VarSubstitutable x z := by
  induction φ with
  | falsum => trivial
  | equal _ _ => trivial
  | imp φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun h => hz (Finset.mem_union_left _ h)),
      ihψ (fun h => hz (Finset.mem_union_right _ h))⟩
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun h => hz (Finset.mem_union_left _ h)),
      ihψ (fun h => hz (Finset.mem_union_right _ h))⟩
  | disj φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun h => hz (Finset.mem_union_left _ h)),
      ihψ (fun h => hz (Finset.mem_union_right _ h))⟩
  | neg φ ih => exact ih hz
  | know _ φ ih => exact ih hz
  | all y φ ih =>
    have hzy : z ≠ y := fun h => hz (Finset.mem_insert.mpr (Or.inl h))
    have hyz : y ≠ z := Ne.symm hzy
    exact Or.inr ⟨Or.inl hyz, ih (fun h => hz (Finset.mem_insert_of_mem h))⟩
  | ex y φ ih =>
    have hzy : z ≠ y := fun h => hz (Finset.mem_insert.mpr (Or.inl h))
    have hyz : y ≠ z := Ne.symm hzy
    exact Or.inr ⟨Or.inl hyz, ih (fun h => hz (Finset.mem_insert_of_mem h))⟩

def AlphaTerm.openVariable (depth z : Nat) : AlphaTerm → AlphaTerm
  | .free x => .free x
  | .bound i => if i = depth then .free z
      else if depth < i then .bound (i - 1) else .bound i
  | .zero => .zero
  | .succ t => .succ (t.openVariable depth z)
  | .add t u => .add (t.openVariable depth z) (u.openVariable depth z)
  | .mul t u => .mul (t.openVariable depth z) (u.openVariable depth z)

def AlphaFormula.openVariable {Owner : Type} (depth z : Nat) :
    AlphaFormula Owner → AlphaFormula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.openVariable depth z) (u.openVariable depth z)
  | .imp φ ψ => .imp (φ.openVariable depth z) (ψ.openVariable depth z)
  | .conj φ ψ => .conj (φ.openVariable depth z) (ψ.openVariable depth z)
  | .disj φ ψ => .disj (φ.openVariable depth z) (ψ.openVariable depth z)
  | .neg φ => .neg (φ.openVariable depth z)
  | .all φ => .all (φ.openVariable (depth + 1) z)
  | .ex φ => .ex (φ.openVariable (depth + 1) z)
  | .know a φ => .know a (φ.openVariable depth z)

theorem Term.alpha_openVariable (t : Term) (bound : List Nat) (x z : Nat)
    (hz : z ∉ bound) :
    (t.substVariables ((numericalAt x z).without bound)).alpha bound =
      (t.alpha (bound ++ [x])).openVariable bound.length z := by
  induction t with
  | var v =>
    by_cases hv : v ∈ bound
    · have hi := List.idxOf_lt_length_of_mem hv
      have hne : bound.idxOf v ≠ bound.length := Nat.ne_of_lt hi
      have hnot : ¬ bound.length < bound.idxOf v := Nat.not_lt.mpr (Nat.le_of_lt hi)
      simp [Term.substVariables, Term.alpha, NumericalSubstitution.without, hv,
        List.mem_append, List.idxOf_append_of_mem hv, AlphaTerm.openVariable, hne, hnot]
    · by_cases hvx : v = x
      · subst v
        simp [Term.substVariables, Term.alpha, NumericalSubstitution.without, numericalAt,
          hv, hz, List.idxOf_append_of_notMem hv, AlphaTerm.openVariable]
      · simp [Term.substVariables, Term.alpha, NumericalSubstitution.without, numericalAt,
          hv, hvx, AlphaTerm.openVariable]
  | zero => rfl
  | succ t ih => simp only [Term.substVariables, Term.alpha, AlphaTerm.openVariable, ih]
  | add t u iht ihu => simp only [Term.substVariables, Term.alpha, AlphaTerm.openVariable, iht, ihu]
  | mul t u iht ihu => simp only [Term.substVariables, Term.alpha, AlphaTerm.openVariable, iht, ihu]

theorem Formula.alpha_openVariable {Owner : Type} (φ : Formula Owner)
    (bound : List Nat) (x z : Nat) (hz : z ∉ bound) (hφ : z ∉ φ.boundVars) :
    (φ.substVariables ((numericalAt x z).without bound)).alpha bound =
      (φ.alpha (bound ++ [x])).openVariable bound.length z := by
  induction φ generalizing bound with
  | falsum => rfl
  | equal t u => simp only [substVariables, alpha, AlphaFormula.openVariable,
      Term.alpha_openVariable t bound x z hz, Term.alpha_openVariable u bound x z hz]
  | imp φ ψ ihφ ihψ =>
    simp only [substVariables, alpha, AlphaFormula.openVariable,
      ihφ bound hz (fun h => hφ (Finset.mem_union_left _ h)),
      ihψ bound hz (fun h => hφ (Finset.mem_union_right _ h))]
  | conj φ ψ ihφ ihψ =>
    simp only [substVariables, alpha, AlphaFormula.openVariable,
      ihφ bound hz (fun h => hφ (Finset.mem_union_left _ h)),
      ihψ bound hz (fun h => hφ (Finset.mem_union_right _ h))]
  | disj φ ψ ihφ ihψ =>
    simp only [substVariables, alpha, AlphaFormula.openVariable,
      ihφ bound hz (fun h => hφ (Finset.mem_union_left _ h)),
      ihψ bound hz (fun h => hφ (Finset.mem_union_right _ h))]
  | neg φ ih => simp only [substVariables, alpha, AlphaFormula.openVariable, ih bound hz hφ]
  | know a φ ih => simp only [substVariables, alpha, AlphaFormula.openVariable, ih bound hz hφ]
  | all y φ ih =>
    have hzy : z ≠ y := fun h => hφ (Finset.mem_insert.mpr (Or.inl h))
    have hz' : z ∉ y :: bound := by simp [hzy, hz]
    have hφ' : z ∉ φ.boundVars := fun h => hφ (Finset.mem_insert_of_mem h)
    simpa only [substVariables, alpha, AlphaFormula.openVariable,
      NumericalSubstitution.without_remove, List.cons_append, List.length_cons,
      Nat.succ_eq_add_one] using congrArg AlphaFormula.all (ih (y :: bound) hz' hφ')
  | ex y φ ih =>
    have hzy : z ≠ y := fun h => hφ (Finset.mem_insert.mpr (Or.inl h))
    have hz' : z ∉ y :: bound := by simp [hzy, hz]
    have hφ' : z ∉ φ.boundVars := fun h => hφ (Finset.mem_insert_of_mem h)
    simpa only [substVariables, alpha, AlphaFormula.openVariable,
      NumericalSubstitution.without_remove, List.cons_append, List.length_cons,
      Nat.succ_eq_add_one] using congrArg AlphaFormula.ex (ih (y :: bound) hz' hφ')

theorem Formula.alpha_substVar_fresh {Owner : Type} (φ : Formula Owner) (x z : Nat)
    (hz : z ∉ φ.boundVars) :
    (φ.substVar x z).alpha [] = (φ.alpha [x]).openVariable 0 z := by
  rw [substVar_eq_substVariables]
  simpa only [NumericalSubstitution.without_nil, List.nil_append, List.length_nil] using
    alpha_openVariable φ [] x z (by simp) hz

@[simp] theorem Formula.logicalSize_substTerm {Owner : Type} (φ : Formula Owner)
    (x : Nat) (t : Term) : (φ.substTerm x t).logicalSize = φ.logicalSize := by
  induction φ <;> simp_all [logicalSize, substTerm]
  all_goals split_ifs <;> simp_all [logicalSize]

@[simp] theorem Formula.logicalSize_substVar {Owner : Type} (φ : Formula Owner)
    (x z : Nat) : (φ.substVar x z).logicalSize = φ.logicalSize := logicalSize_substTerm φ x (.var z)

end Alexander313
