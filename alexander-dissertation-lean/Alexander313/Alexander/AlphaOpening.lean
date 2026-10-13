import Alexander313.Alexander.AlphaClosure

/-!
# Opening a named binder in the alpha representation

Substituting a numeral for one free variable matches opening the final
external de Bruijn binder. Inner binders, including shadowing occurrences,
remain bound. This supplies the quantifier step in filtered alphabetic
invariance without assuming arbitrary-term substitution of modal validity.
-/

namespace Alexander313

def NumericalSubstitution.without (σ : NumericalSubstitution) (bound : List Nat) :
    NumericalSubstitution := fun x => if x ∈ bound then none else σ x

@[simp] theorem NumericalSubstitution.without_nil (σ : NumericalSubstitution) :
    σ.without [] = σ := by
  funext x
  simp [without]

theorem NumericalSubstitution.without_remove (σ : NumericalSubstitution)
    (bound : List Nat) (x : Nat) :
    NumericalSubstitution.remove (σ.without bound) x = σ.without (x :: bound) := by
  funext z
  by_cases hzx : z = x <;> simp [remove, without, hzx]

def numericalAt (x n : Nat) : NumericalSubstitution :=
  fun z => if z = x then some n else none

def AlphaTerm.instantiate (depth n : Nat) : AlphaTerm → AlphaTerm
  | .free x => .free x
  | .bound i => if i = depth then AlphaTerm.numeral n
      else if depth < i then .bound (i - 1) else .bound i
  | .zero => .zero
  | .succ t => .succ (t.instantiate depth n)
  | .add t u => .add (t.instantiate depth n) (u.instantiate depth n)
  | .mul t u => .mul (t.instantiate depth n) (u.instantiate depth n)

def AlphaFormula.instantiate {Owner : Type} (depth n : Nat) :
    AlphaFormula Owner → AlphaFormula Owner
  | .falsum => .falsum
  | .equal t u => .equal (t.instantiate depth n) (u.instantiate depth n)
  | .imp φ ψ => .imp (φ.instantiate depth n) (ψ.instantiate depth n)
  | .conj φ ψ => .conj (φ.instantiate depth n) (ψ.instantiate depth n)
  | .disj φ ψ => .disj (φ.instantiate depth n) (ψ.instantiate depth n)
  | .neg φ => .neg (φ.instantiate depth n)
  | .all φ => .all (φ.instantiate (depth + 1) n)
  | .ex φ => .ex (φ.instantiate (depth + 1) n)
  | .know a φ => .know a (φ.instantiate depth n)

theorem Term.alpha_open (t : Term) (bound : List Nat) (x n : Nat) :
    (t.subst ((numericalAt x n).without bound)).alpha bound =
      (t.alpha (bound ++ [x])).instantiate bound.length n := by
  induction t with
  | var z =>
    by_cases hz : z ∈ bound
    · have hi := List.idxOf_lt_length_of_mem hz
      have hne : bound.idxOf z ≠ bound.length := Nat.ne_of_lt hi
      have hnot : ¬ bound.length < bound.idxOf z := Nat.not_lt.mpr (Nat.le_of_lt hi)
      simp [Term.subst, Term.alpha, NumericalSubstitution.without, hz,
        List.mem_append, List.idxOf_append_of_mem hz, AlphaTerm.instantiate, hne, hnot]
    · by_cases hzx : z = x
      · subst z
        simp [Term.subst, Term.alpha, NumericalSubstitution.without, numericalAt, hz,
          List.idxOf_append_of_notMem hz, AlphaTerm.instantiate]
      · simp [Term.subst, Term.alpha, NumericalSubstitution.without, numericalAt, hz,
          hzx, AlphaTerm.instantiate]
  | zero => rfl
  | succ t ih => simp only [Term.subst, Term.alpha, AlphaTerm.instantiate, ih]
  | add t u iht ihu => simp only [Term.subst, Term.alpha, AlphaTerm.instantiate, iht, ihu]
  | mul t u iht ihu => simp only [Term.subst, Term.alpha, AlphaTerm.instantiate, iht, ihu]

theorem Formula.alpha_open {Owner : Type} (φ : Formula Owner)
    (bound : List Nat) (x n : Nat) :
    (φ.subst ((numericalAt x n).without bound)).alpha bound =
      (φ.alpha (bound ++ [x])).instantiate bound.length n := by
  induction φ generalizing bound with
  | falsum => rfl
  | equal t u => simp only [Formula.subst, Formula.alpha, AlphaFormula.instantiate,
      Term.alpha_open t bound x n, Term.alpha_open u bound x n]
  | imp φ ψ ihφ ihψ => simp only [Formula.subst, Formula.alpha, AlphaFormula.instantiate, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [Formula.subst, Formula.alpha, AlphaFormula.instantiate, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [Formula.subst, Formula.alpha, AlphaFormula.instantiate, ihφ, ihψ]
  | neg φ ih => simp only [Formula.subst, Formula.alpha, AlphaFormula.instantiate, ih]
  | know a φ ih => simp only [Formula.subst, Formula.alpha, AlphaFormula.instantiate, ih]
  | all y φ ih =>
    simpa only [Formula.subst, Formula.alpha, AlphaFormula.instantiate,
      NumericalSubstitution.without_remove, List.cons_append, List.length_cons,
      Nat.succ_eq_add_one] using congrArg AlphaFormula.all (ih (y :: bound))
  | ex y φ ih =>
    simpa only [Formula.subst, Formula.alpha, AlphaFormula.instantiate,
      NumericalSubstitution.without_remove, List.cons_append, List.length_cons,
      Nat.succ_eq_add_one] using congrArg AlphaFormula.ex (ih (y :: bound))

theorem Formula.alpha_numericalAt {Owner : Type} (φ : Formula Owner) (x n : Nat) :
    (φ.subst (numericalAt x n)).alpha [] = (φ.alpha [x]).instantiate 0 n := by
  simpa only [NumericalSubstitution.without_nil, List.nil_append, List.length_nil] using
    alpha_open φ [] x n

theorem Formula.freeVars_subset_singleton_of_all_closed {Owner : Type}
    (φ : Formula Owner) (x : Nat) (h : (Formula.all x φ).Closed) :
    φ.freeVars ⊆ {x} := by
  intro v hv
  by_cases hvx : v = x
  · simpa only [Finset.mem_singleton] using hvx
  · have hm : v ∈ (Formula.all x φ).freeVars := Finset.mem_erase.mpr ⟨hvx, hv⟩
    rw [h] at hm
    exact False.elim (Finset.notMem_empty v hm)

theorem Formula.freeVars_subset_singleton_of_ex_closed {Owner : Type}
    (φ : Formula Owner) (x : Nat) (h : (Formula.ex x φ).Closed) :
    φ.freeVars ⊆ {x} :=
  freeVars_subset_singleton_of_all_closed φ x h

theorem Formula.close_singleton {Owner : Type} (φ : Formula Owner)
    (x n : Nat) (s : Assignment) (h : φ.freeVars ⊆ {x}) :
    φ.close (Function.update s x n) = φ.subst (numericalAt x n) := by
  apply subst_eq_of_agree
  intro v hv
  have hvx := Finset.mem_singleton.mp (h hv)
  subst v
  simp [numericalAt]

def AlphaTerm.toTerm : AlphaTerm → Term
  | .free x => .var x
  | .bound i => .var i
  | .zero => .zero
  | .succ t => .succ t.toTerm
  | .add t u => .add t.toTerm u.toTerm
  | .mul t u => .mul t.toTerm u.toTerm

@[simp] theorem Term.toTerm_alpha_nil (t : Term) : (t.alpha []).toTerm = t := by
  induction t <;> simp_all [Term.alpha, AlphaTerm.toTerm]

theorem Term.alpha_nil_injective : Function.Injective (fun t : Term => t.alpha []) := by
  intro t u h
  simpa only [toTerm_alpha_nil] using congrArg AlphaTerm.toTerm h

def Formula.logicalSize {Owner : Type} : Formula Owner → Nat
  | .falsum => 1
  | .equal _ _ => 1
  | .imp φ ψ => φ.logicalSize + ψ.logicalSize + 1
  | .conj φ ψ => φ.logicalSize + ψ.logicalSize + 1
  | .disj φ ψ => φ.logicalSize + ψ.logicalSize + 1
  | .neg φ => φ.logicalSize + 1
  | .all _ φ => φ.logicalSize + 1
  | .ex _ φ => φ.logicalSize + 1
  | .know _ φ => φ.logicalSize + 1

@[simp] theorem Formula.logicalSize_subst {Owner : Type} (φ : Formula Owner)
    (σ : NumericalSubstitution) : (φ.subst σ).logicalSize = φ.logicalSize := by
  induction φ generalizing σ <;> simp_all [logicalSize, subst]

@[simp] theorem Formula.logicalSize_close {Owner : Type} (φ : Formula Owner)
    (s : Assignment) : (φ.close s).logicalSize = φ.logicalSize := logicalSize_subst φ _

end Alexander313
