import Alexander313.Syntax

/-!
# Filtered and actual consequence interpretations

Formula recursion defines both interpretations. The filtered interpretation
does not assume that any predicate is sound. The numerical-assignment law is
proved, rather than imposed as an extra modal substitution axiom.
-/

namespace Alexander313

abbrev RawPredicates (Owner : Type) := Owner → Formula Owner → Prop

def truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner) :
    Formula Owner → Assignment → Prop
  | .falsum, _ => False
  | .equal t u, s => t.eval s = u.eval s
  | .imp φ ψ, s => truth filtered P φ s → truth filtered P ψ s
  | .conj φ ψ, s => truth filtered P φ s ∧ truth filtered P ψ s
  | .disj φ ψ, s => truth filtered P φ s ∨ truth filtered P ψ s
  | .neg φ, s => ¬ truth filtered P φ s
  | .all x φ, s => ∀ n, truth filtered P φ (Function.update s x n)
  | .ex x φ, s => ∃ n, truth filtered P φ (Function.update s x n)
  | .know a φ, s => P a (φ.close s) ∧
      (if filtered = true then truth filtered P φ s else True)

abbrev filteredTruth {Owner : Type} := @truth Owner true
abbrev actualTruth {Owner : Type} := @truth Owner false

theorem truth_subst {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (φ : Formula Owner) (σ : NumericalSubstitution) (s : Assignment) :
    truth filtered P (φ.subst σ) s ↔ truth filtered P φ (σ.override s) := by
  induction φ generalizing σ s with
  | falsum => rfl
  | equal t u => simp [Formula.subst, truth]
  | imp φ ψ ihφ ihψ => simp [Formula.subst, truth, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp [Formula.subst, truth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [Formula.subst, truth, ihφ, ihψ]
  | neg φ ih => simp [Formula.subst, truth, ih]
  | all x φ ih =>
    simp only [Formula.subst, truth]
    exact forall_congr' fun n => by
      simpa only [NumericalSubstitution.override_update] using
        ih (σ.remove x) (Function.update s x n)
  | ex x φ ih =>
    simp only [Formula.subst, truth]
    exact exists_congr fun n => by
      simpa only [NumericalSubstitution.override_update] using
        ih (σ.remove x) (Function.update s x n)
  | know a φ ih =>
    cases filtered <;> simp [Formula.subst, truth, ih]

theorem truth_close {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (φ : Formula Owner) (s t : Assignment) :
    truth filtered P (φ.close s) t ↔ truth filtered P φ s := by
  simpa only [Formula.close, NumericalSubstitution.override_total] using
    truth_subst filtered P φ (fun x => some (s x)) t

namespace Formula

variable {Owner : Type} [DecidableEq Owner]

/-- Every query class in a formula, including queries below other heads. -/
def queries : Formula Owner → Finset (Owner × Shape Owner)
  | .falsum => ∅
  | .equal _ _ => ∅
  | .imp φ ψ => φ.queries ∪ ψ.queries
  | .conj φ ψ => φ.queries ∪ ψ.queries
  | .disj φ ψ => φ.queries ∪ ψ.queries
  | .neg φ => φ.queries
  | .all _ φ => φ.queries
  | .ex _ φ => φ.queries
  | .know a φ => insert (a, φ.shape) φ.queries

@[simp] theorem queries_subst (φ : Formula Owner) (σ : NumericalSubstitution) :
    (φ.subst σ).queries = φ.queries := by
  induction φ generalizing σ <;> simp_all [subst, queries]

@[simp] theorem close_prefix (a : Owner) (n : Nat) (φ : Formula Owner)
    (s : Assignment) : («prefix» a n φ).close s = «prefix» a n (φ.close s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Formula.know a ((«prefix» a n φ).close s) =
      Formula.know a («prefix» a n (φ.close s))
    rw [ih]

end Formula

def AgreeOn {Owner : Type} [DecidableEq Owner]
    (P Q : RawPredicates Owner) (φ : Formula Owner) : Prop :=
  ∀ a θ, (a, θ.shape) ∈ φ.queries → (P a θ ↔ Q a θ)

theorem AgreeOn.mono {Owner : Type} [DecidableEq Owner]
    {P Q : RawPredicates Owner} {φ ψ : Formula Owner}
    (h : AgreeOn P Q ψ) (hsub : φ.queries ⊆ ψ.queries) : AgreeOn P Q φ :=
  fun a θ hm => h a θ (hsub hm)

/-- Finite masks preserve truth on all numeral instances and term variants
    in the retained query classes, not just a finite list of sentences. -/
theorem truth_congr_queries {Owner : Type} [DecidableEq Owner]
    (filtered : Bool) (P Q : RawPredicates Owner) (φ : Formula Owner)
    (s : Assignment) : AgreeOn P Q φ →
      (truth filtered P φ s ↔ truth filtered Q φ s) := by
  induction φ generalizing s with
  | falsum => intro _; rfl
  | equal t u => intro _; rfl
  | imp φ ψ ihφ ihψ =>
    intro h
    have hφ := h.mono (show φ.queries ⊆ (Formula.imp φ ψ).queries from
      fun _ hm => Finset.mem_union.mpr (Or.inl hm))
    have hψ := h.mono (show ψ.queries ⊆ (Formula.imp φ ψ).queries from
      fun _ hm => Finset.mem_union.mpr (Or.inr hm))
    simp only [truth, ihφ s hφ, ihψ s hψ]
  | conj φ ψ ihφ ihψ =>
    intro h
    have hφ := h.mono (show φ.queries ⊆ (Formula.conj φ ψ).queries from
      fun _ hm => Finset.mem_union.mpr (Or.inl hm))
    have hψ := h.mono (show ψ.queries ⊆ (Formula.conj φ ψ).queries from
      fun _ hm => Finset.mem_union.mpr (Or.inr hm))
    simp only [truth, ihφ s hφ, ihψ s hψ]
  | disj φ ψ ihφ ihψ =>
    intro h
    have hφ := h.mono (show φ.queries ⊆ (Formula.disj φ ψ).queries from
      fun _ hm => Finset.mem_union.mpr (Or.inl hm))
    have hψ := h.mono (show ψ.queries ⊆ (Formula.disj φ ψ).queries from
      fun _ hm => Finset.mem_union.mpr (Or.inr hm))
    simp only [truth, ihφ s hφ, ihψ s hψ]
  | neg φ ih => intro h; simpa only [truth] using not_congr (ih s h)
  | all x φ ih =>
    intro h
    exact forall_congr' fun n => ih (Function.update s x n) h
  | ex x φ ih =>
    intro h
    exact exists_congr fun n => ih (Function.update s x n) h
  | know a φ ih =>
    intro h
    have hraw : P a (φ.close s) ↔ Q a (φ.close s) :=
      h a (φ.close s) (by simp [Formula.queries])
    have hφ := h.mono (show φ.queries ⊆ (Formula.know a φ).queries from
      fun _ hm => Finset.mem_insert_of_mem hm)
    cases filtered <;> simp only [truth, Bool.false_eq_true, ↓reduceIte,
      hraw, ih s hφ]

/-- Full predicate soundness, before any mechanicalness conclusion. -/
def RawSound {Owner : Type} (P : RawPredicates Owner) (a : Owner) : Prop :=
  ∀ φ s, P a (φ.close s) → filteredTruth P φ s

theorem filtered_factive {Owner : Type} (P : RawPredicates Owner)
    (a : Owner) (φ : Formula Owner) (s : Assignment) :
    filteredTruth P (.know a φ) s → filteredTruth P φ s :=
  fun h => h.2

theorem filtered_know_iff {Owner : Type} (P : RawPredicates Owner)
    {a : Owner} (hs : RawSound P a) (φ : Formula Owner) (s : Assignment) :
    filteredTruth P (.know a φ) s ↔ P a (φ.close s) :=
  ⟨fun h => h.1, fun h => ⟨h, hs φ s h⟩⟩

theorem filtered_eq_actual {Owner : Type} (P : RawPredicates Owner)
    (hs : ∀ a, RawSound P a) (φ : Formula Owner) (s : Assignment) :
    filteredTruth P φ s ↔ actualTruth P φ s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t u => rfl
  | imp φ ψ ihφ ihψ => simp only [truth, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [truth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [truth, ihφ, ihψ]
  | neg φ ih => simp only [truth, ih]
  | all x φ ih => exact forall_congr' fun n => ih (Function.update s x n)
  | ex x φ ih => exact exists_congr fun n => ih (Function.update s x n)
  | know a φ _ =>
    exact (filtered_know_iff P (hs a) φ s).trans (by simp [truth])

theorem filtered_deduction {Owner : Type} (P : RawPredicates Owner)
    (a : Owner)
    (mp : ∀ φ ψ, P a (.imp φ ψ) → P a φ → P a ψ)
    (φ ψ : Formula Owner) (s : Assignment) :
    filteredTruth P (.imp (.know a (.imp φ ψ))
      (.imp (.know a φ) (.know a ψ))) s := by
  intro himp hφ
  exact ⟨mp (φ.close s) (ψ.close s) himp.1 hφ.1, himp.2 hφ.2⟩

theorem filtered_introspection {Owner : Type} (P : RawPredicates Owner)
    (a : Owner) (necessity : ∀ φ, P a φ → P a (.know a φ))
    (φ : Formula Owner) (s : Assignment) :
    filteredTruth P (.imp (.know a φ) (.know a (.know a φ))) s := by
  intro h
  exact ⟨necessity (φ.close s) h.1, h⟩

theorem filtered_prefix {Owner : Type} (P : RawPredicates Owner)
    (a : Owner) (φ : Formula Owner) (s : Assignment)
    (membership : ∀ n, P a ((Formula.«prefix» a n φ).close s))
    (hφ : filteredTruth P φ s) (n : Nat) :
    filteredTruth P (Formula.«prefix» a n φ) s := by
  induction n with
  | zero => exact hφ
  | succ n ih => exact ⟨membership n, ih⟩

end Alexander313
