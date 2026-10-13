import Alexander313.FullRecordedAdmissions

/-!
# Finite lists describe exactly the literal own-prefix closure

The closure here is constructed by the actual indexed-prefix rule. A finite
list representation is proved equivalent, with whole-formula admissibility
checking every prefix bound. Both existing recorded tables are exact instances.
No unrestricted necessitation or additional generator-admission contract is used.
-/

namespace Alexander313
namespace Formula

def indexedPrefix {Label : Type} (a : Nat) (L : List Label)
    (φ : Formula (RecordedHead Nat Label)) : Formula (RecordedHead Nat Label) :=
  L.foldr (fun ν ψ => .know (.indexed a ν) ψ) φ

@[simp] theorem indexedPrefix_closed {Label : Type} (a : Nat) (L : List Label)
    (φ : Formula (RecordedHead Nat Label)) : (indexedPrefix a L φ).Closed ↔ φ.Closed := by
  induction L <;> simp_all [indexedPrefix, Closed, freeVars]

@[simp] theorem indexedPrefix_support {Label : Type} [DecidableEq Label]
    (a : Nat) (L : List Label) (φ : Formula (RecordedHead Nat Label)) :
    (indexedPrefix a L φ).labelSupport = L.toFinset ∪ φ.labelSupport := by
  induction L with
  | nil => simp [indexedPrefix]
  | cons ν L ih =>
    change insert ν (indexedPrefix a L φ).labelSupport = (ν :: L).toFinset ∪ φ.labelSupport
    rw [ih]
    simp [Finset.insert_union]

/-- All prefix labels descend strictly, and each dominates the complete
    original support; checking only the outer prefix would be insufficient. -/
theorem indexedPrefix_admissible_iff {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (L : List Label) (φ : Formula (RecordedHead Nat Label)) :
    (indexedPrefix a L φ).RecordedAdmissible A E ↔
      φ.RecordedAdmissible A E ∧ (∀ ν ∈ L, a ∈ A) ∧
        L.Pairwise (fun ν μ => μ < ν) ∧ ∀ ν ∈ L, ∀ μ ∈ φ.labelSupport, μ < ν := by
  induction L with
  | nil => simp [indexedPrefix]
  | cons ν L ih =>
    rw [show indexedPrefix a (ν :: L) φ = .know (.indexed a ν) (indexedPrefix a L φ) from rfl,
      recordedAdmissible_know_indexed, ih, indexedPrefix_support]
    simp only [List.forall_mem_cons, List.pairwise_cons, Finset.mem_union,
      List.mem_toFinset, or_imp, forall_and]
    tauto

theorem indexedPrefix_below_iff {Label : Type} [DecidableEq Label] [LT Label]
    (a : Nat) (L : List Label) (φ : Formula (RecordedHead Nat Label)) (δ : Label) :
    (∀ μ ∈ (indexedPrefix a L φ).labelSupport, μ < δ) ↔
      (∀ ν ∈ L, ν < δ) ∧ ∀ μ ∈ φ.labelSupport, μ < δ := by
  rw [indexedPrefix_support]
  simp only [Finset.mem_union, List.mem_toFinset, or_imp, forall_and]

end Formula

inductive RecordedPrefixClosure {Label : Type} [DecidableEq Label] [LT Label]
    (A : Finset Nat) (a : Nat) (base : Formula (RecordedHead Nat Label) → Prop) :
    Formula (RecordedHead Nat Label) → Prop where
  | base {φ} : base φ → RecordedPrefixClosure A a base φ
  | «prefix» {φ} (ν : Label) : a ∈ A → RecordedPrefixClosure A a base φ →
      (∀ μ ∈ φ.labelSupport, μ < ν) →
      RecordedPrefixClosure A a base (.know (.indexed a ν) φ)

namespace RecordedPrefixClosure

variable {Label : Type} [DecidableEq Label] [LT Label]
    {A : Finset Nat} {a : Nat} {base : Formula (RecordedHead Nat Label) → Prop}

theorem closed (hbase : ∀ φ, base φ → φ.Closed)
    {φ : Formula (RecordedHead Nat Label)} (h : RecordedPrefixClosure A a base φ) : φ.Closed := by
  induction h with
  | base h => exact hbase _ h
  | «prefix» ν ha h below ih => exact ih

theorem admissible (E : Finset Nat) (hbase : ∀ φ, base φ → φ.RecordedAdmissible A E)
    {φ : Formula (RecordedHead Nat Label)} (h : RecordedPrefixClosure A a base φ) :
    φ.RecordedAdmissible A E := by
  induction h with
  | base h => exact hbase _ h
  | «prefix» ν ha h below ih =>
    exact (Formula.recordedAdmissible_know_indexed A E a ν _).mpr ⟨ha, ih, below⟩

theorem of_list (E : Finset Nat) (L : List Label) (φ : Formula (RecordedHead Nat Label))
    (hbase : base φ) (hadm : (Formula.indexedPrefix a L φ).RecordedAdmissible A E) :
    RecordedPrefixClosure A a base (Formula.indexedPrefix a L φ) := by
  revert hadm
  induction L with
  | nil => intro _; exact .base hbase
  | cons ν L ih =>
    intro hadm
    obtain ⟨ha, inner, below⟩ := (Formula.recordedAdmissible_know_indexed A E a ν _).mp hadm
    exact .«prefix» ν ha (ih inner) below

theorem exists_list (E : Finset Nat) (hbase : ∀ φ, base φ → φ.RecordedAdmissible A E)
    {φ : Formula (RecordedHead Nat Label)} (h : RecordedPrefixClosure A a base φ) :
    ∃ θ L, base θ ∧ φ = Formula.indexedPrefix a L θ ∧ φ.RecordedAdmissible A E := by
  induction h with
  | base h => exact ⟨_, [], h, rfl, hbase _ h⟩
  | «prefix» ν ha h below ih =>
    obtain ⟨θ, L, ht, he, hadm⟩ := ih
    refine ⟨θ, ν :: L, ht, ?_, ?_⟩
    · exact congrArg (Formula.know (.indexed a ν)) he
    · exact (Formula.recordedAdmissible_know_indexed A E a ν _).mpr ⟨ha, hadm, below⟩

theorem iff_list (E : Finset Nat) (hbase : ∀ φ, base φ → φ.RecordedAdmissible A E)
    (φ : Formula (RecordedHead Nat Label)) :
    RecordedPrefixClosure A a base φ ↔
      ∃ θ L, base θ ∧ φ = Formula.indexedPrefix a L θ ∧ φ.RecordedAdmissible A E := by
  refine ⟨fun h => h.exists_list E hbase, ?_⟩
  rintro ⟨θ, L, ht, rfl, hadm⟩
  exact of_list E L θ ht hadm

end RecordedPrefixClosure

namespace RecordedAdmissions

theorem iff_prefixClosure {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (R₁ : Label → Label → Prop)
    (φ : Formula (RecordedHead Nat Label)) :
    RecordedAdmissions A E a R₁ φ ↔
      RecordedPrefixClosure A a (RecordedBackground A E a R₁) φ := by
  constructor
  · intro h
    induction h with
    | background h => exact .base h
    | «prefix» ν ha h below ih => exact .«prefix» ν ha ih below
  · intro h
    induction h with
    | base h => exact .background h
    | «prefix» ν ha h below ih => exact .«prefix» ν ha ih below

end RecordedAdmissions

namespace FullRecordedAdmissions

theorem iff_prefixClosure {Label : Type} [DecidableEq Label] [LT Label]
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat) (a : Nat) (R₁ R₂ : Label → Label → Prop)
    (φ : Formula (RecordedHead Nat Label)) :
    FullRecordedAdmissions C A E a R₁ R₂ φ ↔
      RecordedPrefixClosure A a (fun θ =>
        RecordedBackground A E a R₁ θ ∨ RecordedMain C A E a R₁ R₂ θ) φ := by
  constructor
  · intro h
    induction h with
    | background h => exact .base (Or.inl h)
    | main h => exact .base (Or.inr h)
    | «prefix» ν ha h below ih => exact .«prefix» ν ha ih below
  · intro h
    induction h with
    | base h => exact h.elim FullRecordedAdmissions.background FullRecordedAdmissions.main
    | «prefix» ν ha h below ih => exact .«prefix» ν ha ih below

end FullRecordedAdmissions
end Alexander313
