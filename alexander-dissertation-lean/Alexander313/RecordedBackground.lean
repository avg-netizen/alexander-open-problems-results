import Alexander313.RecordedContexts
import Alexander313.CommonCoreAssembly

/-!
# Actual recorded background and contextual-collapse generators

This constructs the background rows of note 24's generator table. Active
owners are indexed; ghosts are restricted to the finite external set. All
formula contexts obey global nesting. Every admitted recorded validity is an
actual validity, never a validity inferred from its erasure. Concrete finite
pattern maps preserve these admissions; no generator-invariance contract is
assumed. The guarded main mechanicalness/code rows are separate unfinished
work, not silently included in this background subsystem.
-/

namespace Alexander313

namespace RecordedHead

def Allowed {Label : Type} (A E : Finset Nat) : RecordedHead Nat Label → Prop
  | .live a => a ∉ A
  | .indexed a _ => a ∈ A
  | .ghost a => a ∈ E ∧ a ∉ A

@[simp] theorem allowed_mapLabel {Label Other : Type} (A E : Finset Nat)
    (a : RecordedHead Nat Label) (f : Label → Other) :
    (a.mapLabel f).Allowed A E ↔ a.Allowed A E := by
  cases a <;> rfl

end RecordedHead

namespace Formula

def HeadsAllowed {Label : Type} (A E : Finset Nat) : Formula (RecordedHead Nat Label) → Prop
  | .falsum => True
  | .equal _ _ => True
  | .imp φ ψ => φ.HeadsAllowed A E ∧ ψ.HeadsAllowed A E
  | .conj φ ψ => φ.HeadsAllowed A E ∧ ψ.HeadsAllowed A E
  | .disj φ ψ => φ.HeadsAllowed A E ∧ ψ.HeadsAllowed A E
  | .neg φ => φ.HeadsAllowed A E
  | .all _ φ => φ.HeadsAllowed A E
  | .ex _ φ => φ.HeadsAllowed A E
  | .know a φ => a.Allowed A E ∧ φ.HeadsAllowed A E

@[simp] theorem headsAllowed_subst {Label : Type} (A E : Finset Nat)
    (φ : Formula (RecordedHead Nat Label)) (σ : NumericalSubstitution) :
    (φ.subst σ).HeadsAllowed A E ↔ φ.HeadsAllowed A E := by
  induction φ generalizing σ <;> simp_all [subst, HeadsAllowed]

@[simp] theorem headsAllowed_close {Label : Type} (A E : Finset Nat)
    (φ : Formula (RecordedHead Nat Label)) (s : Assignment) :
    (φ.close s).HeadsAllowed A E ↔ φ.HeadsAllowed A E :=
  headsAllowed_subst A E φ _

@[simp] theorem headsAllowed_relabel {Label Other : Type} (A E : Finset Nat)
    (φ : Formula (RecordedHead Nat Label)) (f : Label → Other) :
    (φ.relabel f).HeadsAllowed A E ↔ φ.HeadsAllowed A E := by
  induction φ <;> simp_all [relabel, mapOwner, HeadsAllowed, RecordedHead.allowed_mapLabel]

@[simp] theorem headsAllowed_all_foldr {Label : Type} (A E : Finset Nat)
    (xs : List Nat) (φ : Formula (RecordedHead Nat Label)) :
    (xs.foldr Formula.all φ).HeadsAllowed A E ↔ φ.HeadsAllowed A E := by
  induction xs <;> simp_all [HeadsAllowed]

@[simp] theorem headsAllowed_universalClosure {Label : Type} (A E : Finset Nat)
    (φ : Formula (RecordedHead Nat Label)) :
    φ.universalClosure.HeadsAllowed A E ↔ φ.HeadsAllowed A E :=
  headsAllowed_all_foldr A E _ φ

@[simp] theorem globallyStratified_all_foldr {Owner Label : Type} [DecidableEq Label] [LT Label]
    (xs : List Nat) (φ : Formula (RecordedHead Owner Label)) :
    (xs.foldr Formula.all φ).GloballyStratified ↔ φ.GloballyStratified := by
  induction xs <;> simp_all [GloballyStratified]

@[simp] theorem globallyStratified_universalClosure {Owner Label : Type}
    [DecidableEq Label] [LT Label] (φ : Formula (RecordedHead Owner Label)) :
    φ.universalClosure.GloballyStratified ↔ φ.GloballyStratified :=
  globallyStratified_all_foldr _ φ

def RecordedAdmissible {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (φ : Formula (RecordedHead Nat Label)) : Prop :=
  φ.HeadsAllowed A E ∧ φ.GloballyStratified

@[simp] theorem recordedAdmissible_know_indexed {Label : Type}
    [DecidableEq Label] [LT Label] (A E : Finset Nat) (a : Nat) (ν : Label)
    (φ : Formula (RecordedHead Nat Label)) :
    (Formula.know (.indexed a ν) φ).RecordedAdmissible A E ↔
      a ∈ A ∧ φ.RecordedAdmissible A E ∧ ∀ μ ∈ φ.labelSupport, μ < ν := by
  simp only [RecordedAdmissible, HeadsAllowed, RecordedHead.Allowed, GloballyStratified]
  tauto

theorem recordedAdmissible_chain {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (Γ : List (Formula (RecordedHead Nat Label)))
    (φ : Formula (RecordedHead Nat Label)) (hφ : φ.RecordedAdmissible A E)
    (hΓ : ∀ θ ∈ Γ, θ.RecordedAdmissible A E) :
    (chain Γ φ).RecordedAdmissible A E := by
  revert hΓ
  induction Γ with
  | nil => intro _; exact hφ
  | cons θ Γ ih =>
    intro hΓ
    have ht := hΓ θ List.mem_cons_self
    have hr := ih (fun η hη => hΓ η (List.mem_cons_of_mem _ hη))
    exact ⟨⟨ht.1, hr.1⟩, ht.2, hr.2⟩

@[simp] theorem recordedAdmissible_close {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (φ : Formula (RecordedHead Nat Label)) (s : Assignment) :
    (φ.close s).RecordedAdmissible A E ↔ φ.RecordedAdmissible A E := by
  simp only [RecordedAdmissible, headsAllowed_close, globallyStratified_close]

@[simp] theorem recordedAdmissible_universalClosure {Label : Type}
    [DecidableEq Label] [LT Label] (A E : Finset Nat)
    (φ : Formula (RecordedHead Nat Label)) :
    φ.universalClosure.RecordedAdmissible A E ↔ φ.RecordedAdmissible A E := by
  simp only [RecordedAdmissible, headsAllowed_universalClosure, globallyStratified_universalClosure]

theorem recordedAdmissible_relabel {Label Other : Type} [LinearOrder Label] [LinearOrder Other]
    (A E : Finset Nat) (φ : Formula (RecordedHead Nat Label)) (f : Label → Other)
    (strict : ∀ μ ∈ φ.labelSupport, ∀ ν ∈ φ.labelSupport, μ < ν → f μ < f ν)
    (hφ : φ.RecordedAdmissible A E) : (φ.relabel f).RecordedAdmissible A E :=
  ⟨(headsAllowed_relabel A E φ f).mpr hφ.1, φ.globallyStratified_relabel f strict hφ.2⟩

def indexedDeduction {Label : Type} (a : Nat) (ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) : Formula (RecordedHead Nat Label) :=
  (Formula.imp (.know (.indexed a ν) (.imp φ ψ))
    (.imp (.know (.indexed a ν) φ) (.know (.indexed a ν) ψ))).universalClosure

def indexedIntrospection {Label : Type} (a : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) : Formula (RecordedHead Nat Label) :=
  (Formula.imp (.know (.indexed a μ) φ)
    (.know (.indexed a ν) (.know (.indexed a μ) φ))).universalClosure

@[simp] theorem indexedDeduction_relabel {Label Other : Type} (a : Nat) (ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label)) (f : Label → Other) :
    (indexedDeduction a ν φ ψ).relabel f =
      indexedDeduction a (f ν) (φ.relabel f) (ψ.relabel f) := by
  simp only [indexedDeduction, relabel, mapOwner_universalClosure, mapOwner, RecordedHead.mapLabel]

@[simp] theorem indexedIntrospection_relabel {Label Other : Type} (a : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (f : Label → Other) :
    (indexedIntrospection a μ ν φ).relabel f =
      indexedIntrospection a (f μ) (f ν) (φ.relabel f) := by
  simp only [indexedIntrospection, relabel, mapOwner_universalClosure, mapOwner, RecordedHead.mapLabel]

theorem indexedIntrospection_inner_mem {Label : Type} [DecidableEq Label]
    (a : Nat) (μ ν : Label) (φ : Formula (RecordedHead Nat Label)) :
    μ ∈ (indexedIntrospection a μ ν φ).labelSupport := by
  simp [indexedIntrospection, labelSupport]

theorem indexedIntrospection_outer_mem {Label : Type} [DecidableEq Label]
    (a : Nat) (μ ν : Label) (φ : Formula (RecordedHead Nat Label)) :
    ν ∈ (indexedIntrospection a μ ν φ).labelSupport := by
  simp [indexedIntrospection, labelSupport]

end Formula

inductive RecordedBackground {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (R₁ : Label → Label → Prop) :
    Formula (RecordedHead Nat Label) → Prop where
  | arithmetic {σ} : PAInstance (RecordedHead Nat Label) σ →
      σ.RecordedAdmissible A E → RecordedBackground A E a R₁ σ
  | assigned (φ : Formula (RecordedHead Nat Label)) (s : Assignment) :
      Valid φ → φ.RecordedAdmissible A E → RecordedBackground A E a R₁ (φ.close s)
  | own_validity (ν : Label) (φ : Formula (RecordedHead Nat Label)) :
      Valid φ → (Formula.universalClosure (.know (.indexed a ν) φ)).RecordedAdmissible A E →
      RecordedBackground A E a R₁ (Formula.universalClosure (.know (.indexed a ν) φ))
  | deduction (ν : Label) (φ ψ : Formula (RecordedHead Nat Label)) :
      (Formula.indexedDeduction a ν φ ψ).RecordedAdmissible A E →
      RecordedBackground A E a R₁ (Formula.indexedDeduction a ν φ ψ)
  | introspection (μ ν : Label) (φ : Formula (RecordedHead Nat Label)) :
      μ < ν → (Formula.indexedIntrospection a μ ν φ).RecordedAdmissible A E →
      RecordedBackground A E a R₁ (Formula.indexedIntrospection a μ ν φ)
  | reflection (b : RecordedHead Nat Label) (φ : Formula (RecordedHead Nat Label)) :
      (reflection b φ).RecordedAdmissible A E → RecordedBackground A E a R₁ (reflection b φ)
  | contextual (c : Formula.Context (RecordedHead Nat Label)) (b : Nat) (μ ν : Label)
      (φ : Formula (RecordedHead Nat Label)) : R₁ μ ν →
      (Formula.contextualCollapse c b μ ν φ).RecordedAdmissible A E →
      RecordedBackground A E a R₁ (Formula.contextualCollapse c b μ ν φ)

namespace RecordedBackground

variable {Label : Type} [DecidableEq Label] [LT Label]
  {A E : Finset Nat} {a : Nat} {R₁ : Label → Label → Prop}

theorem closed {σ : Formula (RecordedHead Nat Label)}
    (h : RecordedBackground A E a R₁ σ) : σ.Closed := by
  cases h with
  | arithmetic h _ => exact h.closed
  | assigned φ s _ _ => exact φ.close_closed s
  | own_validity ν φ _ _ => exact Formula.universalClosure_closed _
  | deduction ν φ ψ _ => exact Formula.universalClosure_closed _
  | introspection μ ν φ _ _ => exact Formula.universalClosure_closed _
  | reflection b φ _ => exact Formula.universalClosure_closed _
  | contextual c b μ ν φ _ _ => exact Formula.universalClosure_closed _

theorem admissible {σ : Formula (RecordedHead Nat Label)}
    (h : RecordedBackground A E a R₁ σ) : σ.RecordedAdmissible A E := by
  cases h with
  | assigned φ s hv ha => exact (Formula.recordedAdmissible_close A E φ s).mpr ha
  | arithmetic hp ha => exact ha
  | own_validity ν φ hv ha => exact ha
  | deduction ν φ ψ ha => exact ha
  | introspection μ ν φ hμν ha => exact ha
  | reflection b φ ha => exact ha
  | contextual c b μ ν φ hμν ha => exact ha

/-- All structural/background erasures are actual source members. Contextual
    collapse erases to a validity and does not require source soundness. -/
theorem erased_member {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    {σ : Formula (RecordedHead Nat Label)} (h : RecordedBackground A E a R₁ σ) :
    C.family.effective.proves a σ.erase := by
  cases h with
  | arithmetic hp ha =>
    exact C.background_member a (.arithmetic (hp.mapOwner RecordedHead.erase))
  | assigned φ s hv ha =>
    simpa only [Formula.erase, Formula.mapOwner_close] using
      C.background_member a (.assigned φ.erase s hv.erase)
  | own_validity ν φ hv ha =>
    simpa only [Formula.erase, Formula.mapOwner_universalClosure, Formula.mapOwner,
      RecordedHead.erase] using
      C.background_member a (.structural (.validity φ.erase hv.erase))
  | deduction ν φ ψ ha =>
    simpa only [Formula.indexedDeduction, Formula.erase, Formula.mapOwner_universalClosure,
      Formula.mapOwner, RecordedHead.erase] using
      C.background_member a (.structural (.reasoning φ.erase ψ.erase))
  | introspection μ ν φ hμν ha =>
    simpa only [Formula.indexedIntrospection, Formula.erase, Formula.mapOwner_universalClosure,
      Formula.mapOwner, RecordedHead.erase] using
      C.background_member a (.structural (.introspection φ.erase))
  | reflection b φ ha =>
    simpa only [Formula.erase, mapOwner_reflection] using
      C.background_member a (.reflection b.erase φ.erase)
  | contextual c b μ ν φ hμν ha =>
    apply (C.family.theory_closed a _ ((Formula.closed_erase _).mpr
      (Formula.universalClosure_closed _))).mp
    exact Provable.of_valid (Formula.contextualCollapse_erasure_valid c b μ ν φ)

end RecordedBackground

namespace RecordedBackground

variable {Label : Type} [LinearOrder Label] {A E : Finset Nat} {a : Nat}
  {R₁ R₂ : Label → Label → Prop}

/-- This proves actual background generator preservation. The only pattern
    hypothesis describes the finite labels themselves, not generator admission. -/
theorem relabel (F : Finset Label) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f)
    {σ : Formula (RecordedHead Nat Label)} (h : RecordedBackground A E a R₁ σ)
    (support : σ.labelSupport ⊆ F) : RecordedBackground A E a R₁ (σ.relabel f) := by
  have admissible := σ.recordedAdmissible_relabel A E f
    (fun μ hμ ν hν hμν => (pattern.2.1 μ (support hμ) ν (support hν)).mpr hμν) h.admissible
  cases h with
  | arithmetic hp ha => exact .arithmetic (hp.mapOwner (RecordedHead.mapLabel f)) admissible
  | assigned φ s hv ha =>
    have supportφ : φ.labelSupport ⊆ F := by simpa only [Formula.labelSupport_close] using support
    rw [Formula.relabel_close]
    exact .assigned (φ.relabel f) s (hv.mapOwner (RecordedHead.mapLabel f))
      (φ.recordedAdmissible_relabel A E f
        (fun μ hμ ν hν hμν => (pattern.2.1 μ (supportφ hμ) ν (supportφ hν)).mpr hμν) ha)
  | own_validity ν φ hv ha =>
    simp only [Formula.relabel_universalClosure, Formula.relabel, Formula.mapOwner_universalClosure,
      Formula.mapOwner,
      RecordedHead.mapLabel] at admissible ⊢
    exact .own_validity (f ν) (φ.relabel f)
      (hv.mapOwner (RecordedHead.mapLabel f)) admissible
  | deduction ν φ ψ ha =>
    rw [Formula.indexedDeduction_relabel] at admissible ⊢
    exact .deduction (f ν) (φ.relabel f) (ψ.relabel f) admissible
  | introspection μ ν φ hμν ha =>
    have hm := support (Formula.indexedIntrospection_inner_mem a μ ν φ)
    have hn := support (Formula.indexedIntrospection_outer_mem a μ ν φ)
    rw [Formula.indexedIntrospection_relabel] at admissible ⊢
    exact .introspection (f μ) (f ν) (φ.relabel f) ((pattern.2.1 μ hm ν hn).mpr hμν) admissible
  | reflection b φ ha =>
    change RecordedBackground A E a R₁
      ((Alexander313.reflection b φ).mapOwner (RecordedHead.mapLabel f))
    rw [mapOwner_reflection]
    exact .reflection (b.mapLabel f) (φ.relabel f) (by
      simpa only [Formula.relabel, mapOwner_reflection] using admissible)
  | contextual c b μ ν φ hμν ha =>
    have hm := support (Formula.contextualCollapse_left_mem c b μ ν φ)
    have hn := support (Formula.contextualCollapse_right_mem c b μ ν φ)
    rw [Formula.contextualCollapse_relabel] at admissible ⊢
    exact .contextual (c.mapOwner (RecordedHead.mapLabel f)) b (f μ) (f ν) (φ.relabel f)
      (pattern.2.2.1 μ hm ν hn hμν) admissible

end RecordedBackground
end Alexander313
