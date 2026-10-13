import Alexander313.RecordedLabelMaps

/-!
# Finite-support certificate transport and cut collapse

The support contains the conclusion and every premise, including marker and
derived-prefix premises. Only admissions of those actual finite premises need
transporting. The logical implication is transported by Alexander validity.
The final cut equivalence is the logical half of note 24 (3): finite expanded
pattern reflection and preservation of the actual source generators remain
explicit, unconstructed ordinal/source inputs. No converse-to-erasure validity
test or source-proof intersection is used.
-/

namespace Alexander313

namespace Formula

variable {Owner Label : Type} [DecidableEq Label]

theorem labelSupport_subset_chain (Γ : List (Formula (RecordedHead Owner Label)))
    (φ : Formula (RecordedHead Owner Label)) :
    φ.labelSupport ⊆ (chain Γ φ).labelSupport := by
  induction Γ with
  | nil => exact fun _ h => h
  | cons θ Γ ih => exact fun _ h => Finset.mem_union_right _ (ih h)

theorem premise_labelSupport_subset_chain
    (Γ : List (Formula (RecordedHead Owner Label)))
    (φ θ : Formula (RecordedHead Owner Label)) (hθ : θ ∈ Γ) :
    θ.labelSupport ⊆ (chain Γ φ).labelSupport := by
  revert hθ
  induction Γ with
  | nil => intro hθ; cases hθ
  | cons η Γ ih =>
    intro hθ
    rcases List.mem_cons.mp hθ with rfl | hθ
    · exact fun _ h => Finset.mem_union_left _ h
    · exact fun _ h => Finset.mem_union_right _ (ih hθ h)

theorem labelSupport_chain_below [LT Label]
    (Γ : List (Formula (RecordedHead Owner Label)))
    (φ : Formula (RecordedHead Owner Label)) (ν : Label)
    (target : ∀ μ ∈ φ.labelSupport, μ < ν)
    (premises : ∀ θ ∈ Γ, ∀ μ ∈ θ.labelSupport, μ < ν) :
    ∀ μ ∈ (chain Γ φ).labelSupport, μ < ν := by
  revert premises
  induction Γ with
  | nil => intro _; exact target
  | cons θ Γ ih =>
    intro premises μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · exact premises θ List.mem_cons_self μ hμ
    · exact ih (fun η hη => premises η (List.mem_cons_of_mem _ hη)) μ hμ

end Formula

namespace Certificate

variable {Owner Label : Type} [DecidableEq Label]

def labelSupport {axioms : Formula (RecordedHead Owner Label) → Prop}
    {φ : Formula (RecordedHead Owner Label)} (c : Certificate axioms φ) :
    Finset Label := (Formula.chain c.premises φ).labelSupport

theorem target_support {axioms : Formula (RecordedHead Owner Label) → Prop}
    {φ : Formula (RecordedHead Owner Label)} (c : Certificate axioms φ) :
    φ.labelSupport ⊆ c.labelSupport :=
  Formula.labelSupport_subset_chain c.premises φ

theorem premise_support {axioms : Formula (RecordedHead Owner Label) → Prop}
    {φ : Formula (RecordedHead Owner Label)} (c : Certificate axioms φ)
    {θ : Formula (RecordedHead Owner Label)} (hθ : θ ∈ c.premises) :
    θ.labelSupport ⊆ c.labelSupport :=
  Formula.premise_labelSupport_subset_chain c.premises φ θ hθ

/-- Unlike a global generator map, this requires admissions only for premises
    of the supplied finite certificate. Every numerical term is unchanged. -/
def relabelPremises {Other : Type}
    {axioms : Formula (RecordedHead Owner Label) → Prop}
    {target : Formula (RecordedHead Owner Other) → Prop}
    {φ : Formula (RecordedHead Owner Label)} (c : Certificate axioms φ)
    (f : Label → Other)
    (admission : ∀ θ ∈ c.premises, target (θ.relabel f)) :
    Certificate target (φ.relabel f) where
  premises := c.premises.map (fun θ => θ.relabel f)
  admitted := by
    intro θ hθ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hθ
    exact admission η hη
  validity := by
    simpa only [Formula.relabel, Formula.mapOwner_chain] using
      c.validity.mapOwner (RecordedHead.mapLabel f)

end Certificate

def LabelCut {Owner Label : Type} [DecidableEq Label] [LT Label]
    (generator : Formula (RecordedHead Owner Label) → Prop) (ν : Label)
    (φ : Formula (RecordedHead Owner Label)) : Prop :=
  generator φ ∧ ∀ μ ∈ φ.labelSupport, μ < ν

theorem labelCut_mono {Owner Label : Type} [LinearOrder Label]
    (generator : Formula (RecordedHead Owner Label) → Prop)
    {α β : Label} (hαβ : α ≤ β) :
    ∀ φ, LabelCut generator α φ → LabelCut generator β φ :=
  fun _ h => ⟨h.1, fun μ hμ => lt_of_lt_of_le (h.2 μ hμ) hαβ⟩

namespace Certificate

variable {Owner Label : Type} [LinearOrder Label]

theorem labelSupport_below
    {generator : Formula (RecordedHead Owner Label) → Prop} {β : Label}
    {φ : Formula (RecordedHead Owner Label)}
    (c : Certificate (LabelCut generator β) φ)
    (target : ∀ μ ∈ φ.labelSupport, μ < β) :
    ∀ μ ∈ c.labelSupport, μ < β :=
  Formula.labelSupport_chain_below c.premises φ β target
    (fun θ hθ => (c.admitted θ hθ).2)

def relabelCut {generator : Formula (RecordedHead Owner Label) → Prop}
    {α β : Label} {φ : Formula (RecordedHead Owner Label)}
    (c : Certificate (LabelCut generator β) φ) (f : Label → Label)
    (below : ∀ μ ∈ c.labelSupport, f μ < α)
    (admission : ∀ θ ∈ c.premises, generator (θ.relabel f)) :
    Certificate (LabelCut generator α) (φ.relabel f) :=
  c.relabelPremises f (by
    intro θ hθ
    refine ⟨admission θ hθ, ?_⟩
    intro μ hμ
    rw [Formula.labelSupport_relabel] at hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    exact below ν (c.premise_support hθ hν))

end Certificate

/-- Literal agreement of the expanded finite pattern, including equality,
    ordinal order and both extra source relations. -/
def PreservesLabelPattern {Label : Type} [LT Label]
    (R₁ R₂ : Label → Label → Prop) (F : Finset Label)
    (f : Label → Label) : Prop :=
  (∀ x ∈ F, ∀ y ∈ F, f x = f y ↔ x = y) ∧
  (∀ x ∈ F, ∀ y ∈ F, f x < f y ↔ x < y) ∧
  (∀ x ∈ F, ∀ y ∈ F, R₁ (f x) (f y) ↔ R₁ x y) ∧
  (∀ x ∈ F, ∀ y ∈ F, R₂ (f x) (f y) ↔ R₂ x y)

/-- The source finite-pattern reflection obligation. This is a proposition,
    not an asserted Wilken theorem or a new project axiom. -/
def FiniteLabelReflection {Label : Type} [LT Label]
    (R₁ R₂ : Label → Label → Prop) (α β : Label) : Prop :=
  ∀ F : Finset Label, (∀ x ∈ F, x < β) →
    ∃ f : Label → Label,
      (∀ x ∈ F, f x < α) ∧
      (∀ x ∈ F, x < α → f x = x) ∧
      PreservesLabelPattern R₁ R₂ F f

/-- Forward (covering) agreement of a finite pattern: equality and order are
    kept exactly, and both extra relations are carried forward. This is
    Carlson's notion of a covering (*Patterns of resemblance of order 2*,
    Definition 5.2). The stage argument only ever uses these directions. -/
def CoversLabelPattern {Label : Type} [LT Label]
    (R₁ R₂ : Label → Label → Prop) (F : Finset Label)
    (f : Label → Label) : Prop :=
  (∀ x ∈ F, ∀ y ∈ F, f x = f y ↔ x = y) ∧
  (∀ x ∈ F, ∀ y ∈ F, f x < f y ↔ x < y) ∧
  (∀ x ∈ F, ∀ y ∈ F, R₁ x y → R₁ (f x) (f y)) ∧
  (∀ x ∈ F, ∀ y ∈ F, R₂ x y → R₂ (f x) (f y))

/-- Finite reflection by coverings: every finite set below β has a copy below
    α that fixes its part below α and carries both relations forward. -/
def FiniteLabelCovering {Label : Type} [LT Label]
    (R₁ R₂ : Label → Label → Prop) (α β : Label) : Prop :=
  ∀ F : Finset Label, (∀ x ∈ F, x < β) →
    ∃ f : Label → Label,
      (∀ x ∈ F, f x < α) ∧
      (∀ x ∈ F, x < α → f x = x) ∧
      CoversLabelPattern R₁ R₂ F f

theorem PreservesLabelPattern.covers {Label : Type} [LT Label]
    {R₁ R₂ : Label → Label → Prop} {F : Finset Label} {f : Label → Label}
    (h : PreservesLabelPattern R₁ R₂ F f) : CoversLabelPattern R₁ R₂ F f :=
  ⟨h.1, h.2.1, fun x hx y hy => (h.2.2.1 x hx y hy).mpr,
    fun x hx y hy => (h.2.2.2 x hx y hy).mpr⟩

theorem FiniteLabelReflection.covering {Label : Type} [LT Label]
    {R₁ R₂ : Label → Label → Prop} {α β : Label}
    (h : FiniteLabelReflection R₁ R₂ α β) : FiniteLabelCovering R₁ R₂ α β := by
  intro F hF
  obtain ⟨f, below, fixed, pattern⟩ := h F hF
  exact ⟨f, below, fixed, pattern.covers⟩

/-- Exact logical support-collapse theorem. The remaining source work is to
    prove reflection and finite-pattern generator invariance for the actual
    recorded presentations, including their padded guards and prefixes. -/
theorem provable_labelCut_iff {Owner Label : Type} [LinearOrder Label]
    (generator : Formula (RecordedHead Owner Label) → Prop)
    (R₁ R₂ : Label → Label → Prop) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelCovering R₁ R₂ α β)
    (generators : ∀ (F : Finset Label) (f : Label → Label),
      CoversLabelPattern R₁ R₂ F f →
      ∀ θ, generator θ → θ.labelSupport ⊆ F → generator (θ.relabel f))
    (φ : Formula (RecordedHead Owner Label))
    (target : ∀ μ ∈ φ.labelSupport, μ < α) :
    Provable (LabelCut generator α) φ ↔ Provable (LabelCut generator β) φ := by
  constructor
  · exact fun h => h.mono (labelCut_mono generator hαβ)
  · intro h
    obtain ⟨c⟩ := h
    have all_below : ∀ μ ∈ c.labelSupport, μ < β :=
      c.labelSupport_below (fun μ hμ => lt_of_lt_of_le (target μ hμ) hαβ)
    obtain ⟨f, below, fixed, pattern⟩ := reflection c.labelSupport all_below
    have transport : Certificate (LabelCut generator α) (φ.relabel f) :=
      c.relabelCut f below (fun θ hθ =>
        generators c.labelSupport f pattern θ (c.admitted θ hθ).1
          (c.premise_support hθ))
    have hfixed : φ.relabel f = φ :=
      φ.relabel_fixed f (fun μ hμ => fixed μ (c.target_support hμ) (target μ hμ))
    rw [hfixed] at transport
    exact ⟨transport⟩

end Alexander313
