import Alexander313.RecordedGuardRoom

/-!
# Concrete finite certificate plans from source syntax and bounded chains

Source shapes give the finite nesting and cut inequalities on the actual
ordinal label table. Disjoint policies determine allowed heads. Literal main
atoms give the exact guard requirements, whose bounded chain witnesses
construct the finite marker sets. Combining these checks with the actual
source constructors yields the earlier finite lift data and hence real cut
proofs. No recorded-admission, marker-set, recovery or body-truth oracle is an
input here. Existence of a table satisfying the finite ordinal constraints,
with prescribed goal entries fixed, remains a separate construction.
-/

namespace Alexander313

namespace Shape

/-- The table entries remain genuine labels. This recursive finite condition
compares every active descendant query with the whole original argument. -/
def labelNesting {Label : Type} [LT Label] (A : Finset Nat)
    (labels : Nat → Shape Nat → Label) : Shape Nat → Prop
  | .falsum => True
  | .equal => True
  | .imp φ ψ => labelNesting A labels φ ∧ labelNesting A labels ψ
  | .conj φ ψ => labelNesting A labels φ ∧ labelNesting A labels ψ
  | .disj φ ψ => labelNesting A labels φ ∧ labelNesting A labels ψ
  | .neg φ => labelNesting A labels φ
  | .all φ => labelNesting A labels φ
  | .ex φ => labelNesting A labels φ
  | .know a φ => labelNesting A labels φ ∧
      (a ∈ A → ∀ q ∈ φ.queries, q.1 ∈ A → labels q.1 q.2 < labels a φ)

def labelBounds {Label : Type} [LT Label] (A : Finset Nat)
    (labels : Nat → Shape Nat → Label) (δ : Label) (φ : Shape Nat) : Prop :=
  ∀ q ∈ φ.queries, q.1 ∈ A → labels q.1 q.2 < δ

end Shape

theorem mainHeads_allowed {Label : Type} (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (disjoint : Disjoint A E) (a : Nat) (sh : Shape Nat) :
    (mainHeads A E H labels a sh).Allowed A E := by
  by_cases he : a ∈ E
  · have ha : a ∉ A := fun ha => Finset.disjoint_left.mp disjoint ha he
    by_cases hh : (a, sh) ∈ H <;>
      simp [mainHeads, maskedHeads, he, ha, hh, RecordedHead.Allowed]
  · by_cases ha : a ∈ A <;>
      simp [mainHeads, maskedHeads, he, ha, RecordedHead.Allowed]

namespace Formula

variable {Label : Type} [LinearOrder Label]

theorem record_headsAllowed (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (disjoint : Disjoint A E) (φ : Formula Nat) :
    (φ.record (mainHeads A E H labels)).HeadsAllowed A E := by
  induction φ with
  | falsum => trivial
  | equal t u => trivial
  | imp φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | neg φ ih => exact ih
  | all x φ ih => exact ih
  | ex x φ ih => exact ih
  | know a φ ih => exact ⟨mainHeads_allowed A E H labels disjoint a φ.shape, ih⟩

/-- Every label of the whole recorded formula comes from an active original
owner/argument-shape query, including queries below live and ghost heads. -/
theorem record_support_source_query (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (disjoint : Disjoint A E) (φ : Formula Nat)
    (μ : Label) (hμ : μ ∈ (φ.record (mainHeads A E H labels)).labelSupport) :
    ∃ (a : Nat) (sh : Shape Nat), (a, sh) ∈ φ.queries ∧ a ∈ A ∧ μ = labels a sh := by
  revert hμ
  induction φ with
  | falsum => intro hμ; simp [record, labelSupport] at hμ
  | equal t u => intro hμ; simp [record, labelSupport] at hμ
  | imp φ ψ ihφ ihψ =>
    intro hμ
    rcases Finset.mem_union.mp hμ with hφ | hψ
    · obtain ⟨a, sh, hq, ha, he⟩ := ihφ hφ
      exact ⟨a, sh, Finset.mem_union_left _ hq, ha, he⟩
    · obtain ⟨a, sh, hq, ha, he⟩ := ihψ hψ
      exact ⟨a, sh, Finset.mem_union_right _ hq, ha, he⟩
  | conj φ ψ ihφ ihψ =>
    intro hμ
    rcases Finset.mem_union.mp hμ with hφ | hψ
    · obtain ⟨a, sh, hq, ha, he⟩ := ihφ hφ
      exact ⟨a, sh, Finset.mem_union_left _ hq, ha, he⟩
    · obtain ⟨a, sh, hq, ha, he⟩ := ihψ hψ
      exact ⟨a, sh, Finset.mem_union_right _ hq, ha, he⟩
  | disj φ ψ ihφ ihψ =>
    intro hμ
    rcases Finset.mem_union.mp hμ with hφ | hψ
    · obtain ⟨a, sh, hq, ha, he⟩ := ihφ hφ
      exact ⟨a, sh, Finset.mem_union_left _ hq, ha, he⟩
    · obtain ⟨a, sh, hq, ha, he⟩ := ihψ hψ
      exact ⟨a, sh, Finset.mem_union_right _ hq, ha, he⟩
  | neg φ ih => intro hμ; exact ih hμ
  | all x φ ih => intro hμ; exact ih hμ
  | ex x φ ih => intro hμ; exact ih hμ
  | know a φ ih =>
    intro hμ
    have inner (h : μ ∈ (φ.record (mainHeads A E H labels)).labelSupport) :
        ∃ b sh, (b, sh) ∈ (Formula.know a φ).queries ∧ b ∈ A ∧ μ = labels b sh := by
      obtain ⟨b, sh, hq, hb, he⟩ := ih h
      exact ⟨b, sh, Finset.mem_insert_of_mem hq, hb, he⟩
    by_cases he : a ∈ E
    · have ha : a ∉ A := fun ha => Finset.disjoint_left.mp disjoint ha he
      by_cases hh : (a, φ.shape) ∈ H
      · apply inner
        simpa only [record, mainHeads, maskedHeads, he, hh, ↓reduceIte, labelSupport] using hμ
      · apply inner
        simpa only [record, mainHeads, maskedHeads, he, hh, ↓reduceIte, labelSupport] using hμ
    · by_cases ha : a ∈ A
      · have hm : μ ∈ insert (labels a φ.shape)
            (φ.record (mainHeads A E H labels)).labelSupport := by
          simpa only [record, mainHeads, maskedHeads, he, ha, ↓reduceIte, labelSupport] using hμ
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact ⟨a, φ.shape, Finset.mem_insert_self _ _, ha, rfl⟩
        · exact inner hm
      · apply inner
        simpa only [record, mainHeads, maskedHeads, he, ha, ↓reduceIte, labelSupport] using hμ

theorem record_support_below (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (disjoint : Disjoint A E)
    (φ : Formula Nat) (δ : Label) (bounds : φ.shape.labelBounds A labels δ) :
    ∀ μ ∈ (φ.record (mainHeads A E H labels)).labelSupport, μ < δ := by
  intro μ hμ
  obtain ⟨a, sh, hq, ha, rfl⟩ := record_support_source_query A E H labels disjoint φ μ hμ
  exact bounds (a, sh) (by simpa only [queries_shape] using hq) ha

theorem record_globallyStratified (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (disjoint : Disjoint A E) (φ : Formula Nat)
    (nesting : φ.shape.labelNesting A labels) :
    (φ.record (mainHeads A E H labels)).GloballyStratified := by
  revert nesting
  induction φ with
  | falsum => intro _; trivial
  | equal t u => intro _; trivial
  | imp φ ψ ihφ ihψ => intro nesting; exact ⟨ihφ nesting.1, ihψ nesting.2⟩
  | conj φ ψ ihφ ihψ => intro nesting; exact ⟨ihφ nesting.1, ihψ nesting.2⟩
  | disj φ ψ ihφ ihψ => intro nesting; exact ⟨ihφ nesting.1, ihψ nesting.2⟩
  | neg φ ih => intro nesting; exact ih nesting
  | all x φ ih => intro nesting; exact ih nesting
  | ex x φ ih => intro nesting; exact ih nesting
  | know a φ ih =>
    intro nesting
    have inner := ih nesting.1
    by_cases he : a ∈ E
    · by_cases hh : (a, φ.shape) ∈ H <;>
        simpa only [record, mainHeads, maskedHeads, he, hh, ↓reduceIte,
          GloballyStratified] using inner
    · by_cases ha : a ∈ A
      · have below : ∀ μ ∈ (φ.record (mainHeads A E H labels)).labelSupport,
            μ < labels a φ.shape := by
          intro μ hμ
          obtain ⟨b, sh, hq, hb, rfl⟩ :=
            record_support_source_query A E H labels disjoint φ μ hμ
          exact nesting.2 ha (b, sh) (by simpa only [queries_shape] using hq) hb
        simpa only [record, mainHeads, maskedHeads, he, ha, ↓reduceIte,
          GloballyStratified] using And.intro inner below
      · simpa only [record, mainHeads, maskedHeads, he, ha, ↓reduceIte,
          GloballyStratified] using inner

theorem record_admissible_of_labelNesting (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (disjoint : Disjoint A E) (φ : Formula Nat) (nesting : φ.shape.labelNesting A labels) :
    (φ.record (mainHeads A E H labels)).RecordedAdmissible A E :=
  ⟨record_headsAllowed A E H labels disjoint φ,
    record_globallyStratified A E H labels disjoint φ nesting⟩

end Formula

/-- Each main source constructor carries exactly its actual bounded guard
requirements. Background constructors carry their literal reasoning links.
Neither case carries a marker-point set or an admitted recorded formula. -/
inductive GeneratorRoomRequirements {Label : Type} [LinearOrder Label]
    {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (A E : Finset Nat)
    (a : Nat) (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (R₁ R₂ : Label → Label → Prop) (δ : Label) : Formula Nat → Prop where
  | background {σ} : BackgroundGenerator a σ → ReasoningLinks a labels R₁ σ →
      GeneratorRoomRequirements C A E a H labels R₁ R₂ δ σ
  | main {σ} (atom : Formula Nat) : RecordedMainSource C A E a σ atom →
      GuardRequirements.Bounded R₁ R₂ δ
        ((atom.record (mainHeads A E H labels)).mainGuardRequirements E) →
      GeneratorRoomRequirements C A E a H labels R₁ R₂ δ σ

namespace GeneratorRoomRequirements

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} {A E : Finset Nat} {a : Nat}
    {H : Finset (Nat × Shape Nat)} {labels : Nat → Shape Nat → Label}
    {R₁ R₂ : Label → Label → Prop} {δ : Label} {σ : Formula Nat}

theorem exists_lift_data (requirements : GeneratorRoomRequirements C A E a H labels R₁ R₂ δ σ) :
    ∃ B : Finset Label, GeneratorLiftData C A E a H labels R₁ R₂ B σ ∧
      ∀ μ ∈ B, μ < δ := by
  cases requirements with
  | background source links =>
    exact ⟨∅, .background source links, fun μ hμ => False.elim (Finset.notMem_empty μ hμ)⟩
  | main atom source bounded =>
    obtain ⟨B, guard, room⟩ :=
      (Formula.mainGuardRequirements_bounded_iff R₁ R₂ E δ _).mp bounded
    exact ⟨B, .main atom source guard, room⟩

end GeneratorRoomRequirements

/-- All table checks refer to the original whole premise shape. Guard chains
are bounded by the actual base-row cut, before any own prefixes are lifted. -/
def FiniteLiftRequirements {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat) (a : Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (R₁ R₂ : Label → Label → Prop) (δ : Label) (Γ : List (Formula Nat)) : Prop :=
  ∀ θ ∈ Γ, ∃ (σ : Formula Nat) (n : Nat), θ = Formula.«prefix» a n σ ∧
    GeneratorRoomRequirements C A E a H labels R₁ R₂ (sourceBaseCut a σ labels n δ) σ ∧
    θ.shape.labelNesting A labels ∧ θ.shape.labelBounds A labels δ

namespace FiniteLiftRequirements

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} {A E : Finset Nat} {a : Nat}
    {H : Finset (Nat × Shape Nat)} {labels : Nat → Shape Nat → Label}
    {R₁ R₂ : Label → Label → Prop} {δ : Label} {Γ : List (Formula Nat)}

theorem liftData (requirements : FiniteLiftRequirements C A E a H labels R₁ R₂ δ Γ)
    (disjoint : Disjoint A E) : FiniteLiftData C A E a H labels R₁ R₂ δ Γ := by
  intro θ hθ
  obtain ⟨σ, n, he, hr, hn, hb⟩ := requirements θ hθ
  obtain ⟨B, hd, room⟩ := hr.exists_lift_data
  exact ⟨σ, n, B, he, hd,
    Formula.record_admissible_of_labelNesting A E H labels disjoint θ hn,
    Formula.record_support_below A E H labels disjoint θ δ hb, room⟩

end FiniteLiftRequirements

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

theorem certificate_cuts_of_requirements (a : Nat) (δ : Label)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (ha : a ∈ A) (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    {φ : Formula Nat} (closed : φ.Closed)
    (c : Certificate (PrefixedAxioms a (CommonCoreGenerator R C.arithmetic C.family a)) φ)
    (requirements : FiniteLiftRequirements C A E a H labels R₁ R₂ δ c.premises) :
    cuts C A E R₁ R₂ a δ (φ.record (mainHeads A E H labels)) :=
  certificate_cuts C A E R₁ R₂ a δ H labels ha hereditary disjoint closed c
    (requirements.liftData disjoint)

theorem active_query_of_requirements (P : RawPredicates Nat) (a : Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (ha : a ∈ A) (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    (φ : Formula Nat) (s : Assignment)
    (c : Certificate (PrefixedAxioms a (CommonCoreGenerator R C.arithmetic C.family a))
      (φ.close s))
    (requirements : FiniteLiftRequirements C A E a H labels R₁ R₂
      (labels a φ.shape) c.premises) :
    reconstructedPredicates (mainHeads A E H labels) (predicates C A E R₁ R₂ P)
      a (φ.close s) :=
  active_query_of_certificate C A E R₁ R₂ P a H labels ha hereditary disjoint φ s c
    (requirements.liftData disjoint)

end RecordedStage
end Alexander313
