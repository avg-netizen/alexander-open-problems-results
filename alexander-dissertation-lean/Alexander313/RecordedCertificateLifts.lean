import Alexander313.RecordedGeneratorLifts

/-!
# Literal finite source certificates in actual recorded cuts

A single source-shared table records the whole certificate. Each main premise
has displayed finite guards and marker room below its first own-prefix label;
reasoning premises have their two literal contextual-collapse links. Prefix
admissibility supplies the remaining strict nesting bounds. These data yield
actual full-table cut proofs and actual indexed reconstructed acceptances.

This does not assert that every source certificate admits such a table and
finite room, or that a table chosen for a certificate agrees with a prescribed
retained goal table. Those are the remaining prescribed reverse-lift steps.
-/

namespace Alexander313

/-- A nonempty source prefix must already have its base certificate below the
innermost label. Using only the final cut would not justify necessitation. -/
def sourceBaseCut {Label : Type} (a : Nat) (σ : Formula Nat)
    (labels : Nat → Shape Nat → Label) : Nat → Label → Label
  | 0, δ => δ
  | _ + 1, _ => labels a σ.shape

namespace GeneratorLiftData

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} {A E : Finset Nat} {a : Nat}
    {H : Finset (Nat × Shape Nat)} {labels : Nat → Shape Nat → Label}
    {R₁ R₂ : Label → Label → Prop} {B : Finset Label} {σ : Formula Nat}

/-- The prefix labels are the literal table entries for the original source
prefix arguments. They are never recomputed from a recorded argument. -/
theorem prefix_cuts (data : GeneratorLiftData C A E a H labels R₁ R₂ B σ)
    (ha : a ∈ A) (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    (n : Nat) (δ : Label)
    (hadm : ((Formula.«prefix» a n σ).record (mainHeads A E H labels)).RecordedAdmissible A E)
    (below : ∀ μ ∈ ((Formula.«prefix» a n σ).record (mainHeads A E H labels)).labelSupport,
      μ < δ)
    (room : ∀ μ ∈ B, μ < sourceBaseCut a σ labels n δ) :
    RecordedStage.cuts C A E R₁ R₂ a δ
      ((Formula.«prefix» a n σ).record (mainHeads A E H labels)) := by
  revert hadm below room
  induction n generalizing δ with
  | zero =>
    intro hadm below room
    exact data.cuts ha hereditary disjoint δ hadm below room
  | succ n ih =>
    intro hadm below room
    let ν := labels a (Formula.«prefix» a n σ).shape
    have hrec : (Formula.«prefix» a (n + 1) σ).record (mainHeads A E H labels) =
        Formula.know (.indexed a ν)
          ((Formula.«prefix» a n σ).record (mainHeads A E H labels)) := by
      simp only [Formula.«prefix», Formula.record,
        mainHeads_active A E H labels a _ ha disjoint, ν]
    rw [hrec] at hadm below ⊢
    obtain ⟨_, innerAdm, innerBelow⟩ :=
      (Formula.recordedAdmissible_know_indexed A E a ν _).mp hadm
    have νδ : ν < δ := below ν (Finset.mem_insert_self _ _)
    have innerRoom : ∀ μ ∈ B, μ < sourceBaseCut a σ labels n ν := by
      cases n with
      | zero => simpa only [sourceBaseCut, ν, Formula.«prefix»] using room
      | succ n => simpa only [sourceBaseCut] using room
    exact RecordedStage.cuts_prefix C A E R₁ R₂ a ha
      (ih ν innerAdm innerBelow innerRoom) innerAdm innerBelow νδ

end GeneratorLiftData

/-- Concrete finite syntactic lift data for the displayed premise list.
The guard sets may differ between premises; every bound is below the cut in
which its base row must actually be proved. -/
def FiniteLiftData {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat) (a : Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (R₁ R₂ : Label → Label → Prop) (δ : Label) (Γ : List (Formula Nat)) : Prop :=
  ∀ θ ∈ Γ, ∃ (σ : Formula Nat) (n : Nat) (B : Finset Label),
    θ = Formula.«prefix» a n σ ∧ GeneratorLiftData C A E a H labels R₁ R₂ B σ ∧
    (θ.record (mainHeads A E H labels)).RecordedAdmissible A E ∧
    (∀ μ ∈ (θ.record (mainHeads A E H labels)).labelSupport, μ < δ) ∧
    ∀ μ ∈ B, μ < sourceBaseCut a σ labels n δ

namespace FiniteLiftData

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} {A E : Finset Nat} {a : Nat}
    {H : Finset (Nat × Shape Nat)} {labels : Nat → Shape Nat → Label}
    {R₁ R₂ : Label → Label → Prop} {δ : Label} {Γ : List (Formula Nat)}

theorem source_admitted (data : FiniteLiftData C A E a H labels R₁ R₂ δ Γ)
    (θ : Formula Nat) (hθ : θ ∈ Γ) :
    PrefixedAxioms a (CommonCoreGenerator R C.arithmetic C.family a) θ := by
  obtain ⟨σ, n, B, he, hd, _, _, _⟩ := data θ hθ
  exact ⟨σ, n, hd.generator, he⟩

theorem premise_cuts (data : FiniteLiftData C A E a H labels R₁ R₂ δ Γ)
    (ha : a ∈ A) (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    (θ : Formula Nat) (hθ : θ ∈ Γ) :
    RecordedStage.cuts C A E R₁ R₂ a δ (θ.record (mainHeads A E H labels)) := by
  obtain ⟨σ, n, B, rfl, hd, hadm, below, room⟩ := data θ hθ
  exact hd.prefix_cuts ha hereditary disjoint n δ hadm below room

end FiniteLiftData

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

/-- This transforms the actual finite implication-chain certificate. Only its
finite premise list needs lift data; no global generator-transport contract
or source-body truth hypothesis is introduced. -/
theorem certificate_cuts (a : Nat) (δ : Label)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (ha : a ∈ A) (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    {φ : Formula Nat} (closed : φ.Closed)
    (c : Certificate (PrefixedAxioms a (CommonCoreGenerator R C.arithmetic C.family a)) φ)
    (data : FiniteLiftData C A E a H labels R₁ R₂ δ c.premises) :
    cuts C A E R₁ R₂ a δ (φ.record (mainHeads A E H labels)) := by
  refine ⟨(Formula.closed_record _ _).mpr closed, ?_⟩
  apply Provable.chain_elim (c.premises.map (Formula.record (mainHeads A E H labels)))
    (φ.record (mainHeads A E H labels))
  · intro θ hθ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hθ
    exact (data.premise_cuts ha hereditary disjoint η hη).2
  · apply Provable.of_valid
    simpa only [Formula.record_chain] using c.validity.record (mainHeads A E H labels)

/-- The forward half of retained active recovery is unconditional: actual
recorded cuts erase to the original source theory. This uses the full cut,
including its real guarded admissions, rather than an erasure-defined cut. -/
theorem active_query_source (P : RawPredicates Nat) (a : Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (ha : a ∈ A) (disjoint : Disjoint A E)
    (θ : Formula Nat)
    (accepted : reconstructedPredicates (mainHeads A E H labels)
      (predicates C A E R₁ R₂ P) a θ) :
    C.family.effective.proves a θ := by
  have own := mainHeads_active A E H labels a θ.shape ha disjoint
  have hcut : cuts C A E R₁ R₂ a (labels a θ.shape)
      (θ.record (mainHeads A E H labels)) := by
    simpa only [reconstructedPredicates, own, predicates, sourceQueries] using accepted
  have erased := cuts_erasure C A E R₁ R₂ a _ hcut
  simpa only [Formula.erase_record _ _ (mainHeads_erase A E H labels)] using erased

/-- The reverse half is constructed for this literal finite certificate and
its displayed syntactic finite room. The target label is fixed by its original
source argument shape, including every numerical instance. -/
theorem active_query_of_certificate (P : RawPredicates Nat) (a : Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (ha : a ∈ A) (hereditary : HereditaryQueries H)
    (disjoint : Disjoint A E) (φ : Formula Nat) (s : Assignment)
    (c : Certificate (PrefixedAxioms a (CommonCoreGenerator R C.arithmetic C.family a))
      (φ.close s))
    (data : FiniteLiftData C A E a H labels R₁ R₂ (labels a φ.shape) c.premises) :
    reconstructedPredicates (mainHeads A E H labels)
      (predicates C A E R₁ R₂ P) a (φ.close s) := by
  have hcut := certificate_cuts C A E R₁ R₂ a (labels a φ.shape) H labels ha hereditary
    disjoint (φ.close_closed s) c data
  have own := mainHeads_active A E H labels a φ.shape ha disjoint
  simpa only [reconstructedPredicates, Formula.shape_close, own, predicates, sourceQueries]
    using hcut

end RecordedStage
end Alexander313
