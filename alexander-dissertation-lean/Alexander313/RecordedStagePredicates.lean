import Alexander313.FullRecordedPrefixes
import Alexander313.SourceModels
import Alexander313.Alexander.ModelTransport

/-!
# Actual sentence predicates of the full recorded cuts

An indexed predicate is the sentence consequence predicate of the literal
`LabelCut (FullRecordedAdmissions ...)`. The sentence restriction is necessary:
an unrestricted `Provable` conclusion may be a free validity. It disappears on
every actual modal query, which is numerically closed before being tested.

Live heads test the old predicate on the source erasure of the actual argument;
ghost predicates are empty. Alphabetic closure follows from the actual finite
certificate alpha transformation and source-erasure transport. The filtered
Alexander model is constructed from those facts, before any cut or source
soundness. For a source MachineFamily the old alphabetic property is derived.

These are stage-consequence cuts, not source-erasure replacement cuts. Finite
reflection remains an explicit dependency of cut collapse. No retained active
query recovery or common-core/whole-ideal genericity is asserted.
-/

namespace Alexander313.RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}

abbrev theory (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop) (a : Nat) (ν : Label) :
    Formula (RecordedHead Nat Label) → Prop :=
  LabelCut (FullRecordedAdmissions C A E a R₁ R₂) ν

def cuts (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop) (a : Nat) (ν : Label)
    (θ : Formula (RecordedHead Nat Label)) : Prop :=
  θ.Closed ∧ Provable (theory C A E R₁ R₂ a ν) θ

def predicates (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop) (P : RawPredicates Nat) :
    RawPredicates (RecordedHead Nat Label) :=
  sourceQueries P (cuts C A E R₁ R₂)

variable (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

theorem cuts_sentences (a : Nat) (ν : Label) (θ : Formula (RecordedHead Nat Label))
    (h : cuts C A E R₁ R₂ a ν θ) : θ.Closed := h.1

theorem cuts_iff (a : Nat) (ν : Label) (θ : Formula (RecordedHead Nat Label))
    (hc : θ.Closed) : cuts C A E R₁ R₂ a ν θ ↔ Provable (theory C A E R₁ R₂ a ν) θ :=
  ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

@[simp] theorem cuts_query (a : Nat) (ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (s : Assignment) :
    cuts C A E R₁ R₂ a ν (φ.close s) ↔
      Provable (theory C A E R₁ R₂ a ν) (φ.close s) :=
  cuts_iff C A E R₁ R₂ a ν _ (φ.close_closed s)

theorem cuts_alpha (a : Nat) (ν : Label) (φ ψ : Formula (RecordedHead Nat Label))
    (hφ : φ.Closed) (hψ : ψ.Closed) (hα : φ.AlphaEquivalent ψ) :
    cuts C A E R₁ R₂ a ν φ ↔ cuts C A E R₁ R₂ a ν ψ :=
  ⟨fun h => ⟨hψ, h.2.alpha hα⟩, fun h => ⟨hφ, h.2.alpha hα.symm⟩⟩

theorem rawAlphabetic (P : RawPredicates Nat) (hP : RawAlphabetic P) :
    RawAlphabetic (predicates C A E R₁ R₂ P) := by
  intro h φ ψ hφ hψ hα
  cases h with
  | live a =>
    exact hP a φ.erase ψ.erase ((Formula.closed_erase φ).mpr hφ)
      ((Formula.closed_erase ψ).mpr hψ) (hα.mapOwner RecordedHead.erase)
  | indexed a ν => exact cuts_alpha C A E R₁ R₂ a ν φ ψ hφ hψ hα
  | ghost a => rfl

theorem sentences (P : RawPredicates Nat)
    (hP : ∀ a θ, P a θ → θ.Closed) (h : RecordedHead Nat Label)
    (θ : Formula (RecordedHead Nat Label)) (hp : predicates C A E R₁ R₂ P h θ) :
    θ.Closed := by
  cases h with
  | live a => exact (Formula.closed_erase θ).mp (hP a θ.erase hp)
  | indexed a ν => exact hp.1
  | ghost a => exact False.elim hp

def filteredRealization (P : RawPredicates Nat) (hP : RawAlphabetic P) :
    FilteredRealization (predicates C A E R₁ R₂ P) :=
  FilteredRealization.ofAlphabetic _ (rawAlphabetic C A E R₁ R₂ P hP)

def sourceRealization : FilteredRealization
    (predicates C A E R₁ R₂ C.family.effective.proves) :=
  filteredRealization C A E R₁ R₂ _ C.family.rawAlphabetic

theorem source_sentences (h : RecordedHead Nat Label)
    (θ : Formula (RecordedHead Nat Label))
    (hp : predicates C A E R₁ R₂ C.family.effective.proves h θ) : θ.Closed :=
  sentences C A E R₁ R₂ _ C.family.sentences h θ hp

theorem cuts_of_admission (a : Nat) (ν : Label) {θ : Formula (RecordedHead Nat Label)}
    (h : FullRecordedAdmissions C A E a R₁ R₂ θ)
    (below : ∀ μ ∈ θ.labelSupport, μ < ν) : cuts C A E R₁ R₂ a ν θ :=
  ⟨h.closed, Provable.of_axiom ⟨h, below⟩⟩

theorem cuts_mono (a : Nat) {α β : Label} (hαβ : α ≤ β)
    {θ : Formula (RecordedHead Nat Label)} (h : cuts C A E R₁ R₂ a α θ) :
    cuts C A E R₁ R₂ a β θ :=
  ⟨h.1, h.2.mono (labelCut_mono _ hαβ)⟩

theorem cuts_modus_ponens (a : Nat) (ν : Label)
    (φ ψ : Formula (RecordedHead Nat Label))
    (hi : cuts C A E R₁ R₂ a ν (.imp φ ψ)) (hp : cuts C A E R₁ R₂ a ν φ) :
    cuts C A E R₁ R₂ a ν ψ := by
  have hc : φ.Closed ∧ ψ.Closed := by
    simpa only [Formula.Closed, Formula.freeVars, Finset.union_eq_empty] using hi.1
  exact ⟨hc.2, hi.2.modus_ponens hp.2⟩

theorem cuts_assigned_validity (a : Nat) (ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (s : Assignment) (hv : Valid φ)
    (hadm : φ.RecordedAdmissible A E) (below : ∀ μ ∈ φ.labelSupport, μ < ν) :
    cuts C A E R₁ R₂ a ν (φ.close s) := by
  apply cuts_of_admission C A E R₁ R₂ a ν
    (.background (.assigned φ s hv hadm))
  simpa only [Formula.labelSupport_close] using below

theorem cuts_prefix (a : Nat) {ν δ : Label} (ha : a ∈ A)
    {φ : Formula (RecordedHead Nat Label)} (hp : cuts C A E R₁ R₂ a ν φ)
    (hadm : φ.RecordedAdmissible A E) (below : ∀ μ ∈ φ.labelSupport, μ < ν)
    (hνδ : ν < δ) : cuts C A E R₁ R₂ a δ (.know (.indexed a ν) φ) :=
  ⟨hp.1, FullRecordedAdmissions.prefix_of_provable ha hp.2 hp.1 hadm below hνδ⟩

theorem cuts_erasure (a : Nat) (ν : Label) {φ : Formula (RecordedHead Nat Label)}
    (h : cuts C A E R₁ R₂ a ν φ) : C.family.effective.proves a φ.erase :=
  FullRecordedAdmissions.erasure_of_provable h.1
    (h.2.mono (fun _ hθ => hθ.1))

/-- Actual full-table cut equality, conditional only on the displayed finite
reflection input and the target's literal support bound. -/
theorem cuts_collapse (a : Nat) {α β : Label} (hαβ : α ≤ β)
    (reflection : FiniteLabelCovering R₁ R₂ α β)
    (φ : Formula (RecordedHead Nat Label)) (target : ∀ μ ∈ φ.labelSupport, μ < α) :
    cuts C A E R₁ R₂ a α φ ↔ cuts C A E R₁ R₂ a β φ :=
  and_congr Iff.rfl
    (FullRecordedAdmissions.cut_provable_iff C A E a R₁ R₂ hαβ reflection φ target)

end Alexander313.RecordedStage
