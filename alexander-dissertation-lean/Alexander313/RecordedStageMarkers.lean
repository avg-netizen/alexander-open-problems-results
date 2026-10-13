import Alexander313.RecordedStageBackground

/-!
# Holder-local marker proofs and same-cut main discharge

Every literal marker is true in the actual full-cut interpretation: its tag is
a closed arithmetic validity and therefore belongs to every raw cut. Its own
known validity is an actual background admission. Thus a cut containing the
marker label proves that marker, and a padded main admission in that cut proves
the unpadded recorded row by a finite sequence of modus ponens steps.

These statements do not infer truth of an unpadded main row from its admission.
They remove the marker-discharge part of finite proof transport without assuming
source-body recovery, stage soundness, ordinal room or a new necessitation rule.
-/

namespace Alexander313

@[simp] theorem markerPadding_freeVars {Label : Type} (a : Nat)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label)) :
    (markerPadding a ms φ).freeVars = φ.freeVars := by
  induction ms with
  | nil => rfl
  | cons p ms ih =>
    change (markerTag (RecordedHead Nat Label) p.2).freeVars ∪
      (markerPadding a ms φ).freeVars = φ.freeVars
    rw [markerTag_closed _ p.2, ih, Finset.empty_union]

@[simp] theorem markerPadding_closed_iff {Label : Type} (a : Nat)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label)) :
    (markerPadding a ms φ).Closed ↔ φ.Closed := by
  simp only [Formula.Closed, markerPadding_freeVars]

theorem markerPadding_body_admissible {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (ms : List (Label × Nat))
    (φ : Formula (RecordedHead Nat Label))
    (h : (markerPadding a ms φ).RecordedAdmissible A E) : φ.RecordedAdmissible A E := by
  revert h
  induction ms with
  | nil => intro h; exact h
  | cons p ms ih =>
    intro h
    exact ih ((Formula.recordedAdmissible_imp_iff A E _ _).mp h).2

theorem RecordedMain.holder_active {Label : Type} [DecidableEq Label] [LT Label]
    {R : Nat → Nat → Prop} {C : CommonCorePresentation R} {A E : Finset Nat}
    {a : Nat} {R₁ R₂ : Label → Label → Prop} {φ : Formula (RecordedHead Nat Label)}
    (h : RecordedMain C A E a R₁ R₂ φ) : a ∈ A := by
  obtain ⟨σ, atom, H, labels, ms, hs, _⟩ := h
  exact hs.holder_active

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

theorem markerTag_truth (P : RawPredicates (RecordedHead Nat Label))
    (n : Nat) (s : Assignment) : filteredTruth P (markerTag _ n) s := by
  cases n <;> intro h <;> exact False.elim h

theorem marker_cuts (a : Nat) (ν : Label) (n : Nat) :
    cuts C A E R₁ R₂ a ν (markerTag _ n) :=
  ⟨markerTag_closed _ n, Provable.of_valid (markerTag_valid _ n)⟩

theorem marker_truth (P : RawPredicates Nat) (a : Nat) (ν : Label)
    (n : Nat) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      (.know (.indexed a ν) (markerTag _ n)) s := by
  have hp : cuts C A E R₁ R₂ a ν ((markerTag _ n).close s) := by
    rw [Formula.close_eq_self_of_closed _ (markerTag_closed _ n)]
    exact marker_cuts C A E R₁ R₂ a ν n
  exact ⟨hp, markerTag_truth _ n s⟩

/-- The proof is from the holder's actual own-validity admission. The tag's
empty support imposes no lower-label requirement. -/
theorem marker_provable (a : Nat) (ha : a ∈ A) (ν δ : Label) (hνδ : ν < δ)
    (n : Nat) : Provable (theory C A E R₁ R₂ a δ)
      (.know (.indexed a ν) (markerTag _ n)) := by
  have hadm : (Formula.universalClosure
      (.know (.indexed a ν) (markerTag _ n))).RecordedAdmissible A E := by
    apply (Formula.recordedAdmissible_universalClosure A E _).mpr
    apply (Formula.recordedAdmissible_know_indexed A E a ν _).mpr
    refine ⟨ha, markerTag_admissible A E n, ?_⟩
    intro μ hμ
    rw [markerTag_support] at hμ
    exact False.elim (Finset.notMem_empty μ hμ)
  have hrow : RecordedBackground A E a R₁
      (.know (.indexed a ν) (markerTag _ n)) := by
    have h := RecordedBackground.own_validity (A := A) (E := E) (a := a) (R₁ := R₁)
      ν (markerTag _ n) (markerTag_valid _ n) hadm
    simpa only [Formula.universalClosure_eq_self_of_closed
      (Formula.know (RecordedHead.indexed a ν) (markerTag _ n)) (markerTag_closed _ n)] using h
  apply Provable.of_axiom
  refine ⟨FullRecordedAdmissions.background hrow, ?_⟩
  intro μ hμ
  have he : μ = ν := by
    simpa only [Formula.labelSupport, markerTag_support, Finset.mem_insert,
      Finset.notMem_empty, or_false] using hμ
  simpa only [he] using hνδ

theorem markerPadding_truth_iff (P : RawPredicates Nat) (a : Nat)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label)) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) (markerPadding a ms φ) s ↔
      filteredTruth (predicates C A E R₁ R₂ P) φ s := by
  induction ms with
  | nil => rfl
  | cons p ms ih =>
    change (filteredTruth (predicates C A E R₁ R₂ P)
        (.know (.indexed a p.1) (markerTag _ p.2)) s →
      filteredTruth (predicates C A E R₁ R₂ P) (markerPadding a ms φ) s) ↔ _
    rw [ih]
    exact ⟨fun h => h (marker_truth C A E R₁ R₂ P a p.1 p.2 s), fun h _ => h⟩

theorem markerPadding_provable_iff (a : Nat) (ha : a ∈ A) (δ : Label)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label))
    (below : ∀ p ∈ ms, p.1 < δ) :
    Provable (theory C A E R₁ R₂ a δ) (markerPadding a ms φ) ↔
      Provable (theory C A E R₁ R₂ a δ) φ := by
  constructor
  · intro hp
    apply Provable.chain_elim (markerFormulas a ms) φ _ hp
    intro θ hθ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hθ
    exact marker_provable C A E R₁ R₂ a ha p.1 δ (below p hp) p.2
  · intro hp
    have hv : Valid (.imp φ (markerPadding a ms φ)) := by
      intro D hD M s h
      exact chain_intro M (markerFormulas a ms) φ s (fun _ => h)
    exact (Provable.of_valid hv).modus_ponens hp

theorem markerPadding_cuts_iff (a : Nat) (ha : a ∈ A) (δ : Label)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label))
    (below : ∀ p ∈ ms, p.1 < δ) :
    cuts C A E R₁ R₂ a δ (markerPadding a ms φ) ↔ cuts C A E R₁ R₂ a δ φ :=
  and_congr (markerPadding_closed_iff a ms φ)
    (markerPadding_provable_iff C A E R₁ R₂ a ha δ ms φ below)

theorem main_unpadded_cuts (a : Nat) (δ : Label) (ms : List (Label × Nat))
    (φ : Formula (RecordedHead Nat Label))
    (hmain : RecordedMain C A E a R₁ R₂ (markerPadding a ms φ))
    (below : ∀ μ ∈ (markerPadding a ms φ).labelSupport, μ < δ) :
    cuts C A E R₁ R₂ a δ φ := by
  have markerBelow : ∀ p ∈ ms, p.1 < δ := by
    intro p hp
    apply below p.1
    rw [markerPadding_support]
    exact Finset.mem_union_left _
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))
  exact (markerPadding_cuts_iff C A E R₁ R₂ a hmain.holder_active δ ms φ markerBelow).mp
    (cuts_of_admission C A E R₁ R₂ a δ (.main hmain) below)

/-- The next cut knows the discharged main row, using the proved finite
certificate prefix operation. This is consequence transport, not local truth. -/
theorem main_unpadded_prefix (a : Nat) (ν δ : Label) (ms : List (Label × Nat))
    (φ : Formula (RecordedHead Nat Label))
    (hmain : RecordedMain C A E a R₁ R₂ (markerPadding a ms φ))
    (below : ∀ μ ∈ (markerPadding a ms φ).labelSupport, μ < ν) (hνδ : ν < δ) :
    cuts C A E R₁ R₂ a δ (.know (.indexed a ν) φ) := by
  apply cuts_prefix C A E R₁ R₂ a hmain.holder_active
    (main_unpadded_cuts C A E R₁ R₂ a ν ms φ hmain below)
    (markerPadding_body_admissible A E a ms φ hmain.admissible) _ hνδ
  intro μ hμ
  apply below μ
  rw [markerPadding_support]
  exact Finset.mem_union_right _ hμ

end RecordedStage
end Alexander313
