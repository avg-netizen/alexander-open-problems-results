import Alexander313.RecordedStagePredicates
import Alexander313.RecordedNumericalContexts

/-!
# Contextual truth in the actual full recorded cut interpretation

At the changed indexed atom, the displayed finite reflection input equates its
actual cut proof tests. Through a live context, the two raw source erasures are
literally equal; ghost contexts have empty tests. Through an indexed context,
the numerically closed argument equivalence is itself an actual admissible
contextual-collapse row below that outer holder. Finite consequence projection
and modus ponens therefore equate its raw tests. Quantifiers use all assignments.

This proof uses no cut soundness, source soundness, supplied contextual truth
contract or inference from erased validity. The ordinal order/reflection input
at the changed atom remains explicit.
-/

namespace Alexander313.RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

theorem cuts_contextual_query (a : Nat) (δ : Label)
    (c : Formula.Context (RecordedHead Nat Label)) (b : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (hμν : R₁ μ ν)
    (hleft : (c.fill (.know (.indexed b μ) φ)).RecordedAdmissible A E)
    (hright : (c.fill (.know (.indexed b ν) φ)).RecordedAdmissible A E)
    (belowLeft : ∀ ξ ∈ (c.fill (.know (.indexed b μ) φ)).labelSupport, ξ < δ)
    (belowRight : ∀ ξ ∈ (c.fill (.know (.indexed b ν) φ)).labelSupport, ξ < δ)
    (s : Assignment) :
    cuts C A E R₁ R₂ a δ ((c.fill (.know (.indexed b μ) φ)).close s) ↔
      cuts C A E R₁ R₂ a δ ((c.fill (.know (.indexed b ν) φ)).close s) := by
  let η := c.fill (.know (.indexed b μ) φ)
  let ζ := c.fill (.know (.indexed b ν) φ)
  have hadm : (Formula.iff (η.close s) (ζ.close s)).RecordedAdmissible A E :=
    (Formula.recordedAdmissible_iff_iff A E _ _).mpr
      ⟨(Formula.recordedAdmissible_close A E η s).mpr hleft,
       (Formula.recordedAdmissible_close A E ζ s).mpr hright⟩
  have he := Formula.Context.contextualCollapse_close_fill c b μ ν φ s
  have hcc : RecordedBackground A E a R₁ (Formula.iff (η.close s) (ζ.close s)) := by
    have ha : (Formula.contextualCollapse (c.subst (fun x => some (s x))) b μ ν
        (φ.subst (c.holeSubstitution (fun x => some (s x))))).RecordedAdmissible A E := by
      rw [he]
      exact hadm
    have h := RecordedBackground.contextual (A := A) (E := E) (a := a) (R₁ := R₁)
      (c.subst (fun x => some (s x))) b μ ν
      (φ.subst (c.holeSubstitution (fun x => some (s x)))) hμν ha
    simpa only [he] using h
  have hp : cuts C A E R₁ R₂ a δ (Formula.iff (η.close s) (ζ.close s)) := by
    apply cuts_of_admission C A E R₁ R₂ a δ (.background hcc)
    intro ξ hξ
    simp only [Formula.labelSupport_iff, Formula.labelSupport_close, Finset.mem_union] at hξ
    exact hξ.elim (belowLeft ξ) (belowRight ξ)
  have forward : Provable (theory C A E R₁ R₂ a δ) (.imp (η.close s) (ζ.close s)) := by
    have hv : Valid (.imp (Formula.iff (η.close s) (ζ.close s))
        (.imp (η.close s) (ζ.close s))) := by
      intro D hD M t h
      exact h.1
    exact (Provable.of_valid hv).modus_ponens hp.2
  have reverse : Provable (theory C A E R₁ R₂ a δ) (.imp (ζ.close s) (η.close s)) := by
    have hv : Valid (.imp (Formula.iff (η.close s) (ζ.close s))
        (.imp (ζ.close s) (η.close s))) := by
      intro D hD M t h
      exact h.2
    exact (Provable.of_valid hv).modus_ponens hp.2
  exact ⟨fun h => ⟨ζ.close_closed s, forward.modus_ponens h.2⟩,
    fun h => ⟨η.close_closed s, reverse.modus_ponens h.2⟩⟩

theorem contextual_truth (P : RawPredicates Nat)
    (c : Formula.Context (RecordedHead Nat Label)) (b : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (hR : R₁ μ ν) (hμν : μ ≤ ν)
    (reflection : FiniteLabelCovering R₁ R₂ μ ν)
    (hleft : (c.fill (.know (.indexed b μ) φ)).RecordedAdmissible A E)
    (hright : (c.fill (.know (.indexed b ν) φ)).RecordedAdmissible A E)
    (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) (c.fill (.know (.indexed b μ) φ)) s ↔
      filteredTruth (predicates C A E R₁ R₂ P) (c.fill (.know (.indexed b ν) φ)) s := by
  revert hleft hright s
  induction c with
  | hole =>
    intro hleft hright s
    have below : ∀ ξ ∈ (φ.close s).labelSupport, ξ < μ := by
      simpa only [Formula.labelSupport_close] using hleft.2.2
    change (cuts C A E R₁ R₂ b μ (φ.close s) ∧
      filteredTruth (predicates C A E R₁ R₂ P) φ s) ↔
      (cuts C A E R₁ R₂ b ν (φ.close s) ∧
      filteredTruth (predicates C A E R₁ R₂ P) φ s)
    exact and_congr (cuts_collapse C A E R₁ R₂ b hμν reflection _ below) Iff.rfl
  | impLeft c ψ ih =>
    intro hleft hright s
    have hl := (Formula.recordedAdmissible_imp_iff A E _ _).mp hleft
    have hr := (Formula.recordedAdmissible_imp_iff A E _ _).mp hright
    exact imp_congr (ih hl.1 hr.1 s) Iff.rfl
  | impRight ψ c ih =>
    intro hleft hright s
    have hl := (Formula.recordedAdmissible_imp_iff A E _ _).mp hleft
    have hr := (Formula.recordedAdmissible_imp_iff A E _ _).mp hright
    exact imp_congr Iff.rfl (ih hl.2 hr.2 s)
  | conjLeft c ψ ih =>
    intro hleft hright s
    have hl := (Formula.recordedAdmissible_conj_iff A E _ _).mp hleft
    have hr := (Formula.recordedAdmissible_conj_iff A E _ _).mp hright
    exact and_congr (ih hl.1 hr.1 s) Iff.rfl
  | conjRight ψ c ih =>
    intro hleft hright s
    have hl := (Formula.recordedAdmissible_conj_iff A E _ _).mp hleft
    have hr := (Formula.recordedAdmissible_conj_iff A E _ _).mp hright
    exact and_congr Iff.rfl (ih hl.2 hr.2 s)
  | disjLeft c ψ ih =>
    intro hleft hright s
    have hl := (Formula.recordedAdmissible_disj_iff A E _ _).mp hleft
    have hr := (Formula.recordedAdmissible_disj_iff A E _ _).mp hright
    exact or_congr (ih hl.1 hr.1 s) Iff.rfl
  | disjRight ψ c ih =>
    intro hleft hright s
    have hl := (Formula.recordedAdmissible_disj_iff A E _ _).mp hleft
    have hr := (Formula.recordedAdmissible_disj_iff A E _ _).mp hright
    exact or_congr Iff.rfl (ih hl.2 hr.2 s)
  | neg c ih =>
    intro hleft hright s
    exact not_congr (ih hleft hright s)
  | all x c ih =>
    intro hleft hright s
    exact forall_congr' (fun n => ih hleft hright (Function.update s x n))
  | ex x c ih =>
    intro hleft hright s
    exact exists_congr (fun n => ih hleft hright (Function.update s x n))
  | know h c ih =>
    intro hleft hright s
    cases h with
    | live a =>
      have hl : (c.fill (.know (.indexed b μ) φ)).RecordedAdmissible A E :=
        ⟨hleft.1.2, hleft.2⟩
      have hr : (c.fill (.know (.indexed b ν) φ)).RecordedAdmissible A E :=
        ⟨hright.1.2, hright.2⟩
      change (P a (((c.fill (.know (.indexed b μ) φ)).close s).erase) ∧
        filteredTruth (predicates C A E R₁ R₂ P) (c.fill (.know (.indexed b μ) φ)) s) ↔
        (P a (((c.fill (.know (.indexed b ν) φ)).close s).erase) ∧
        filteredTruth (predicates C A E R₁ R₂ P) (c.fill (.know (.indexed b ν) φ)) s)
      exact and_congr (by rw [Formula.Context.erase_close_fill_indexed c b μ ν φ s])
        (ih hl hr s)
    | indexed a δ =>
      have hl : (c.fill (.know (.indexed b μ) φ)).RecordedAdmissible A E :=
        ⟨hleft.1.2, hleft.2.1⟩
      have hr : (c.fill (.know (.indexed b ν) φ)).RecordedAdmissible A E :=
        ⟨hright.1.2, hright.2.1⟩
      change (cuts C A E R₁ R₂ a δ ((c.fill (.know (.indexed b μ) φ)).close s) ∧
        filteredTruth (predicates C A E R₁ R₂ P) (c.fill (.know (.indexed b μ) φ)) s) ↔
        (cuts C A E R₁ R₂ a δ ((c.fill (.know (.indexed b ν) φ)).close s) ∧
        filteredTruth (predicates C A E R₁ R₂ P) (c.fill (.know (.indexed b ν) φ)) s)
      exact and_congr (cuts_contextual_query C A E R₁ R₂ a δ c b μ ν φ hR
        hl hr hleft.2.2 hright.2.2 s) (ih hl hr s)
    | ghost a =>
      simp [Formula.Context.fill, truth, predicates, sourceQueries]

theorem contextualCollapse_truth (P : RawPredicates Nat)
    (c : Formula.Context (RecordedHead Nat Label)) (b : Nat) (μ ν : Label)
    (φ : Formula (RecordedHead Nat Label)) (hR : R₁ μ ν) (hμν : μ ≤ ν)
    (reflection : FiniteLabelCovering R₁ R₂ μ ν)
    (hadm : (Formula.contextualCollapse c b μ ν φ).RecordedAdmissible A E)
    (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) (Formula.contextualCollapse c b μ ν φ) s := by
  have ha := (Formula.recordedAdmissible_universalClosure A E _).mp hadm
  have pair := (Formula.recordedAdmissible_iff_iff A E _ _).mp ha
  apply truth_universalClosure true _ _ _ s
  intro t
  have h := contextual_truth C A E R₁ R₂ P c b μ ν φ hR hμν reflection pair.1 pair.2 t
  exact ⟨h.mp, h.mpr⟩

end Alexander313.RecordedStage
