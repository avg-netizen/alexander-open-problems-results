import Alexander313.RecordedShapeLabels
import Alexander313.CoherentMinima
import Alexander313.RecordedGeneratorLifts

/-!
# Equivalence of coherent lifts inside one actual cut

Two shape-tabled lifts of the same source formula, with the same live/ghost
mask, prove the same numerical instances in every actual cut whose bound lies
above both, provided all their labels lie in one ≤₁-coherent set. This is the
"coherent-chain equivalence" of note 24 §§4–5.

The proof first lowers each lift to the pointwise minimum. A paired-label
formula records the old and new label at every indexed occurrence. Lowering
proceeds by formula recursion inside an arbitrary one-hole context: children
are lowered before their parent, and the parent label is then moved by one
actual contextual-collapse row. Every intermediate formula is admissible
because its labels are dominated by the original ones. No cut soundness,
reflection or source soundness is used. Uncompiled candidates.
-/

namespace Alexander313

namespace Formula

theorem relabel_comp {Owner L₁ L₂ L₃ : Type} (φ : Formula (RecordedHead Owner L₁))
    (f : L₁ → L₂) (g : L₂ → L₃) :
    (φ.relabel f).relabel g = φ.relabel (fun x => g (f x)) := by
  induction φ with
  | know a φ ih =>
    change Formula.know ((a.mapLabel f).mapLabel g) ((φ.relabel f).relabel g) =
      Formula.know (a.mapLabel (fun x => g (f x))) (φ.relabel (fun x => g (f x)))
    rw [ih]
    cases a <;> rfl
  | _ => simp_all [relabel, mapOwner]

theorem record_mainHeads_relabel {L₁ L₂ : Type} (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → L₁) (f : L₁ → L₂)
    (φ : Formula Nat) :
    (φ.record (mainHeads A E H labels)).relabel f =
      φ.record (mainHeads A E H (fun b sh => f (labels b sh))) := by
  rw [relabel_record]
  congr 1
  funext b sh
  exact mainHeads_relabel A E H labels f b sh

end Formula

namespace Formula.Context

variable {Owner : Type}

def compose : Context Owner → Context Owner → Context Owner
  | .hole, d => d
  | .impLeft c ψ, d => .impLeft (c.compose d) ψ
  | .impRight ψ c, d => .impRight ψ (c.compose d)
  | .conjLeft c ψ, d => .conjLeft (c.compose d) ψ
  | .conjRight ψ c, d => .conjRight ψ (c.compose d)
  | .disjLeft c ψ, d => .disjLeft (c.compose d) ψ
  | .disjRight ψ c, d => .disjRight ψ (c.compose d)
  | .neg c, d => .neg (c.compose d)
  | .all x c, d => .all x (c.compose d)
  | .ex x c, d => .ex x (c.compose d)
  | .know a c, d => .know a (c.compose d)

@[simp] theorem fill_compose (c d : Context Owner) (φ : Formula Owner) :
    (c.compose d).fill φ = c.fill (d.fill φ) := by
  induction c <;> simp_all [compose, fill]

variable {Label : Type} [LinearOrder Label]

theorem recordedAdmissible_of_fill (A E : Finset Nat)
    (c : Context (RecordedHead Nat Label)) (φ : Formula (RecordedHead Nat Label))
    (h : (c.fill φ).RecordedAdmissible A E) : φ.RecordedAdmissible A E := by
  induction c with
  | hole => exact h
  | impLeft c ψ ih => exact ih ((recordedAdmissible_imp_iff A E _ _).mp h).1
  | impRight ψ c ih => exact ih ((recordedAdmissible_imp_iff A E _ _).mp h).2
  | conjLeft c ψ ih => exact ih ((recordedAdmissible_conj_iff A E _ _).mp h).1
  | conjRight ψ c ih => exact ih ((recordedAdmissible_conj_iff A E _ _).mp h).2
  | disjLeft c ψ ih => exact ih ((recordedAdmissible_disj_iff A E _ _).mp h).1
  | disjRight ψ c ih => exact ih ((recordedAdmissible_disj_iff A E _ _).mp h).2
  | neg c ih => exact ih h
  | all x c ih => exact ih h
  | ex x c ih => exact ih h
  | know a c ih =>
    apply ih
    simp only [fill, RecordedAdmissible] at h ⊢
    cases a <;> simp only [HeadsAllowed, GloballyStratified] at h <;> tauto

/-- Labels of a filled context are dominated as soon as the filler's are. -/
theorem fill_support_dominated (c : Context (RecordedHead Nat Label))
    (X Y : Formula (RecordedHead Nat Label))
    (dom : ∀ μ ∈ Y.labelSupport, ∃ ν ∈ X.labelSupport, μ ≤ ν) :
    ∀ μ ∈ (c.fill Y).labelSupport, ∃ ν ∈ (c.fill X).labelSupport, μ ≤ ν := by
  induction c with
  | hole => exact dom
  | impLeft c ψ ih =>
    intro μ hμ
    rcases Finset.mem_union.mp hμ with h | h
    · obtain ⟨ν, hν, hle⟩ := ih μ h
      exact ⟨ν, Finset.mem_union_left _ hν, hle⟩
    · exact ⟨μ, Finset.mem_union_right _ h, le_refl μ⟩
  | impRight ψ c ih =>
    intro μ hμ
    rcases Finset.mem_union.mp hμ with h | h
    · exact ⟨μ, Finset.mem_union_left _ h, le_refl μ⟩
    · obtain ⟨ν, hν, hle⟩ := ih μ h
      exact ⟨ν, Finset.mem_union_right _ hν, hle⟩
  | conjLeft c ψ ih =>
    intro μ hμ
    rcases Finset.mem_union.mp hμ with h | h
    · obtain ⟨ν, hν, hle⟩ := ih μ h
      exact ⟨ν, Finset.mem_union_left _ hν, hle⟩
    · exact ⟨μ, Finset.mem_union_right _ h, le_refl μ⟩
  | conjRight ψ c ih =>
    intro μ hμ
    rcases Finset.mem_union.mp hμ with h | h
    · exact ⟨μ, Finset.mem_union_left _ h, le_refl μ⟩
    · obtain ⟨ν, hν, hle⟩ := ih μ h
      exact ⟨ν, Finset.mem_union_right _ hν, hle⟩
  | disjLeft c ψ ih =>
    intro μ hμ
    rcases Finset.mem_union.mp hμ with h | h
    · obtain ⟨ν, hν, hle⟩ := ih μ h
      exact ⟨ν, Finset.mem_union_left _ hν, hle⟩
    · exact ⟨μ, Finset.mem_union_right _ h, le_refl μ⟩
  | disjRight ψ c ih =>
    intro μ hμ
    rcases Finset.mem_union.mp hμ with h | h
    · exact ⟨μ, Finset.mem_union_left _ h, le_refl μ⟩
    · obtain ⟨ν, hν, hle⟩ := ih μ h
      exact ⟨ν, Finset.mem_union_right _ hν, hle⟩
  | neg c ih => exact ih
  | all x c ih => exact ih
  | ex x c ih => exact ih
  | know a c ih =>
    cases a with
    | live a => exact ih
    | ghost a => exact ih
    | indexed a ν =>
      intro μ hμ
      rcases Finset.mem_insert.mp hμ with rfl | h
      · exact ⟨μ, Finset.mem_insert_self _ _, le_refl μ⟩
      · obtain ⟨ξ, hξ, hle⟩ := ih μ h
        exact ⟨ξ, Finset.mem_insert_of_mem hξ, hle⟩

/-- Replacing the filler by an admissible formula with dominated labels keeps
the whole filled context admissible: ancestors still lie strictly above. -/
theorem fill_recordedAdmissible_dominated (A E : Finset Nat)
    (c : Context (RecordedHead Nat Label)) (X Y : Formula (RecordedHead Nat Label))
    (hX : (c.fill X).RecordedAdmissible A E) (hY : Y.RecordedAdmissible A E)
    (dom : ∀ μ ∈ Y.labelSupport, ∃ ν ∈ X.labelSupport, μ ≤ ν) :
    (c.fill Y).RecordedAdmissible A E := by
  induction c with
  | hole => exact hY
  | impLeft c ψ ih =>
    have h := (recordedAdmissible_imp_iff A E _ _).mp hX
    exact (recordedAdmissible_imp_iff A E _ _).mpr ⟨ih h.1, h.2⟩
  | impRight ψ c ih =>
    have h := (recordedAdmissible_imp_iff A E _ _).mp hX
    exact (recordedAdmissible_imp_iff A E _ _).mpr ⟨h.1, ih h.2⟩
  | conjLeft c ψ ih =>
    have h := (recordedAdmissible_conj_iff A E _ _).mp hX
    exact (recordedAdmissible_conj_iff A E _ _).mpr ⟨ih h.1, h.2⟩
  | conjRight ψ c ih =>
    have h := (recordedAdmissible_conj_iff A E _ _).mp hX
    exact (recordedAdmissible_conj_iff A E _ _).mpr ⟨h.1, ih h.2⟩
  | disjLeft c ψ ih =>
    have h := (recordedAdmissible_disj_iff A E _ _).mp hX
    exact (recordedAdmissible_disj_iff A E _ _).mpr ⟨ih h.1, h.2⟩
  | disjRight ψ c ih =>
    have h := (recordedAdmissible_disj_iff A E _ _).mp hX
    exact (recordedAdmissible_disj_iff A E _ _).mpr ⟨h.1, ih h.2⟩
  | neg c ih => exact ih hX
  | all x c ih => exact ih hX
  | ex x c ih => exact ih hX
  | know a c ih =>
    have inner : (c.fill X).RecordedAdmissible A E := by
      simp only [fill, RecordedAdmissible] at hX ⊢
      cases a <;> simp only [HeadsAllowed, GloballyStratified] at hX <;> tauto
    have innerResult := ih inner
    cases a with
    | live b =>
      simp only [fill, RecordedAdmissible, HeadsAllowed, GloballyStratified] at hX innerResult ⊢
      exact ⟨⟨hX.1.1, innerResult.1⟩, innerResult.2⟩
    | ghost b =>
      simp only [fill, RecordedAdmissible, HeadsAllowed, GloballyStratified] at hX innerResult ⊢
      exact ⟨⟨hX.1.1, innerResult.1⟩, innerResult.2⟩
    | indexed b ν =>
      simp only [fill, RecordedAdmissible, HeadsAllowed, GloballyStratified] at hX innerResult ⊢
      refine ⟨⟨hX.1.1, innerResult.1⟩, innerResult.2, ?_⟩
      intro μ hμ
      obtain ⟨ξ, hξ, hle⟩ := fill_support_dominated c X Y dom μ hμ
      exact lt_of_le_of_lt hle (hX.2.2 ξ hξ)

end Formula.Context

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

/-- Lowering a paired lift inside an arbitrary context. -/
theorem cuts_fill_paired (a : Nat) (δ : Label)
    (ψ : Formula (RecordedHead Nat (Label × Label)))
    (lower : ∀ p ∈ ψ.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1)
    (sndAdm : (ψ.relabel Prod.snd).RecordedAdmissible A E) :
    ∀ (c : Formula.Context (RecordedHead Nat Label)),
      (c.fill (ψ.relabel Prod.fst)).RecordedAdmissible A E →
      (∀ ξ ∈ (c.fill (ψ.relabel Prod.fst)).labelSupport, ξ < δ) →
      ∀ s, cuts C A E R₁ R₂ a δ ((c.fill (ψ.relabel Prod.fst)).close s) ↔
        cuts C A E R₁ R₂ a δ ((c.fill (ψ.relabel Prod.snd)).close s) := by
  -- domination of the lowered labels by the original ones
  have dominated : ∀ ψ : Formula (RecordedHead Nat (Label × Label)),
      (∀ p ∈ ψ.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1) →
      ∀ μ ∈ (ψ.relabel Prod.snd).labelSupport,
        ∃ ν ∈ (ψ.relabel Prod.fst).labelSupport, μ ≤ ν := by
    intro ψ low μ hμ
    rw [Formula.labelSupport_relabel] at hμ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hμ
    refine ⟨p.1, ?_, (low p hp).1⟩
    rw [Formula.labelSupport_relabel]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  revert lower sndAdm
  induction ψ with
  | falsum => intro _ _ c _ _ s; rfl
  | equal t u => intro _ _ c _ _ s; rfl
  | imp ψ₁ ψ₂ ih₁ ih₂ =>
    intro lower sndAdm c adm below s
    have low₁ : ∀ p ∈ ψ₁.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1 :=
      fun p hp => lower p (Finset.mem_union_left _ hp)
    have low₂ : ∀ p ∈ ψ₂.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1 :=
      fun p hp => lower p (Finset.mem_union_right _ hp)
    have snd := (Formula.recordedAdmissible_imp_iff A E _ _).mp sndAdm
    have whole := Formula.Context.recordedAdmissible_of_fill A E c _ adm
    have fst := (Formula.recordedAdmissible_imp_iff A E _ _).mp whole
    let X₂ := ψ₂.relabel Prod.fst
    let Y₁ := ψ₁.relabel Prod.snd
    have step₁ := ih₁ low₁ snd.1 (c.compose (.impLeft .hole X₂))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using adm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using below) s
    have midDom : ∀ μ ∈ (Formula.imp Y₁ X₂).labelSupport,
        ∃ ν ∈ (Formula.imp (ψ₁.relabel Prod.fst) X₂).labelSupport, μ ≤ ν := by
      intro μ hμ
      rcases Finset.mem_union.mp hμ with h | h
      · obtain ⟨ν, hν, hle⟩ := dominated ψ₁ low₁ μ h
        exact ⟨ν, Finset.mem_union_left _ hν, hle⟩
      · exact ⟨μ, Finset.mem_union_right _ h, le_refl μ⟩
    have midAdm : (c.fill (Formula.imp Y₁ X₂)).RecordedAdmissible A E :=
      Formula.Context.fill_recordedAdmissible_dominated A E c _ _ adm
        ((Formula.recordedAdmissible_imp_iff A E _ _).mpr ⟨snd.1, fst.2⟩) midDom
    have midBelow : ∀ ξ ∈ (c.fill (Formula.imp Y₁ X₂)).labelSupport, ξ < δ := by
      intro ξ hξ
      obtain ⟨ν, hν, hle⟩ := Formula.Context.fill_support_dominated c _ _ midDom ξ hξ
      exact lt_of_le_of_lt hle (below ν hν)
    have step₂ := ih₂ low₂ snd.2 (c.compose (.impRight Y₁ .hole))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using midAdm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using midBelow) s
    simp only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] at step₁ step₂
    exact step₁.trans step₂
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro lower sndAdm c adm below s
    have low₁ : ∀ p ∈ ψ₁.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1 :=
      fun p hp => lower p (Finset.mem_union_left _ hp)
    have low₂ : ∀ p ∈ ψ₂.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1 :=
      fun p hp => lower p (Finset.mem_union_right _ hp)
    have snd := (Formula.recordedAdmissible_conj_iff A E _ _).mp sndAdm
    have whole := Formula.Context.recordedAdmissible_of_fill A E c _ adm
    have fst := (Formula.recordedAdmissible_conj_iff A E _ _).mp whole
    let X₂ := ψ₂.relabel Prod.fst
    let Y₁ := ψ₁.relabel Prod.snd
    have step₁ := ih₁ low₁ snd.1 (c.compose (.conjLeft .hole X₂))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using adm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using below) s
    have midDom : ∀ μ ∈ (Formula.conj Y₁ X₂).labelSupport,
        ∃ ν ∈ (Formula.conj (ψ₁.relabel Prod.fst) X₂).labelSupport, μ ≤ ν := by
      intro μ hμ
      rcases Finset.mem_union.mp hμ with h | h
      · obtain ⟨ν, hν, hle⟩ := dominated ψ₁ low₁ μ h
        exact ⟨ν, Finset.mem_union_left _ hν, hle⟩
      · exact ⟨μ, Finset.mem_union_right _ h, le_refl μ⟩
    have midAdm : (c.fill (Formula.conj Y₁ X₂)).RecordedAdmissible A E :=
      Formula.Context.fill_recordedAdmissible_dominated A E c _ _ adm
        ((Formula.recordedAdmissible_conj_iff A E _ _).mpr ⟨snd.1, fst.2⟩) midDom
    have midBelow : ∀ ξ ∈ (c.fill (Formula.conj Y₁ X₂)).labelSupport, ξ < δ := by
      intro ξ hξ
      obtain ⟨ν, hν, hle⟩ := Formula.Context.fill_support_dominated c _ _ midDom ξ hξ
      exact lt_of_le_of_lt hle (below ν hν)
    have step₂ := ih₂ low₂ snd.2 (c.compose (.conjRight Y₁ .hole))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using midAdm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using midBelow) s
    simp only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] at step₁ step₂
    exact step₁.trans step₂
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro lower sndAdm c adm below s
    have low₁ : ∀ p ∈ ψ₁.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1 :=
      fun p hp => lower p (Finset.mem_union_left _ hp)
    have low₂ : ∀ p ∈ ψ₂.labelSupport, p.2 ≤ p.1 ∧ R₁ p.2 p.1 :=
      fun p hp => lower p (Finset.mem_union_right _ hp)
    have snd := (Formula.recordedAdmissible_disj_iff A E _ _).mp sndAdm
    have whole := Formula.Context.recordedAdmissible_of_fill A E c _ adm
    have fst := (Formula.recordedAdmissible_disj_iff A E _ _).mp whole
    let X₂ := ψ₂.relabel Prod.fst
    let Y₁ := ψ₁.relabel Prod.snd
    have step₁ := ih₁ low₁ snd.1 (c.compose (.disjLeft .hole X₂))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using adm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using below) s
    have midDom : ∀ μ ∈ (Formula.disj Y₁ X₂).labelSupport,
        ∃ ν ∈ (Formula.disj (ψ₁.relabel Prod.fst) X₂).labelSupport, μ ≤ ν := by
      intro μ hμ
      rcases Finset.mem_union.mp hμ with h | h
      · obtain ⟨ν, hν, hle⟩ := dominated ψ₁ low₁ μ h
        exact ⟨ν, Finset.mem_union_left _ hν, hle⟩
      · exact ⟨μ, Finset.mem_union_right _ h, le_refl μ⟩
    have midAdm : (c.fill (Formula.disj Y₁ X₂)).RecordedAdmissible A E :=
      Formula.Context.fill_recordedAdmissible_dominated A E c _ _ adm
        ((Formula.recordedAdmissible_disj_iff A E _ _).mpr ⟨snd.1, fst.2⟩) midDom
    have midBelow : ∀ ξ ∈ (c.fill (Formula.disj Y₁ X₂)).labelSupport, ξ < δ := by
      intro ξ hξ
      obtain ⟨ν, hν, hle⟩ := Formula.Context.fill_support_dominated c _ _ midDom ξ hξ
      exact lt_of_le_of_lt hle (below ν hν)
    have step₂ := ih₂ low₂ snd.2 (c.compose (.disjRight Y₁ .hole))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using midAdm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] using midBelow) s
    simp only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel, X₂, Y₁] at step₁ step₂
    exact step₁.trans step₂
  | neg ψ ih =>
    intro lower sndAdm c adm below s
    have step := ih lower sndAdm (c.compose (.neg .hole))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using adm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using below) s
    simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using step
  | all x ψ ih =>
    intro lower sndAdm c adm below s
    have step := ih lower sndAdm (c.compose (.all x .hole))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using adm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using below) s
    simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using step
  | ex x ψ ih =>
    intro lower sndAdm c adm below s
    have step := ih lower sndAdm (c.compose (.ex x .hole))
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using adm)
      (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using below) s
    simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using step
  | know h ψ ih =>
    intro lower sndAdm c adm below s
    cases h with
    | live e =>
      have sndInner := Formula.Context.recordedAdmissible_of_fill A E
        (.know (.live e) .hole) (ψ.relabel Prod.snd) sndAdm
      have step := ih lower sndInner (c.compose (.know (.live e) .hole))
        (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using adm)
        (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using below) s
      simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using step
    | ghost e =>
      have sndInner := Formula.Context.recordedAdmissible_of_fill A E
        (.know (.ghost e) .hole) (ψ.relabel Prod.snd) sndAdm
      have step := ih lower sndInner (c.compose (.know (.ghost e) .hole))
        (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using adm)
        (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using below) s
      simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using step
    | indexed b p =>
      -- the original label is p.1, the lowered label p.2
      have hp := lower p (Finset.mem_insert_self _ _)
      have low' : ∀ q ∈ ψ.labelSupport, q.2 ≤ q.1 ∧ R₁ q.2 q.1 :=
        fun q hq => lower q (Finset.mem_insert_of_mem hq)
      change (c.fill (.know (.indexed b p.1) (ψ.relabel Prod.fst))).RecordedAdmissible A E at adm
      change ∀ ξ ∈ (c.fill (.know (.indexed b p.1) (ψ.relabel Prod.fst))).labelSupport,
        ξ < δ at below
      change (Formula.know (.indexed b p.2) (ψ.relabel Prod.snd)).RecordedAdmissible A E
        at sndAdm
      change cuts C A E R₁ R₂ a δ
          ((c.fill (.know (.indexed b p.1) (ψ.relabel Prod.fst))).close s) ↔
        cuts C A E R₁ R₂ a δ ((c.fill (.know (.indexed b p.2) (ψ.relabel Prod.snd))).close s)
      have sndParts := (Formula.recordedAdmissible_know_indexed A E b p.2 _).mp sndAdm
      have whole := Formula.Context.recordedAdmissible_of_fill A E c _ adm
      have fstParts := (Formula.recordedAdmissible_know_indexed A E b p.1 _).mp whole
      have dom' := dominated ψ low'
      -- lower the argument under the old label
      have step₁ := ih low' sndParts.2.1 (c.compose (.know (.indexed b p.1) .hole))
        (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using adm)
        (by simpa only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] using below) s
      simp only [Formula.Context.fill_compose, Formula.Context.fill, Formula.relabel,
        Formula.mapOwner, RecordedHead.mapLabel] at step₁
      -- the two remaining fillings, both dominated by the original one
      have midInner : (Formula.know (.indexed b p.1) (ψ.relabel Prod.snd)).RecordedAdmissible
          A E := by
        refine (Formula.recordedAdmissible_know_indexed A E b p.1 _).mpr
          ⟨fstParts.1, sndParts.2.1, ?_⟩
        intro μ hμ
        obtain ⟨ν, hν, hle⟩ := dom' μ hμ
        exact lt_of_le_of_lt hle (fstParts.2.2 ν hν)
      have midDom : ∀ μ ∈ (Formula.know (.indexed b p.1) (ψ.relabel Prod.snd)).labelSupport,
          ∃ ν ∈ (Formula.know (.indexed b p.1) (ψ.relabel Prod.fst)).labelSupport,
            μ ≤ ν := by
        intro μ hμ
        rcases Finset.mem_insert.mp hμ with rfl | h
        · exact ⟨p.1, Finset.mem_insert_self _ _, le_refl p.1⟩
        · obtain ⟨ν, hν, hle⟩ := dom' μ h
          exact ⟨ν, Finset.mem_insert_of_mem hν, hle⟩
      have lastDom : ∀ μ ∈ (Formula.know (.indexed b p.2) (ψ.relabel Prod.snd)).labelSupport,
          ∃ ν ∈ (Formula.know (.indexed b p.1) (ψ.relabel Prod.fst)).labelSupport,
            μ ≤ ν := by
        intro μ hμ
        rcases Finset.mem_insert.mp hμ with rfl | h
        · exact ⟨p.1, Finset.mem_insert_self _ _, hp.1⟩
        · obtain ⟨ν, hν, hle⟩ := dom' μ h
          exact ⟨ν, Finset.mem_insert_of_mem hν, hle⟩
      have midAdm := Formula.Context.fill_recordedAdmissible_dominated A E c _ _ adm
        midInner midDom
      have lastAdm := Formula.Context.fill_recordedAdmissible_dominated A E c _ _ adm
        sndAdm lastDom
      have midBelow : ∀ ξ ∈ (c.fill (.know (.indexed b p.1) (ψ.relabel Prod.snd))).labelSupport,
          ξ < δ := by
        intro ξ hξ
        obtain ⟨ν, hν, hle⟩ := Formula.Context.fill_support_dominated c _ _ midDom ξ hξ
        exact lt_of_le_of_lt hle (below ν hν)
      have lastBelow : ∀ ξ ∈ (c.fill (.know (.indexed b p.2) (ψ.relabel Prod.snd))).labelSupport,
          ξ < δ := by
        intro ξ hξ
        obtain ⟨ν, hν, hle⟩ := Formula.Context.fill_support_dominated c _ _ lastDom ξ hξ
        exact lt_of_le_of_lt hle (below ν hν)
      -- move the head label by one actual contextual-collapse row
      have step₂ := cuts_contextual_query C A E R₁ R₂ a δ c b p.2 p.1 (ψ.relabel Prod.snd)
        hp.2 lastAdm midAdm lastBelow midBelow s
      exact step₁.trans step₂.symm

/-- Two lifts of one source formula with labels in a common coherent set are
interchangeable in every cut above both of them. -/
theorem cuts_record_coherent (a : Nat) (δ : Label) (disjoint : Disjoint A E)
    (H : Finset (Nat × Shape Nat)) (lab₁ lab₂ : Nat → Shape Nat → Label)
    (φ : Formula Nat) (S : Set Label)
    (coh : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → R₁ x y)
    (in₁ : ∀ μ ∈ (φ.record (mainHeads A E H lab₁)).labelSupport, μ ∈ S)
    (in₂ : ∀ μ ∈ (φ.record (mainHeads A E H lab₂)).labelSupport, μ ∈ S)
    (adm₁ : (φ.record (mainHeads A E H lab₁)).RecordedAdmissible A E)
    (adm₂ : (φ.record (mainHeads A E H lab₂)).RecordedAdmissible A E)
    (below₁ : ∀ μ ∈ (φ.record (mainHeads A E H lab₁)).labelSupport, μ < δ)
    (below₂ : ∀ μ ∈ (φ.record (mainHeads A E H lab₂)).labelSupport, μ < δ)
    (s : Assignment) :
    cuts C A E R₁ R₂ a δ ((φ.record (mainHeads A E H lab₁)).close s) ↔
      cuts C A E R₁ R₂ a δ ((φ.record (mainHeads A E H lab₂)).close s) := by
  let pair : Nat → Shape Nat → Label × Label := fun b sh => (lab₁ b sh, lab₂ b sh)
  let ψ := φ.record (mainHeads A E H pair)
  let labmin : Nat → Shape Nat → Label := fun b sh => min (lab₁ b sh) (lab₂ b sh)
  have hfst : ψ.relabel Prod.fst = φ.record (mainHeads A E H lab₁) :=
    Formula.record_mainHeads_relabel A E H pair Prod.fst φ
  have hsnd : ψ.relabel Prod.snd = φ.record (mainHeads A E H lab₂) :=
    Formula.record_mainHeads_relabel A E H pair Prod.snd φ
  have hmin : ψ.relabel (fun p => min p.1 p.2) = φ.record (mainHeads A E H labmin) :=
    Formula.record_mainHeads_relabel A E H pair (fun p => min p.1 p.2) φ
  -- both coordinates of every paired label lie in S
  have inS : ∀ p ∈ ψ.labelSupport, p.1 ∈ S ∧ p.2 ∈ S := by
    intro p hp
    constructor
    · apply in₁
      rw [← hfst, Formula.labelSupport_relabel]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · apply in₂
      rw [← hsnd, Formula.labelSupport_relabel]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have minAdm : (φ.record (mainHeads A E H labmin)).RecordedAdmissible A E := by
    refine ⟨Formula.record_headsAllowed A E H labmin disjoint φ, ?_⟩
    rw [← hmin]
    apply Formula.globallyStratified_minimum ψ
    · rw [hfst]; exact adm₁.2
    · rw [hsnd]; exact adm₂.2
  -- lowering from one side to the minimum
  have side (f : Label × Label → Label) (hf : ∀ p, min p.1 p.2 ≤ f p)
      (hfS : ∀ p ∈ ψ.labelSupport, f p ∈ S)
      (adm : (ψ.relabel f).RecordedAdmissible A E)
      (below : ∀ μ ∈ (ψ.relabel f).labelSupport, μ < δ) :
      cuts C A E R₁ R₂ a δ ((ψ.relabel f).close s) ↔
        cuts C A E R₁ R₂ a δ ((φ.record (mainHeads A E H labmin)).close s) := by
    let ψf := ψ.relabel (fun p => (f p, min p.1 p.2))
    have hψfst : ψf.relabel Prod.fst = ψ.relabel f := by
      simp only [ψf, Formula.relabel_comp]
    have hψsnd : ψf.relabel Prod.snd = φ.record (mainHeads A E H labmin) := by
      simp only [ψf, Formula.relabel_comp]
      exact hmin
    have lower : ∀ q ∈ ψf.labelSupport, q.2 ≤ q.1 ∧ R₁ q.2 q.1 := by
      intro q hq
      simp only [ψf, Formula.labelSupport_relabel] at hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hpS := inS p hp
      have hminS : min p.1 p.2 ∈ S := by
        rcases le_total p.1 p.2 with h | h
        · rw [min_eq_left h]; exact hpS.1
        · rw [min_eq_right h]; exact hpS.2
      exact ⟨hf p, coh _ hminS _ (hfS p hp) (hf p)⟩
    have h := cuts_fill_paired C A E R₁ R₂ a δ ψf lower (by rw [hψsnd]; exact minAdm)
      .hole (by simpa only [Formula.Context.fill, hψfst] using adm)
      (by simpa only [Formula.Context.fill, hψfst] using below) s
    simpa only [Formula.Context.fill, hψfst, hψsnd] using h
  have left := side Prod.fst (fun p => min_le_left _ _)
    (fun p hp => (inS p hp).1) (by rw [hfst]; exact adm₁) (by rw [hfst]; exact below₁)
  have right := side Prod.snd (fun p => min_le_right _ _)
    (fun p hp => (inS p hp).2) (by rw [hsnd]; exact adm₂) (by rw [hsnd]; exact below₂)
  rw [hfst] at left
  rw [hsnd] at right
  exact left.trans right.symm

end RecordedStage

end Alexander313
