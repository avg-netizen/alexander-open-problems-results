import Alexander313.RecordedFiniteLiftPlans
import Alexander313.OrdinalPackage

/-!
# Skeleton facts for shape-tabled recorded lifts

A source-shared head table depends only on the owner and the whole argument
skeleton. The label support and the guards of a recorded lift are therefore
skeleton invariants: every term variant and numerical instance of a retained
argument has the same labels as the literal occurrence that was guarded.

The active nesting depth of a skeleton gives the canonical depth table of
note 24 §5: an active head over an argument of depth d receives the label
`c d`. Strictly increasing labels make every such lift nest correctly and
bound its support by the labels below the formula's own depth.

The final lemmas read off the literal guards of a main atom: below every live
external head, every active query has a guard chain of the external
argument's rank and its argument support is ≤₁-below its label. Uncompiled.
-/

namespace Alexander313

namespace Shape

def activeDepth (A : Finset Nat) : Shape Nat → Nat
  | .falsum => 0
  | .equal => 0
  | .imp φ ψ => max (φ.activeDepth A) (ψ.activeDepth A)
  | .conj φ ψ => max (φ.activeDepth A) (ψ.activeDepth A)
  | .disj φ ψ => max (φ.activeDepth A) (ψ.activeDepth A)
  | .neg φ => φ.activeDepth A
  | .all φ => φ.activeDepth A
  | .ex φ => φ.activeDepth A
  | .know b φ => if b ∈ A then φ.activeDepth A + 1 else φ.activeDepth A

theorem activeDepth_query (A : Finset Nat) (sh₀ : Shape Nat) (b : Nat) (sh : Shape Nat)
    (h : (b, sh) ∈ sh₀.queries) :
    sh.activeDepth A ≤ sh₀.activeDepth A ∧
      (b ∈ A → sh.activeDepth A < sh₀.activeDepth A) := by
  induction sh₀ with
  | falsum => simp [queries] at h
  | equal => simp [queries] at h
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · obtain ⟨h₁, h₂⟩ := ihφ hφ
      refine ⟨le_trans h₁ (le_max_left _ _), fun hb => ?_⟩
      exact lt_of_lt_of_le (h₂ hb) (le_max_left _ _)
    · obtain ⟨h₁, h₂⟩ := ihψ hψ
      refine ⟨le_trans h₁ (le_max_right _ _), fun hb => ?_⟩
      exact lt_of_lt_of_le (h₂ hb) (le_max_right _ _)
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · obtain ⟨h₁, h₂⟩ := ihφ hφ
      refine ⟨le_trans h₁ (le_max_left _ _), fun hb => ?_⟩
      exact lt_of_lt_of_le (h₂ hb) (le_max_left _ _)
    · obtain ⟨h₁, h₂⟩ := ihψ hψ
      refine ⟨le_trans h₁ (le_max_right _ _), fun hb => ?_⟩
      exact lt_of_lt_of_le (h₂ hb) (le_max_right _ _)
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · obtain ⟨h₁, h₂⟩ := ihφ hφ
      refine ⟨le_trans h₁ (le_max_left _ _), fun hb => ?_⟩
      exact lt_of_lt_of_le (h₂ hb) (le_max_left _ _)
    · obtain ⟨h₁, h₂⟩ := ihψ hψ
      refine ⟨le_trans h₁ (le_max_right _ _), fun hb => ?_⟩
      exact lt_of_lt_of_le (h₂ hb) (le_max_right _ _)
  | neg φ ih => exact ih h
  | all φ ih => exact ih h
  | ex φ ih => exact ih h
  | know c φ ih =>
    have step : φ.activeDepth A ≤ (Shape.know c φ).activeDepth A := by
      by_cases hc : c ∈ A <;> simp [activeDepth, hc]
    rcases Finset.mem_insert.mp h with heq | hsub
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      refine ⟨step, fun hb => ?_⟩
      simp [activeDepth, hb]
    · obtain ⟨h₁, h₂⟩ := ih hsub
      exact ⟨le_trans h₁ step, fun hb => lt_of_lt_of_le (h₂ hb) step⟩

theorem rank_query (sh₀ : Shape Nat) (b : Nat) (sh : Shape Nat)
    (h : (b, sh) ∈ sh₀.queries) : sh.rank < sh₀.rank := by
  induction sh₀ with
  | falsum => simp [queries] at h
  | equal => simp [queries] at h
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · have := ihφ hφ; simp only [rank]; omega
    · have := ihψ hψ; simp only [rank]; omega
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · have := ihφ hφ; simp only [rank]; omega
    · have := ihψ hψ; simp only [rank]; omega
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · have := ihφ hφ; simp only [rank]; omega
    · have := ihψ hψ; simp only [rank]; omega
  | neg φ ih => have := ih h; simp only [rank]; omega
  | all φ ih => have := ih h; simp only [rank]; omega
  | ex φ ih => have := ih h; simp only [rank]; omega
  | know c φ ih =>
    rcases Finset.mem_insert.mp h with heq | hsub
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [rank]; omega
    · have := ih hsub; simp only [rank]; omega

end Shape

/-- The canonical depth table of note 24 §5. -/
def depthLabels {Label : Type} (A : Finset Nat) (c : Nat → Label) :
    Nat → Shape Nat → Label :=
  fun _ sh => c (sh.activeDepth A)

namespace Shape

variable {Label : Type} [LinearOrder Label]

theorem labelNesting_depth (A : Finset Nat) (c : Nat → Label) (N : Nat)
    (mono : ∀ d₁ d₂, d₁ < d₂ → d₂ < N → c d₁ < c d₂) :
    ∀ sh : Shape Nat, sh.activeDepth A ≤ N → sh.labelNesting A (depthLabels A c) := by
  intro sh
  induction sh with
  | falsum => intro _; trivial
  | equal => intro _; trivial
  | imp φ ψ ihφ ihψ =>
    intro h
    exact ⟨ihφ (le_trans (le_max_left _ _) h), ihψ (le_trans (le_max_right _ _) h)⟩
  | conj φ ψ ihφ ihψ =>
    intro h
    exact ⟨ihφ (le_trans (le_max_left _ _) h), ihψ (le_trans (le_max_right _ _) h)⟩
  | disj φ ψ ihφ ihψ =>
    intro h
    exact ⟨ihφ (le_trans (le_max_left _ _) h), ihψ (le_trans (le_max_right _ _) h)⟩
  | neg φ ih => intro h; exact ih h
  | all φ ih => intro h; exact ih h
  | ex φ ih => intro h; exact ih h
  | know a φ ih =>
    intro h
    have hφ : φ.activeDepth A ≤ N := by
      by_cases ha : a ∈ A <;> simp only [activeDepth, ha, ↓reduceIte] at h <;> omega
    refine ⟨ih hφ, ?_⟩
    intro ha q hq hqA
    have hdepth : φ.activeDepth A < N := by
      simp only [activeDepth, ha, ↓reduceIte] at h
      omega
    have hlt := (activeDepth_query A φ q.1 q.2 hq).2 hqA
    exact mono _ _ hlt hdepth

theorem labelBounds_depth (A : Finset Nat) (c : Nat → Label) (δ : Label)
    (sh : Shape Nat) (below : ∀ d < sh.activeDepth A, c d < δ) :
    sh.labelBounds A (depthLabels A c) δ := by
  intro q hq hqA
  exact below _ ((activeDepth_query A sh q.1 q.2 hq).2 hqA)

end Shape

namespace Formula

variable {Label : Type} [LinearOrder Label]

/-- Every label of a depth-tabled lift is a depth label below the whole depth. -/
theorem record_depth_support (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (c : Nat → Label) (disjoint : Disjoint A E) (φ : Formula Nat) :
    ∀ μ ∈ (φ.record (mainHeads A E H (depthLabels A c))).labelSupport,
      ∃ d, d < φ.shape.activeDepth A ∧ μ = c d := by
  intro μ hμ
  obtain ⟨b, sh, hq, hb, rfl⟩ :=
    record_support_source_query A E H (depthLabels A c) disjoint φ μ hμ
  refine ⟨sh.activeDepth A, ?_, rfl⟩
  exact (Shape.activeDepth_query A φ.shape b sh (by simpa only [queries_shape] using hq)).2 hb

theorem record_depth_admissible (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (c : Nat → Label) (disjoint : Disjoint A E) (N : Nat)
    (mono : ∀ d₁ d₂, d₁ < d₂ → d₂ < N → c d₁ < c d₂) (φ : Formula Nat)
    (hφ : φ.shape.activeDepth A ≤ N) :
    (φ.record (mainHeads A E H (depthLabels A c))).RecordedAdmissible A E :=
  record_admissible_of_labelNesting A E H _ disjoint φ
    (Shape.labelNesting_depth A c N mono φ.shape hφ)

/-- Shape-tabled lifts of equal skeletons have equal label support. -/
theorem labelSupport_record_shape (head : Nat → Shape Nat → RecordedHead Nat Label) :
    ∀ φ ψ : Formula Nat, φ.shape = ψ.shape →
      (φ.record head).labelSupport = (ψ.record head).labelSupport := by
  intro φ
  induction φ with
  | falsum =>
    intro ψ h
    cases ψ with
    | falsum => rfl
    | _ => simp [shape] at h
  | equal t u =>
    intro ψ h
    cases ψ with
    | equal t' u' => rfl
    | _ => simp [shape] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ with
    | imp ψ₁ ψ₂ =>
      simp only [shape, Shape.imp.injEq] at h
      simp only [record, labelSupport, ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [shape] at h
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ with
    | conj ψ₁ ψ₂ =>
      simp only [shape, Shape.conj.injEq] at h
      simp only [record, labelSupport, ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [shape] at h
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ with
    | disj ψ₁ ψ₂ =>
      simp only [shape, Shape.disj.injEq] at h
      simp only [record, labelSupport, ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [shape] at h
  | neg φ₁ ih =>
    intro ψ h
    cases ψ with
    | neg ψ₁ =>
      simp only [shape, Shape.neg.injEq] at h
      simp only [record, labelSupport, ih ψ₁ h]
    | _ => simp [shape] at h
  | all x φ₁ ih =>
    intro ψ h
    cases ψ with
    | all y ψ₁ =>
      simp only [shape, Shape.all.injEq] at h
      simp only [record, labelSupport, ih ψ₁ h]
    | _ => simp [shape] at h
  | ex x φ₁ ih =>
    intro ψ h
    cases ψ with
    | ex y ψ₁ =>
      simp only [shape, Shape.ex.injEq] at h
      simp only [record, labelSupport, ih ψ₁ h]
    | _ => simp [shape] at h
  | know a φ₁ ih =>
    intro ψ h
    cases ψ with
    | know b ψ₁ =>
      simp only [shape, Shape.know.injEq] at h
      obtain ⟨hab, hs⟩ := h
      subst hab
      have inner := ih ψ₁ hs
      simp only [record, hs]
      cases head a ψ₁.shape <;> simp only [labelSupport, inner]
    | _ => simp [shape] at h

/-- Shape-tabled lifts of equal skeletons are admissible together. -/
theorem recordedAdmissible_record_shape (A E : Finset Nat)
    (head : Nat → Shape Nat → RecordedHead Nat Label) :
    ∀ φ ψ : Formula Nat, φ.shape = ψ.shape →
      ((φ.record head).RecordedAdmissible A E ↔ (ψ.record head).RecordedAdmissible A E) := by
  intro φ
  induction φ with
  | falsum =>
    intro ψ h
    cases ψ with
    | falsum => rfl
    | _ => simp [shape] at h
  | equal t u =>
    intro ψ h
    cases ψ with
    | equal t' u' => exact Iff.rfl
    | _ => simp [shape] at h
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ with
    | imp ψ₁ ψ₂ =>
      simp only [shape, Shape.imp.injEq] at h
      simp only [record, recordedAdmissible_imp_iff, ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [shape] at h
  | conj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ with
    | conj ψ₁ ψ₂ =>
      simp only [shape, Shape.conj.injEq] at h
      simp only [record, recordedAdmissible_conj_iff, ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [shape] at h
  | disj φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ with
    | disj ψ₁ ψ₂ =>
      simp only [shape, Shape.disj.injEq] at h
      simp only [record, recordedAdmissible_disj_iff, ih₁ ψ₁ h.1, ih₂ ψ₂ h.2]
    | _ => simp [shape] at h
  | neg φ₁ ih =>
    intro ψ h
    cases ψ with
    | neg ψ₁ =>
      simp only [shape, Shape.neg.injEq] at h
      have hi := ih ψ₁ h
      simp only [record, RecordedAdmissible, HeadsAllowed, GloballyStratified] at hi ⊢
      exact hi
    | _ => simp [shape] at h
  | all x φ₁ ih =>
    intro ψ h
    cases ψ with
    | all y ψ₁ =>
      simp only [shape, Shape.all.injEq] at h
      have hi := ih ψ₁ h
      simp only [record, RecordedAdmissible, HeadsAllowed, GloballyStratified] at hi ⊢
      exact hi
    | _ => simp [shape] at h
  | ex x φ₁ ih =>
    intro ψ h
    cases ψ with
    | ex y ψ₁ =>
      simp only [shape, Shape.ex.injEq] at h
      have hi := ih ψ₁ h
      simp only [record, RecordedAdmissible, HeadsAllowed, GloballyStratified] at hi ⊢
      exact hi
    | _ => simp [shape] at h
  | know a φ₁ ih =>
    intro ψ h
    cases ψ with
    | know b ψ₁ =>
      simp only [shape, Shape.know.injEq] at h
      obtain ⟨hab, hs⟩ := h
      subst hab
      have hi := ih ψ₁ hs
      have hsupp := labelSupport_record_shape head φ₁ ψ₁ hs
      simp only [record, hs]
      simp only [RecordedAdmissible] at hi ⊢
      cases head a ψ₁.shape <;>
        simp only [HeadsAllowed, GloballyStratified, hsupp] <;> tauto
    | _ => simp [shape] at h

/-- An active query of the source formula leaves its label in the support. -/
theorem query_label_mem (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (disjoint : Disjoint A E) (φ : Formula Nat)
    (b : Nat) (sh : Shape Nat) (hq : (b, sh) ∈ φ.queries) (hb : b ∈ A) :
    labels b sh ∈ (φ.record (mainHeads A E H labels)).labelSupport := by
  induction φ with
  | falsum => simp [queries] at hq
  | equal t u => simp [queries] at hq
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ (ihφ h)
    · exact Finset.mem_union_right _ (ihψ h)
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ (ihφ h)
    · exact Finset.mem_union_right _ (ihψ h)
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ (ihφ h)
    · exact Finset.mem_union_right _ (ihψ h)
  | neg φ ih => exact ih hq
  | all x φ ih => exact ih hq
  | ex x φ ih => exact ih hq
  | know a φ ih =>
    have own := mainHeads_active A E H labels b sh hb disjoint
    have hinner : (φ.record (mainHeads A E H labels)).labelSupport ⊆
        ((Formula.know a φ).record (mainHeads A E H labels)).labelSupport := by
      intro μ hμ
      simp only [record]
      cases mainHeads A E H labels a φ.shape <;>
        simp only [labelSupport, Finset.mem_insert] <;> tauto
    rcases Finset.mem_insert.mp hq with heq | hsub
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [record, own, labelSupport, Finset.mem_insert_self]
    · exact hinner (ih hsub)

/-- Strict nesting at an active query, for every argument of that skeleton. -/
theorem query_support_below (A E : Finset Nat) (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (disjoint : Disjoint A E) (φ : Formula Nat)
    (adm : (φ.record (mainHeads A E H labels)).RecordedAdmissible A E)
    (b : Nat) (sh : Shape Nat) (hq : (b, sh) ∈ φ.queries) (hb : b ∈ A)
    (ψ : Formula Nat) (hψ : ψ.shape = sh) :
    (ψ.record (mainHeads A E H labels)).RecordedAdmissible A E ∧
      ∀ μ ∈ (ψ.record (mainHeads A E H labels)).labelSupport, μ < labels b sh := by
  induction φ with
  | falsum => simp [queries] at hq
  | equal t u => simp [queries] at hq
  | imp φ₁ φ₂ ih₁ ih₂ =>
    have h := (recordedAdmissible_imp_iff A E _ _).mp adm
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ih₁ h.1 hq
    · exact ih₂ h.2 hq
  | conj φ₁ φ₂ ih₁ ih₂ =>
    have h := (recordedAdmissible_conj_iff A E _ _).mp adm
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ih₁ h.1 hq
    · exact ih₂ h.2 hq
  | disj φ₁ φ₂ ih₁ ih₂ =>
    have h := (recordedAdmissible_disj_iff A E _ _).mp adm
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ih₁ h.1 hq
    · exact ih₂ h.2 hq
  | neg φ₁ ih => exact ih adm hq
  | all x φ₁ ih => exact ih adm hq
  | ex x φ₁ ih => exact ih adm hq
  | know a φ₁ ih =>
    have inner : (φ₁.record (mainHeads A E H labels)).RecordedAdmissible A E := by
      simp only [record, RecordedAdmissible] at adm ⊢
      cases hh : mainHeads A E H labels a φ₁.shape <;>
        simp only [hh, HeadsAllowed, GloballyStratified] at adm <;> tauto
    rcases Finset.mem_insert.mp hq with heq | hsub
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have own := mainHeads_active A E H labels b φ₁.shape hb disjoint
      have whole := (recordedAdmissible_know_indexed A E b (labels b φ₁.shape) _).mp
        (by simpa only [record, own] using adm)
      refine ⟨(recordedAdmissible_record_shape A E _ ψ φ₁ hψ).mpr inner, ?_⟩
      rw [labelSupport_record_shape _ ψ φ₁ hψ]
      exact whole.2.2
    · exact ih inner hsub

end Formula

namespace Formula

variable {Label : Type} [LinearOrder Label]

/-- Guards recorded at an indexed query below an inspected live external head. -/
theorem indexedGuarded_query (R₁ R₂ : Label → Label → Prop) (B : Finset Label) (k : Nat)
    (head : Nat → Shape Nat → RecordedHead Nat Label) (χ : Formula Nat)
    (h : (χ.record head).IndexedGuarded R₁ R₂ B k)
    (b : Nat) (sh : Shape Nat) (ν : Label) (hq : (b, sh) ∈ χ.queries)
    (hhead : head b sh = .indexed b ν) :
    ∃ ψ : Formula Nat, ψ.shape = sh ∧ GuardChainIn R₂ B k ν ∧
      ∀ μ ∈ (ψ.record head).labelSupport, μ < ν ∧ R₁ μ ν := by
  induction χ with
  | falsum => simp [queries] at hq
  | equal t u => simp [queries] at hq
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ihφ h.1 hq
    · exact ihψ h.2 hq
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ihφ h.1 hq
    · exact ihψ h.2 hq
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ihφ h.1 hq
    · exact ihψ h.2 hq
  | neg φ ih => exact ih h hq
  | all x φ ih => exact ih h hq
  | ex x φ ih => exact ih h hq
  | know a φ ih =>
    have inner : (φ.record head).IndexedGuarded R₁ R₂ B k := by
      simp only [record] at h
      cases hh : head a φ.shape <;> simp only [hh, IndexedGuarded] at h
      · exact h
      · exact h.2.2
      · exact h
    rcases Finset.mem_insert.mp hq with heq | hsub
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [record, hhead, IndexedGuarded] at h
      exact ⟨φ, rfl, h.1, h.2.1⟩
    · exact ih inner hsub

/-- Every live external query of a main-guarded atom has its whole argument
guarded at the argument's own rank. -/
theorem mainGuarded_query (R₁ R₂ : Label → Label → Prop) (E : Finset Nat)
    (B : Finset Label) (head : Nat → Shape Nat → RecordedHead Nat Label)
    (herase : ∀ a sh, (head a sh).erase = a) (φ : Formula Nat)
    (h : (φ.record head).MainGuarded R₁ R₂ E B)
    (e : Nat) (shχ : Shape Nat) (hq : (e, shχ) ∈ φ.queries) (he : e ∈ E)
    (hlive : head e shχ = .live e) :
    ∃ χ : Formula Nat, χ.shape = shχ ∧ (χ.record head).IndexedGuarded R₁ R₂ B shχ.rank := by
  induction φ with
  | falsum => simp [queries] at hq
  | equal t u => simp [queries] at hq
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ihφ h.1 hq
    · exact ihψ h.2 hq
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ihφ h.1 hq
    · exact ihψ h.2 hq
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ihφ h.1 hq
    · exact ihψ h.2 hq
  | neg φ ih => exact ih h hq
  | all x φ ih => exact ih h hq
  | ex x φ ih => exact ih h hq
  | know a φ ih =>
    have inner : (φ.record head).MainGuarded R₁ R₂ E B := by
      simp only [record] at h
      cases hh : head a φ.shape <;> simp only [hh, MainGuarded] at h
      · exact h.2
      · exact h
      · exact h
    rcases Finset.mem_insert.mp hq with heq | hsub
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [record, hlive, MainGuarded] at h
      have hrank : (φ.record head).erase.shape.rank = φ.shape.rank := by
        rw [erase_record φ head herase]
      refine ⟨φ, rfl, ?_⟩
      simpa only [hrank] using h.1 he
    · exact ih inner hsub

/-- The two previous lemmas combined, for the actual main-row heads: below a
live external query, every active query has a guard of the external rank and
its whole argument class lies strictly and ≤₁-below the guarded label. -/
theorem mainGuarded_active_query (R₁ R₂ : Label → Label → Prop) (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (disjoint : Disjoint A E) (B : Finset Label) (φ : Formula Nat)
    (h : (φ.record (mainHeads A E H labels)).MainGuarded R₁ R₂ E B)
    (e : Nat) (shχ : Shape Nat) (hq : (e, shχ) ∈ φ.queries) (he : e ∈ E)
    (hH : (e, shχ) ∈ H) (b : Nat) (sh : Shape Nat) (hb : (b, sh) ∈ shχ.queries)
    (hbA : b ∈ A) (ψ : Formula Nat) (hψ : ψ.shape = sh) :
    GuardChainIn R₂ B shχ.rank (labels b sh) ∧
      ∀ μ ∈ (ψ.record (mainHeads A E H labels)).labelSupport,
        μ < labels b sh ∧ R₁ μ (labels b sh) := by
  have hlive : mainHeads A E H labels e shχ = .live e := by
    simp only [mainHeads, maskedHeads, he, hH, ↓reduceIte]
  obtain ⟨χ, hχ, guarded⟩ := mainGuarded_query R₁ R₂ E B (mainHeads A E H labels)
    (mainHeads_erase A E H labels) φ h e shχ hq he hlive
  have hbχ : (b, sh) ∈ χ.queries := by
    rw [← queries_shape, hχ]
    exact hb
  obtain ⟨ψ₀, hψ₀, chain, support⟩ := indexedGuarded_query R₁ R₂ B shχ.rank
    (mainHeads A E H labels) χ guarded b sh (labels b sh) hbχ
    (mainHeads_active A E H labels b sh hbA disjoint)
  refine ⟨chain, ?_⟩
  rw [labelSupport_record_shape _ ψ ψ₀ (hψ.trans hψ₀.symm)]
  exact support

end Formula

end Alexander313
