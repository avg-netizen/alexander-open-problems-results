import Alexander313.StageMainRow
import Alexander313.ColumnGenericity
import Alexander313.GenericityReduction

/-!
# Whole-ideal genericity by rank induction, and soundness of the actual family

Note 26 §5 recovers the entire ideal after stage soundness and then closes
G(J) with G_U. Here every theorem of a full original owner is lifted with the
depth table on the room copies of one guarded top whose rank exceeds the
theorem's rank, with every external argument kept live:

* for an active owner, guarded transport puts the lift in the actual cut at
  the top and stage soundness makes it true;
* for a passive owner of the lower ideal, `lift_truth` makes it true, with
  (X) supplied by exact room recovery instead of literal guards.

Exact room recovery identifies every active test of such a lift with its
source test, so the lift's stage truth is the theorem's truth in the old
filtered model. The hand proof's infinite chain is not needed. The
finite-policy reduction removes all but finitely many outside owners first,
so the external set is finite.

`idealGen_all` is the outer induction on the ordinal frontier rank, and
`family_sound` is note 26 §6. Both declarations belong to the checked
unconditional completion chain.
-/

namespace Alexander313

namespace ExtensionStage

variable {P : OrdinalPackage} {R : Nat → Nat → Prop} {C : CommonCorePresentation R}
    (S : ExtensionStage P C)

/-- The guarded room used to lift one formula: rank above the formula's rank
and one copy per active depth. -/
noncomputable def room (θ : Formula Nat) :
    RecordedStage.GuardedRoom P θ.shape.rank (θ.shape.activeDepth S.A + 1) :=
  RecordedStage.guardedRoom P _ _

/-- The room-labelled, externally live lift of a formula. -/
noncomputable def liftHeads (θ : Formula Nat) : Nat → Shape Nat → RecordedHead Nat P.Label :=
  mainHeads S.A S.E θ.queries (depthLabels S.A (S.room θ).copies.first)

/-- Exact recovery of every active test below a room lift. -/
theorem lift_active_exact (θ : Formula Nat) (c : Nat) (hcA : c ∈ S.A) (ψ : Formula Nat)
    (hq : (c, ψ.shape) ∈ θ.queries) :
    RecordedStage.cuts C S.A S.E P.R₁ P.R₂ c
        ((S.room θ).copies.first (ψ.shape.activeDepth S.A))
        (ψ.record (S.liftHeads θ)) ↔ C.family.effective.proves c ψ := by
  have hψ : ψ.queries ⊆ θ.queries := by
    rw [← Formula.queries_shape]
    exact Formula.queries_hereditary θ c ψ.shape hq
  have hθq : (c, ψ.shape) ∈ θ.shape.queries := by
    simpa only [Formula.queries_shape] using hq
  have hdepth : ψ.shape.activeDepth S.A < θ.shape.activeDepth S.A :=
    (Shape.activeDepth_query S.A θ.shape c ψ.shape hθq).2 hcA
  have hrank : ψ.shape.rank ≤ θ.shape.rank + 1 :=
    le_of_lt (lt_trans (Shape.rank_query θ.shape c ψ.shape hθq) (Nat.lt_succ_self _))
  have hH : ∀ e sh, (e, sh) ∈ ψ.queries → e ∈ S.E → (e, sh) ∈ θ.queries :=
    fun e sh h _ => hψ h
  have onRoom : ∀ μ ∈ (ψ.record (S.liftHeads θ)).labelSupport,
      ∃ d < ψ.shape.activeDepth S.A, μ = (S.room θ).copies.first d := by
    intro μ hμ
    obtain ⟨d, hd, rfl⟩ := Formula.record_depth_support S.A S.E θ.queries
      (S.room θ).copies.first S.sides.disjoint ψ μ hμ
    exact ⟨d, hd, rfl⟩
  have adm : (ψ.record (S.liftHeads θ)).RecordedAdmissible S.A S.E :=
    Formula.record_depth_admissible S.A S.E θ.queries (S.room θ).copies.first
      S.sides.disjoint (ψ.shape.activeDepth S.A)
      (fun d₁ d₂ h hd => (S.room θ).first_mono d₁ d₂ h (by omega)) ψ le_rfl
  by_cases hclosed : ψ.Closed
  · have h := RecordedStage.room_recovery P C S.A S.E S.sides c hcA (S.room θ) θ.queries
      (depthLabels S.A (S.room θ).copies.first) ψ hH hrank (ψ.shape.activeDepth S.A)
      (by omega) onRoom adm (fun _ => 0)
    rwa [Formula.close_eq_self_of_closed _ ((Formula.closed_record ψ _).mpr hclosed),
      Formula.close_eq_self_of_closed ψ hclosed] at h
  · constructor
    · intro h
      exact absurd ((Formula.closed_record ψ _).mp h.1) hclosed
    · intro h
      exact absurd (C.family.sentences c ψ h) hclosed

/-- The room lift is true in the stage model exactly when the formula is true
in the old filtered model. -/
theorem lift_transfer (θ : Formula Nat) (t : Assignment) :
    filteredTruth S.M (θ.record (S.liftHeads θ)) t ↔ filteredTruth S.live θ t := by
  have herase : ∀ b sh, (S.liftHeads θ b sh).erase = b :=
    mainHeads_erase S.A S.E θ.queries (depthLabels S.A (S.room θ).copies.first)
  have agree : AgreeOn (reconstructedPredicates (S.liftHeads θ) S.M) S.live θ := by
    intro b ψ hq
    cases hh : S.liftHeads θ b ψ.shape with
    | live c =>
      have hcb : c = b := by simpa only [hh, RecordedHead.erase] using herase b ψ.shape
      rw [hcb] at hh
      exact reconstructed_live _ herase S.live _ b ψ hh
    | ghost c =>
      exact absurd hq (S.mainHeads_ghost_iff θ.queries _ hh).2
    | indexed c ν =>
      obtain ⟨hbA, hcb, hν⟩ := S.mainHeads_indexed_active θ.queries _ hh
      rw [hcb] at hh
      have step₁ := reconstructed_indexed (S.liftHeads θ) S.live
        (RecordedStage.cuts C S.A S.E P.R₁ P.R₂) b ν ψ hh
      have step₂ : RecordedStage.cuts C S.A S.E P.R₁ P.R₂ b ν (ψ.record (S.liftHeads θ)) ↔
          C.family.effective.proves b ψ := by
        rw [hν]
        exact S.lift_active_exact θ b hbA ψ hq
      exact step₁.trans (step₂.trans (S.retained b (S.active_full hbA) ψ).symm)
  exact (truth_reconstructed true (S.liftHeads θ) S.M θ t).symm.trans
    (truth_congr_queries true _ S.live θ t agree)

/-- Recovery of an active owner from stage soundness and guarded transport. -/
theorem active_sound (stageSound : ∀ b ν, RawSound S.M (.indexed b ν))
    (b : Nat) (hbA : b ∈ S.A) : RawSound S.live b := by
  intro θ u hp
  let φ := θ.close u
  have hφ : φ.Closed := θ.close_closed u
  have hsrc : C.family.effective.proves b φ := (S.retained b (S.active_full hbA) φ).mp hp
  have hcut := RecordedStage.room_transport P C S.A S.E S.sides b hbA (S.room φ) φ.queries
    (depthLabels S.A (S.room φ).copies.first) φ (fun e sh h _ => h) (Nat.le_succ _)
    (by
      intro μ hμ
      obtain ⟨d, hd, rfl⟩ := Formula.record_depth_support S.A S.E φ.queries
        (S.room φ).copies.first S.sides.disjoint φ μ hμ
      exact ⟨d, by omega, rfl⟩)
    (Formula.record_depth_admissible S.A S.E φ.queries (S.room φ).copies.first
      S.sides.disjoint (φ.shape.activeDepth S.A)
      (fun d₁ d₂ h hd => (S.room φ).first_mono d₁ d₂ h (by omega)) φ le_rfl)
    (fun _ => 0) (by rw [Formula.close_eq_self_of_closed φ hφ]; exact hsrc)
  have htrue := stageSound b _ (φ.record (S.liftHeads φ)) (fun _ => 0) hcut
  have hlive := (S.lift_transfer φ (fun _ => 0)).mp htrue
  exact (truth_close true S.live θ u (fun _ => 0)).mp hlive

/-- Recovery of a passive owner of the lower ideal by lower-rank genericity. -/
theorem lower_sound (eff : StageEffectivity C)
    (IH : ∀ J' : Finset Nat, J'.Nonempty → FrontierAntichain R J' →
      frontierRank S.wf J' < frontierRank S.wf S.J → IdealGen C J')
    (stageSound : ∀ b ν, RawSound S.M (.indexed b ν))
    (b : Nat) (hbFull : IdealFull R S.J b) (hbA : b ∉ S.A) : RawSound S.live b := by
  intro θ u hp
  let φ := θ.close u
  have hφ : φ.Closed := θ.close_closed u
  have hsrc : C.family.effective.proves b φ := (S.retained b hbFull φ).mp hp
  have htrue := S.lift_truth eff IH b hbFull hbA φ.queries
    (depthLabels S.A (S.room φ).copies.first) (target_queries_hereditary φ) φ
    (fun c μ _ => stageSound c μ)
    (by
      intro e sh hq _ _ c sh'' hc hcA ψ hψ
      have hq' : (c, ψ.shape) ∈ φ.queries := by
        rw [hψ]
        exact Formula.queries_hereditary φ e sh hq hc
      have h := S.lift_active_exact φ c hcA ψ hq'
      rw [hψ] at h
      exact h)
    (fun _ => 0) (by rw [Formula.close_eq_self_of_closed φ hφ]; exact hsrc)
  have hlive := (S.lift_transfer φ (fun _ => 0)).mp htrue
  exact (truth_close true S.live θ u (fun _ => 0)).mp hlive

end ExtensionStage

/-- One step of the rank induction: Lemma G(J). -/
theorem idealGen_step (P : OrdinalPackage) {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} (eff : StageEffectivity C) (wf : WellFounded R)
    (J : Finset Nat) (anti : FrontierAntichain R J)
    (IH : ∀ J' : Finset Nat, J'.Nonempty → FrontierAntichain R J' →
      frontierRank wf J' < frontierRank wf J → IdealGen C J') :
    IdealGen C J := by
  classical
  unfold IdealGen
  apply finite_policy_genericity_reduction C.family.effective.proves (IdealFull R J)
    ColumnAdmissible (fun Q hQ φ => rawShapeMask_columnAdmissible hQ (IdealFull R J) φ.queries)
  intro Q hQ retained outside policy
  obtain ⟨Hpol, hpol⟩ := policy
  let E : Finset Nat := (Hpol.image Prod.fst).filter (fun b => ¬ IdealFull R J b)
  let S : ExtensionStage P C := {
    wf := wf
    J := J
    antichain := anti
    E := E
    external := fun e he => (Finset.mem_filter.mp he).2
    live := Q
    admissible := hQ
    retained := retained
    outside_sound := outside
    outside_empty := by
      intro a ha haE θ hθ
      apply haE
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(a, θ.shape), hpol a θ ha hθ, rfl⟩, ha⟩ }
  have stageSound := RecordedStage.stage_sound P C S.A S.E Q hQ.1
    (fun a σ h lower s => S.mainRow_truth eff IH a σ h lower s)
  have positive : ∀ d, DownIdeal R J d → RawSound Q (d + 1) := by
    intro d hd
    by_cases hA : d + 1 ∈ S.A
    · exact S.active_sound stageSound (d + 1) hA
    · exact S.lower_sound eff IH stageSound (d + 1) (Or.inr ⟨d, rfl, hd⟩) hA
  intro a ha
  rcases ha with rfl | ⟨d, rfl, hd⟩
  · apply C.core_genericity_columns Q hQ (retained 0 (Or.inl rfl))
    intro j
    by_cases hj : DownIdeal R J j
    · exact positive j hj
    · apply outside (j + 1)
      rintro (h | ⟨d, hd', h⟩)
      · omega
      · have hjd : j = d := by omega
        subst hjd
        exact hj h
  · exact positive d hd

/-- Lemma G(J) for every finite R⁺-antichain, by induction on frontier rank. -/
theorem idealGen_all (P : OrdinalPackage) {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} (eff : StageEffectivity C) (wf : WellFounded R) :
    ∀ J : Finset Nat, FrontierAntichain R J → IdealGen C J := by
  suffices key : ∀ o : Ordinal, ∀ J : Finset Nat, frontierRank wf J = o →
      FrontierAntichain R J → IdealGen C J by
    exact fun J anti => key _ J rfl anti
  intro o
  induction o using Ordinal.induction with
  | h o ih =>
    intro J hJo anti
    apply idealGen_step P eff wf J anti
    intro J' _ anti' hlt
    exact ih _ (hJo ▸ hlt) J' rfl anti'

/-- Note 26 §6: every theorem of every machine of the actual family is true. -/
theorem family_sound (P : OrdinalPackage) {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} (eff : StageEffectivity C) (wf : WellFounded R) :
    ∀ a, RawSound C.family.effective.proves a := by
  classical
  have orig : ∀ i, RawSound C.family.effective.proves (i + 1) := by
    intro i θ s hp
    let F : Finset Nat :=
      insert i (((θ.queries.image Prod.fst).filter (· ≠ 0)).image (· - 1))
    let J := maximalFrontier R F
    have hi : DownIdeal R J i := finite_frontier_covers wf F i (Finset.mem_insert_self _ _)
    let Q : RawPredicates Nat := fun b ψ => IdealFull R J b ∧ C.family.effective.proves b ψ
    have hQ : ColumnAdmissible Q :=
      C.family.columnAdmissible.restrict (fun b _ => IdealFull R J b)
    have sound := idealGen_all P eff wf J (maximalFrontier_antichain R F) Q hQ
      (fun b hb ψ => and_iff_right hb)
      (fun b hb ψ u h => absurd h.1 hb) (i + 1) (Or.inr ⟨i, rfl, hi⟩)
    have hθQ := sound θ s ⟨Or.inr ⟨i, rfl, hi⟩, hp⟩
    have agree : AgreeOn Q C.family.effective.proves θ := by
      intro b ψ hq
      have hb : IdealFull R J b := by
        rcases Nat.eq_zero_or_pos b with rfl | hpos
        · exact Or.inl rfl
        · refine Or.inr ⟨b - 1, by omega, finite_frontier_covers wf F (b - 1) ?_⟩
          apply Finset.mem_insert_of_mem
          exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨(b, ψ.shape), hq, rfl⟩, by omega⟩, rfl⟩
      exact and_iff_right hb
    exact (truth_congr_queries true Q _ θ s agree).mp hθQ
  intro a
  cases a with
  | zero =>
    exact C.core_genericity_columns _ C.family.columnAdmissible (fun _ => Iff.rfl) orig
  | succ i => exact orig i

end Alexander313
