import Alexander313.StageCutSoundness
import Alexander313.RecordedFixedLabelTransport
import Alexander313.RecordedStageColumns
import Alexander313.Hierarchy

/-!
# Local truth of guarded code rows (note 26 §5)

This file states Lemma G(J) with Nat owners (owner 0 is the core, owner d+1 the
original machine d) and proves the decisive local step of its induction.

An `ExtensionStage` is the setting of one genericity step for a finite
R⁺-antichain J: the active set is J's image, the finite external set E holds
every nonempty outside owner, the live predicates retain the core and the
whole original ideal of J in full, outside owners are fully sound, and every
other outside owner is empty.

`lift_truth` is the reconstruction argument of note 24 §7 combined with the
outer rank induction. A recorded lift of a theorem of a full, non-active owner
is true in the stage model as soon as (S) every cut at one of its labels is
sound and (X) below every retained live external argument the active tests are
exactly their source tests. The reconstructed predicates keep the core and the
retained lower ideal of the finite frontier A′ of the formula's lower names in
full; active owners get masked stage tests, external owners their old live
classes, everything else is empty. These predicates are column admissible.
Lower-rank G(A′), or G_U when A′ is empty, then makes the source theorem true
in the reconstruction, hence its lift true in the stage model.

`mainRow_truth` derives (X) from the literal guards of a main row by guarded
fixed-label transport and applies `lift_truth` to the source code body.
These declarations belong to the checked unconditional completion chain.
-/

namespace Alexander313

/-- The core and the whole original downward ideal of J. -/
def IdealFull (R : Nat → Nat → Prop) (J : Finset Nat) (a : Nat) : Prop :=
  a = 0 ∨ ∃ d, a = d + 1 ∧ DownIdeal R J d

/-- Note 26 §5, Lemma G(J), with the core included in the conclusion. -/
def IdealGen {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (J : Finset Nat) : Prop :=
  ∀ Q : RawPredicates Nat, ColumnAdmissible Q →
    (∀ a, IdealFull R J a → ∀ θ, Q a θ ↔ C.family.effective.proves a θ) →
    (∀ a, ¬ IdealFull R J a → RawSound Q a) →
    ∀ a, IdealFull R J a → RawSound Q a

theorem idealFull_empty {R : Nat → Nat → Prop} {a : Nat} : IdealFull R ∅ a ↔ a = 0 := by
  constructor
  · rintro (h | ⟨d, _, j, hj, _⟩)
    · exact h
    · exact absurd hj (Finset.notMem_empty j)
  · intro h
    exact Or.inl h

/-- G(∅) is core genericity. -/
theorem idealGen_empty {R : Nat → Nat → Prop} (C : CommonCorePresentation R) :
    IdealGen C ∅ := by
  intro Q hQ retained outside a ha
  have ha0 := idealFull_empty.mp ha
  subst ha0
  apply C.core_genericity_columns Q hQ (retained 0 (Or.inl rfl))
  intro j
  apply outside (j + 1)
  intro h
  have := idealFull_empty.mp h
  omega

/-- Reconstructed stage predicates are column admissible. -/
theorem reconstructed_stage_columnAdmissible (P : OrdinalPackage) {R : Nat → Nat → Prop}
    {C : CommonCorePresentation R} (eff : StageEffectivity C) (A E : Finset Nat)
    (Q : RawPredicates Nat) (hQ : ColumnAdmissible Q)
    (head : Nat → Shape Nat → RecordedHead Nat P.Label)
    (herase : ∀ a sh, (head a sh).erase = a) :
    ColumnAdmissible (reconstructedPredicates head (RecordedStage.predicates C A E P.R₁ P.R₂ Q)) := by
  constructor
  · intro b φ ψ hφ hψ hα
    have hs : φ.shape = ψ.shape := hα.shape_eq
    simp only [reconstructedPredicates, hs]
    exact RecordedStage.rawAlphabetic C A E P.R₁ P.R₂ Q hQ.1 (head b ψ.shape)
      (φ.record head) (ψ.record head) ((Formula.closed_record φ head).mpr hφ)
      ((Formula.closed_record ψ head).mpr hψ) (hα.record head)
  · intro b φ x s
    cases hh : head b φ.shape with
    | live c =>
      have hcb : c = b := by simpa only [hh, RecordedHead.erase] using herase b φ.shape
      rw [hcb] at hh
      apply column_congr _ (hQ.2 b φ x s)
      intro n
      simp only [reconstructedPredicates, Formula.shape_close, hh, RecordedStage.predicates,
        sourceQueries, Formula.erase_record _ head herase]
    | indexed c ν =>
      apply column_congr _ (RecordedStage.cut_column P eff A E c ν (φ.record head) x s)
      intro n
      simp only [reconstructedPredicates, Formula.shape_close, hh, RecordedStage.predicates,
        sourceQueries, Formula.record_close]
    | ghost c =>
      apply column_of_false
      intro n h
      simp only [reconstructedPredicates, Formula.shape_close, hh, RecordedStage.predicates,
        sourceQueries] at h

/-- The setting of one whole-ideal genericity step. -/
structure ExtensionStage (P : OrdinalPackage) {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) where
  wf : WellFounded R
  J : Finset Nat
  antichain : FrontierAntichain R J
  E : Finset Nat
  external : ∀ e ∈ E, ¬ IdealFull R J e
  live : RawPredicates Nat
  admissible : ColumnAdmissible live
  retained : ∀ a, IdealFull R J a → ∀ θ, live a θ ↔ C.family.effective.proves a θ
  outside_sound : ∀ a, ¬ IdealFull R J a → RawSound live a
  outside_empty : ∀ a, ¬ IdealFull R J a → a ∉ E → ∀ θ, ¬ live a θ

namespace ExtensionStage

variable {P : OrdinalPackage} {R : Nat → Nat → Prop} {C : CommonCorePresentation R}
    (S : ExtensionStage P C)

def A : Finset Nat := S.J.image (· + 1)

theorem mem_A {b : Nat} : b ∈ S.A ↔ ∃ i ∈ S.J, b = i + 1 := by
  simp only [A, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem active_full {b : Nat} (hb : b ∈ S.A) : IdealFull R S.J b := by
  obtain ⟨i, hi, rfl⟩ := S.mem_A.mp hb
  exact Or.inr ⟨i, rfl, i, hi, Or.inl rfl⟩

theorem zero_not_A : 0 ∉ S.A := by
  intro h
  obtain ⟨i, _, hi⟩ := S.mem_A.mp h
  omega

theorem full_not_E {b : Nat} (hb : IdealFull R S.J b) : b ∉ S.E :=
  fun he => S.external b he hb

theorem zero_not_E : 0 ∉ S.E := S.full_not_E (Or.inl rfl)

theorem sides : ExtensionSides R S.A S.E where
  disjoint := by
    rw [Finset.disjoint_left]
    intro b hA hE
    exact S.full_not_E (S.active_full hA) hE
  core_active := S.zero_not_A
  core_external := S.zero_not_E
  codes := by
    intro i j hi hji
    obtain ⟨i', hi', heq⟩ := S.mem_A.mp hi
    have hii : i = i' := by omega
    subst hii
    constructor
    · intro hj
      obtain ⟨j', hj', hjeq⟩ := S.mem_A.mp hj
      have hjj : j = j' := by omega
      subst hjj
      exact S.antichain j hj' i hi' (.edge hji)
    · exact S.full_not_E (Or.inr ⟨j, rfl, i, hi', Or.inr (.edge hji)⟩)

/-- The stage model. -/
def M : RawPredicates (RecordedHead Nat P.Label) :=
  RecordedStage.predicates C S.A S.E P.R₁ P.R₂ S.live

/-- Original names, below J, of a formula together with a distinguished owner. -/
noncomputable def lowerNames (w : Nat) (θ : Formula Nat) : Finset Nat := by
  classical
  exact ((insert w (θ.queries.image Prod.fst)).filter
    (fun b => b ≠ 0 ∧ ∃ i ∈ S.J, StrictBelow R (b - 1) i)).image (· - 1)

theorem lowerNames_below (w : Nat) (θ : Formula Nat) :
    ∀ x ∈ S.lowerNames w θ, ∃ i ∈ S.J, StrictBelow R x i := by
  intro x hx
  classical
  simp only [lowerNames, Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨b, ⟨_, _, h⟩, rfl⟩ := hx
  exact h

theorem lowerNames_mem (w : Nat) (θ : Formula Nat) (b : Nat)
    (hb : b ∈ insert w (θ.queries.image Prod.fst)) (hb0 : b ≠ 0)
    (h : ∃ i ∈ S.J, StrictBelow R (b - 1) i) : b - 1 ∈ S.lowerNames w θ := by
  classical
  simp only [lowerNames, Finset.mem_image, Finset.mem_filter]
  exact ⟨b, ⟨hb, hb0, h⟩, rfl⟩

/-- Full owners of the lower frontier are full, passive and internal for J. -/
theorem frontierFull (w : Nat) (θ : Formula Nat) (b : Nat)
    (hb : IdealFull R (maximalFrontier R (S.lowerNames w θ)) b) :
    IdealFull R S.J b ∧ b ∉ S.A ∧ b ∉ S.E := by
  classical
  rcases hb with rfl | ⟨d, rfl, a', ha', hd⟩
  · exact ⟨Or.inl rfl, S.zero_not_A, S.zero_not_E⟩
  · have ha'F : a' ∈ S.lowerNames w θ := by
      simp only [maximalFrontier, Finset.mem_filter] at ha'
      exact ha'.1
    obtain ⟨i, hi, hbelow⟩ := S.lowerNames_below w θ a' ha'F
    have hdi : StrictBelow R d i := by
      rcases hd with rfl | hd
      · exact hbelow
      · exact .trans hd hbelow
    have hfull : IdealFull R S.J (d + 1) := Or.inr ⟨d, rfl, i, hi, Or.inr hdi⟩
    refine ⟨hfull, ?_, S.full_not_E hfull⟩
    intro hA
    obtain ⟨i', hi', heq⟩ := S.mem_A.mp hA
    have hdd : d = i' := by omega
    subst hdd
    exact S.antichain d hi' i hi hdi

/-- Every passive full owner of the formula lies in the lower frontier's ideal. -/
theorem ownerFull (w : Nat) (θ : Formula Nat) (b : Nat)
    (hbo : b ∈ insert w (θ.queries.image Prod.fst)) (hfull : IdealFull R S.J b)
    (hbA : b ∉ S.A) : IdealFull R (maximalFrontier R (S.lowerNames w θ)) b := by
  rcases hfull with rfl | ⟨d, rfl, j, hj, hd⟩
  · exact Or.inl rfl
  · rcases hd with rfl | hd
    · exact absurd (S.mem_A.mpr ⟨d, hj, rfl⟩) hbA
    · have hdn : d ∈ S.lowerNames w θ := by
        have h := S.lowerNames_mem w θ (d + 1) hbo (by omega)
          ⟨j, hj, by simpa only [Nat.add_sub_cancel] using hd⟩
        simpa only [Nat.add_sub_cancel] using h
      exact Or.inr ⟨d, rfl, finite_frontier_covers S.wf _ d hdn⟩

theorem mainHeads_ghost_iff (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → P.Label)
    {b c : Nat} {sh : Shape Nat} (h : mainHeads S.A S.E H labels b sh = .ghost c) :
    b ∈ S.E ∧ (b, sh) ∉ H := by
  by_cases hE : b ∈ S.E
  · by_cases hH : (b, sh) ∈ H
    · simp [mainHeads, maskedHeads, hE, hH] at h
    · exact ⟨hE, hH⟩
  · by_cases hA : b ∈ S.A <;> simp [mainHeads, maskedHeads, hE, hA] at h

theorem mainHeads_indexed_active (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → P.Label) {b c : Nat} {sh : Shape Nat} {ν : P.Label}
    (h : mainHeads S.A S.E H labels b sh = .indexed c ν) :
    b ∈ S.A ∧ c = b ∧ ν = labels b sh := by
  by_cases hA : b ∈ S.A
  · have own := mainHeads_active S.A S.E H labels b sh hA S.sides.disjoint
    rw [own] at h
    injection h with h₁ h₂
    exact ⟨hA, h₁.symm, h₂.symm⟩
  · exact absurd h (Formula.mainHeads_not_indexed S.A S.E H labels b sh hA c ν)

/-- The reconstruction argument of note 24 §7 with the outer rank induction. -/
theorem lift_truth (eff : StageEffectivity C)
    (IH : ∀ J' : Finset Nat, J'.Nonempty → FrontierAntichain R J' →
      frontierRank S.wf J' < frontierRank S.wf S.J → IdealGen C J')
    (w : Nat) (hwFull : IdealFull R S.J w) (hwA : w ∉ S.A)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → P.Label)
    (hH : HereditaryQueries H) (θ : Formula Nat)
    (lower : ∀ b, ∀ μ ∈ (θ.record (mainHeads S.A S.E H labels)).labelSupport,
      RawSound S.M (.indexed b μ))
    (hX : ∀ e sh, (e, sh) ∈ θ.queries → e ∈ S.E → (e, sh) ∈ H →
      ∀ c sh'', (c, sh'') ∈ sh.queries → c ∈ S.A → ∀ ψ : Formula Nat, ψ.shape = sh'' →
        (RecordedStage.cuts C S.A S.E P.R₁ P.R₂ c (labels c sh'')
            (ψ.record (mainHeads S.A S.E H labels)) ↔
          C.family.effective.proves c ψ))
    (t : Assignment) (hsrc : C.family.effective.proves w (θ.close t)) :
    filteredTruth S.M (θ.record (mainHeads S.A S.E H labels)) t := by
  classical
  let heads := mainHeads S.A S.E H labels
  have herase : ∀ b sh, (heads b sh).erase = b := mainHeads_erase S.A S.E H labels
  let A' := maximalFrontier R (S.lowerNames w θ)
  have ownerOf : ∀ b sh, (b, sh) ∈ θ.queries → b ∈ insert w (θ.queries.image Prod.fst) :=
    fun b sh h => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(b, sh), h, rfl⟩)
  have wFull' : IdealFull R A' w :=
    S.ownerFull w θ w (Finset.mem_insert_self _ _) hwFull hwA
  let recon := reconstructedPredicates heads S.M
  let Q' : RawPredicates Nat := selectPredicates (fun b _ => IdealFull R A' b)
    C.family.effective.proves (fun b ψ => (b, ψ.shape) ∈ θ.queries ∧ recon b ψ)
  have fullLive : ∀ b sh, IdealFull R A' b → heads b sh = .live b := fun b sh hb =>
    RecordedStage.mainHeads_outside_live S.A S.E H labels b sh
      (S.frontierFull w θ b hb).2.1 (S.frontierFull w θ b hb).2.2
  have recon_full : ∀ b ψ, IdealFull R A' b → (recon b ψ ↔ C.family.effective.proves b ψ) := by
    intro b ψ hb
    exact (reconstructed_live heads herase S.live
      (RecordedStage.cuts C S.A S.E P.R₁ P.R₂) b ψ (fullLive b ψ.shape hb)).trans
      (S.retained b (S.frontierFull w θ b hb).1 ψ)
  have agree : AgreeOn Q' recon θ := by
    intro b ψ hq
    by_cases hb : IdealFull R A' b
    · exact (selectPredicates_pos hb).trans (recon_full b ψ hb).symm
    · exact (selectPredicates_neg hb).trans (and_iff_right hq)
  have truthIff : ∀ ψ u, ψ.queries ⊆ θ.queries →
      (filteredTruth Q' ψ u ↔ filteredTruth S.M (ψ.record heads) u) := by
    intro ψ u hsub
    exact (truth_congr_queries true Q' recon ψ u (agree.mono hsub)).trans
      (truth_reconstructed true heads S.M ψ u)
  have subQueries : ∀ b (ψ : Formula Nat), (b, ψ.shape) ∈ θ.queries → ψ.queries ⊆ θ.queries := by
    intro b ψ h
    rw [← Formula.queries_shape]
    exact Formula.queries_hereditary θ b ψ.shape h
  have adm' : ColumnAdmissible Q' :=
    ColumnAdmissible.select _ C.family.columnAdmissible
      ((reconstructed_stage_columnAdmissible P eff S.A S.E S.live S.admissible heads
        herase).restrict (fun b sh => (b, sh) ∈ θ.queries))
  have retained' : ∀ b, IdealFull R A' b → ∀ ψ, Q' b ψ ↔ C.family.effective.proves b ψ :=
    fun b hb ψ => selectPredicates_pos hb
  have outside' : ∀ b, ¬ IdealFull R A' b → RawSound Q' b := by
    intro b hb ψ u hp
    obtain ⟨hq, hrec⟩ := (selectPredicates_neg hb).mp hp
    rw [Formula.shape_close] at hq
    have hsub := subQueries b ψ hq
    cases hh : heads b ψ.shape with
    | indexed c ν =>
      obtain ⟨hbA, hcb, hν⟩ := S.mainHeads_indexed_active H labels hh
      rw [hcb] at hh
      have hmem : ν ∈ (θ.record heads).labelSupport := by
        rw [hν]
        exact Formula.query_label_mem S.A S.E H labels S.sides.disjoint θ b ψ.shape hq hbA
      have hrec' : RecordedStage.cuts C S.A S.E P.R₁ P.R₂ b ν ((ψ.close u).record heads) :=
        (reconstructed_indexed heads S.live (RecordedStage.cuts C S.A S.E P.R₁ P.R₂)
          b ν (ψ.close u) (by simpa only [Formula.shape_close] using hh)).mp hrec
      have hcut : S.M (.indexed b ν) ((ψ.record heads).close u) := by
        rw [← Formula.record_close]
        exact hrec'
      exact (truthIff ψ u hsub).mpr (lower b ν hmem (ψ.record heads) u hcut)
    | live c =>
      have hcb : c = b := by simpa only [hh, RecordedHead.erase] using herase b ψ.shape
      rw [hcb] at hh
      have hold : S.live b (ψ.close u) :=
        (reconstructed_live heads herase S.live _ b (ψ.close u)
          (by simpa only [Formula.shape_close] using hh)).mp hrec
      by_cases hbE : b ∈ S.E
      · have hH' : (b, ψ.shape) ∈ H := by
          by_contra hn
          have hg : heads b ψ.shape = .ghost b := maskedHeads_ghost S.E H _ b ψ.shape hbE hn
          rw [hh] at hg
          cases hg
        have hsubH : ψ.queries ⊆ H := by
          rw [← Formula.queries_shape]
          exact hH b ψ.shape hH'
        have oldTrue := S.outside_sound b (S.external b hbE) ψ u hold
        have agreeLive : AgreeOn Q' S.live ψ := by
          intro d χ hdq
          have hdθ : (d, χ.shape) ∈ θ.queries := hsub hdq
          have hdH : (d, χ.shape) ∈ H := hsubH hdq
          by_cases hd : IdealFull R A' d
          · exact (selectPredicates_pos hd).trans (S.retained d (S.frontierFull w θ d hd).1 χ).symm
          · have step₁ : Q' d χ ↔ recon d χ :=
              (selectPredicates_neg hd).trans (and_iff_right hdθ)
            cases hdh : heads d χ.shape with
            | live d' =>
              have hdd : d' = d := by simpa only [hdh, RecordedHead.erase] using herase d χ.shape
              rw [hdd] at hdh
              exact step₁.trans (reconstructed_live heads herase S.live _ d χ hdh)
            | ghost d' =>
              exact absurd hdH (S.mainHeads_ghost_iff H labels hdh).2
            | indexed d' ν' =>
              obtain ⟨hdA, hdd, hν'⟩ := S.mainHeads_indexed_active H labels hdh
              rw [hdd] at hdh
              have step₂ : recon d χ ↔
                  RecordedStage.cuts C S.A S.E P.R₁ P.R₂ d ν' (χ.record heads) :=
                reconstructed_indexed heads S.live _ d ν' χ hdh
              have hdq' : (d, χ.shape) ∈ ψ.shape.queries := by
                simpa only [Formula.queries_shape] using hdq
              have step₃ : RecordedStage.cuts C S.A S.E P.R₁ P.R₂ d ν' (χ.record heads) ↔
                  C.family.effective.proves d χ := by
                rw [hν']
                exact hX b ψ.shape hq hbE hH' d χ.shape hdq' hdA χ rfl
              exact step₁.trans (step₂.trans (step₃.trans
                (S.retained d (S.active_full hdA) χ).symm))
        exact (truth_congr_queries true Q' S.live ψ u agreeLive).mpr oldTrue
      · exfalso
        have hbA : b ∉ S.A := by
          intro hA
          have own := mainHeads_active S.A S.E H labels b ψ.shape hA S.sides.disjoint
          have hh' : heads b ψ.shape = .indexed b (labels b ψ.shape) := own
          rw [hh] at hh'
          cases hh'
        by_cases hbFull : IdealFull R S.J b
        · exact hb (S.ownerFull w θ b (ownerOf b ψ.shape hq) hbFull hbA)
        · exact S.outside_empty b hbFull hbE (ψ.close u) hold
    | ghost c =>
      exact absurd hrec (reconstructed_ghost heads S.live _ b c (ψ.close u)
        (by simpa only [Formula.shape_close] using hh))
  have gen : IdealGen C A' := by
    by_cases hA' : A'.Nonempty
    · apply IH A' hA' (maximalFrontier_antichain R _)
      apply frontierRank_strict S.wf A' S.J hA'
      intro x hx
      have hxF : x ∈ S.lowerNames w θ := by
        simp only [A', maximalFrontier, Finset.mem_filter] at hx
        exact hx.1
      exact S.lowerNames_below w θ x hxF
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA']
      exact idealGen_empty C
  have soundW := gen Q' adm' retained' outside' w wFull'
  have hθ := soundW θ t ((retained' w wFull' _).mpr hsrc)
  exact (truthIff θ t (fun _ h => h)).mp hθ

/-- Local truth of every guarded main row, from soundness of its own cuts. -/
theorem mainRow_truth (eff : StageEffectivity C)
    (IH : ∀ J' : Finset Nat, J'.Nonempty → FrontierAntichain R J' →
      frontierRank S.wf J' < frontierRank S.wf S.J → IdealGen C J')
    (a : Nat) (σ : Formula (RecordedHead Nat P.Label))
    (hmain : RecordedMain C S.A S.E a P.R₁ P.R₂ σ)
    (lower : ∀ b, ∀ μ ∈ σ.labelSupport, RawSound S.M (.indexed b μ)) (s : Assignment) :
    filteredTruth S.M σ s := by
  obtain ⟨σ₀, atom, H, labels, ms, hsrc, hH, _, _, _, hguard, rfl, hadm⟩ := hmain
  let heads := mainHeads S.A S.E H labels
  have codeRow : ∀ (w : Nat) (φ : UnaryFormula Nat), IdealFull R S.J w → w ∉ S.A → w ∉ S.E →
      atom = .know w φ.body →
      σ₀ = codeSentence C.arithmetic w φ (C.family.unaryColumnIndex w φ) →
      filteredTruth S.M (markerPadding a ms (σ₀.record heads)) s := by
    intro w φ hwFull hwA hwE hatom hσ₀
    subst hatom
    subst hσ₀
    have hlive : heads w φ.body.shape = .live w :=
      RecordedStage.mainHeads_outside_live S.A S.E H labels w φ.body.shape hwA hwE
    have hrecord : (codeSentence C.arithmetic w φ (C.family.unaryColumnIndex w φ)).record heads =
        .all φ.input (Formula.iff (.know (.live w) (φ.body.record heads))
          ((C.arithmetic.member (Term.numeral (C.family.unaryColumnIndex w φ))
            (.var φ.input)).record heads)) := by
      simp only [codeSentence, Formula.record_iff, Formula.record, hlive]
    have bodySupport : ∀ μ ∈ (φ.body.record heads).labelSupport,
        μ ∈ (markerPadding a ms ((codeSentence C.arithmetic w φ
          (C.family.unaryColumnIndex w φ)).record heads)).labelSupport := by
      intro μ hμ
      rw [markerPadding_support, hrecord]
      apply Finset.mem_union_right
      simp only [Formula.labelSupport, Formula.labelSupport_iff, Finset.mem_union]
      exact Or.inl hμ
    have bodyAdm : (φ.body.record heads).RecordedAdmissible S.A S.E := by
      have h := markerPadding_body_admissible S.A S.E a ms _ hadm
      rw [hrecord] at h
      have h' := (Formula.recordedAdmissible_iff_iff S.A S.E _ _).mp h
      exact ⟨h'.1.1.2, h'.1.2⟩
    dsimp only [M, heads]
    rw [RecordedStage.retained_code_padding_truth_iff C S.A S.E P.R₁ P.R₂ S.live H labels a w
      ms hwA hwE (S.retained w hwFull) φ s]
    intro n hn
    apply S.lift_truth eff IH w hwFull hwA H labels hH φ.body
      (fun b μ hμ => lower b μ (bodySupport μ hμ)) ?_ (Function.update s φ.input n)
      ((S.retained w hwFull _).mp hn)
    -- exact recovery below every live external argument, from the literal guards
    intro e sh hq he heH c sh'' hc hcA ψ hψ
    obtain ⟨chainG, suppG⟩ := Formula.mainGuarded_active_query P.R₁ P.R₂ S.A S.E H labels
      S.sides.disjoint (markerPoints ms) (.know w φ.body) hguard e sh
      (Finset.mem_insert_of_mem hq) he heH c sh'' hc hcA ψ hψ
    constructor
    · intro hcut
      have h := RecordedStage.cuts_erasure C S.A S.E P.R₁ P.R₂ c _ hcut
      simpa only [Formula.erase_record _ _ (mainHeads_erase S.A S.E H labels)] using h
    · intro hsrcψ
      have hclosed : ψ.Closed := C.family.sentences c ψ hsrcψ
      have hrank : 1 ≤ sh.rank := by cases sh <;> simp [Shape.rank]
      have guardTop : GuardHead P.R₂ (sh.rank - 1 + 1) (labels c sh'') := by
        rw [Nat.sub_add_cancel hrank]
        exact chainG.guardHead
      have hψrank : ψ.shape.rank ≤ sh.rank - 1 + 1 := by
        rw [hψ, Nat.sub_add_cancel hrank]
        exact le_of_lt (Shape.rank_query sh c sh'' hc)
      have hψq : ψ.queries ⊆ sh.queries := by
        rw [← Formula.queries_shape, hψ]
        exact Shape.queries_hereditary sh c sh'' hc
      have hH'' : ∀ e' sh', (e', sh') ∈ ψ.queries → e' ∈ S.E → (e', sh') ∈ H :=
        fun e' sh' h _ => hH e sh heH (hψq h)
      have hcθ : (c, sh'') ∈ φ.body.queries := by
        rw [← Formula.queries_shape] at hq ⊢
        exact Shape.queries_hereditary φ.body.shape e sh hq hc
      have admψ : (ψ.record heads).RecordedAdmissible S.A S.E :=
        (Formula.query_support_below S.A S.E H labels S.sides.disjoint φ.body bodyAdm c sh''
          hcθ hcA ψ hψ).1
      have hcut := RecordedStage.fixed_label_transport_mask P C S.A S.E S.sides c hcA
        (labels c sh'') (sh.rank - 1) guardTop H labels ψ hH'' hψrank admψ suppG
        (fun _ => 0) (by rw [Formula.close_eq_self_of_closed ψ hclosed]; exact hsrcψ)
      rwa [Formula.close_eq_self_of_closed _ ((Formula.closed_record ψ heads).mpr hclosed)]
        at hcut
  cases hsrc with
  | core_mechanical j x e φ core fresh distinct =>
    exfalso
    have h0 : 0 ∈ S.A := by rw [core]; exact Finset.mem_singleton_self 0
    exact S.zero_not_A h0
  | core_code i φ active outA outE =>
    exact codeRow 0 φ (Or.inl rfl) outA outE rfl rfl
  | subordinate_code i j φ below active outA outE =>
    obtain ⟨i', hi', heq⟩ := S.mem_A.mp active
    have hii : i = i' := by omega
    subst hii
    exact codeRow (j + 1) φ (Or.inr ⟨j, rfl, i, hi', Or.inr (.edge below)⟩) outA outE rfl rfl

end ExtensionStage

end Alexander313
