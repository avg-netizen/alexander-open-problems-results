import Alexander313.RecordedCoherentCollapse
import Alexander313.RecordedFiniteLiftPlans
import Alexander313.RecordedFiniteTables

/-!
# Guarded fixed-label transport (note 24 §5, equation (4))

Let `top` carry a rank-(k+1) guard, and let a recorded lift of a source formula
β of rank at most k+1 have its whole support strictly and ≤₁-below `top`, with
every external argument of β kept live. Then every source theorem β^s of an
active holder is already provable in that holder's actual stage cut below
`top`, at the prescribed labels.

The proof is the one in the note. A finite source certificate is chosen. The
room clause of the ordinal package supplies separated rank-k guard copies
below `top`, above the goal support. The canonical depth table puts every
active head over an argument of depth d at the first point of copy d. Then
every premise has its literal finite lift data: nesting from depth, reasoning
links from the coherent chain, and the guards of every main premise from the
copies strictly below its first own-prefix label. The existing certificate
compiler lifts the certificate, and the coherent-collapse lemma moves the
canonical conclusion to the prescribed labels.

The forward direction is erasure. Transport and exact recovery at the room
copies of one guarded top are corollaries; they replace the infinite chain of
the earlier hand proof. These declarations belong to the checked completion chain.
-/

namespace Alexander313

namespace Formula

@[simp] theorem queries_all_foldr {Owner : Type} [DecidableEq Owner] (xs : List Nat)
    (φ : Formula Owner) : (xs.foldr Formula.all φ).queries = φ.queries := by
  induction xs <;> simp_all [queries]

@[simp] theorem queries_universalClosure {Owner : Type} [DecidableEq Owner]
    (φ : Formula Owner) : φ.universalClosure.queries = φ.queries :=
  queries_all_foldr _ φ

theorem activeDepth_prefix (A : Finset Nat) (a : Nat) (ha : a ∈ A) (σ : Formula Nat) :
    ∀ n, (Formula.«prefix» a n σ).shape.activeDepth A = n + σ.shape.activeDepth A := by
  intro n
  induction n with
  | zero => simp [Formula.«prefix»]
  | succ n ih =>
    simp only [Formula.«prefix», shape, Shape.activeDepth, ha, ↓reduceIte, ih]
    omega

@[simp] theorem erase_close {Label : Type} (φ : Formula (RecordedHead Nat Label))
    (s : Assignment) : (φ.close s).erase = φ.erase.close s :=
  mapOwner_close φ _ s

theorem codeSentence_atom_queries (A : ArithmeticCoding Nat) (j : Nat)
    (φ : UnaryFormula Nat) (e : Nat) :
    (Formula.know j φ.body).queries ⊆ (codeSentence A j φ e).queries := by
  intro q hq
  simp only [codeSentence, Formula.iff, queries, Finset.mem_union]
  tauto

theorem mainHeads_not_indexed {Label : Type} (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a : Nat) (sh : Shape Nat) (ha : a ∉ A) (b : Nat) (ν : Label) :
    mainHeads A E H labels a sh ≠ .indexed b ν := by
  by_cases he : a ∈ E
  · by_cases hh : (a, sh) ∈ H <;> simp [mainHeads, maskedHeads, he, hh]
  · simp [mainHeads, maskedHeads, he, ha]

variable {Label : Type} [LinearOrder Label]

/-- Indexed guards from query-level data, for any shape table. -/
theorem indexedGuarded_of_queries (R₁ R₂ : Label → Label → Prop) (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (disjoint : Disjoint A E) (B : Finset Label) (k : Nat) (χ : Formula Nat)
    (hyp : ∀ b sh, (b, sh) ∈ χ.queries → b ∈ A →
      GuardChainIn R₂ B k (labels b sh) ∧
        ∀ b' sh', (b', sh') ∈ sh.queries → b' ∈ A →
          labels b' sh' < labels b sh ∧ R₁ (labels b' sh') (labels b sh)) :
    (χ.record (mainHeads A E H labels)).IndexedGuarded R₁ R₂ B k := by
  induction χ with
  | falsum => trivial
  | equal t u => trivial
  | imp φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun b sh h hb => hyp b sh (Finset.mem_union_left _ h) hb),
      ihψ (fun b sh h hb => hyp b sh (Finset.mem_union_right _ h) hb)⟩
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun b sh h hb => hyp b sh (Finset.mem_union_left _ h) hb),
      ihψ (fun b sh h hb => hyp b sh (Finset.mem_union_right _ h) hb)⟩
  | disj φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun b sh h hb => hyp b sh (Finset.mem_union_left _ h) hb),
      ihψ (fun b sh h hb => hyp b sh (Finset.mem_union_right _ h) hb)⟩
  | neg φ ih => exact ih hyp
  | all x φ ih => exact ih hyp
  | ex x φ ih => exact ih hyp
  | know a ψ ih =>
    have inner := ih (fun b sh h hb => hyp b sh (Finset.mem_insert_of_mem h) hb)
    by_cases ha : a ∈ A
    · have own := mainHeads_active A E H labels a ψ.shape ha disjoint
      obtain ⟨chain, edges⟩ := hyp a ψ.shape (Finset.mem_insert_self _ _) ha
      simp only [record, own, IndexedGuarded]
      refine ⟨chain, ?_, inner⟩
      intro μ hμ
      obtain ⟨b', sh', hq, hb', rfl⟩ :=
        record_support_source_query A E H labels disjoint ψ μ hμ
      exact edges b' sh' (by simpa only [queries_shape] using hq) hb'
    · simp only [record]
      cases hh : mainHeads A E H labels a ψ.shape with
      | live b => exact inner
      | ghost b => exact inner
      | indexed b ν => exact absurd hh (mainHeads_not_indexed A E H labels a ψ.shape ha b ν)

/-- Main guards from query-level data below every live external argument. -/
theorem mainGuarded_of_queries (R₁ R₂ : Label → Label → Prop) (A E : Finset Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (disjoint : Disjoint A E) (B : Finset Label) (φ : Formula Nat)
    (hyp : ∀ e shχ, (e, shχ) ∈ φ.queries → e ∈ E → (e, shχ) ∈ H →
      ∀ b sh, (b, sh) ∈ shχ.queries → b ∈ A →
        GuardChainIn R₂ B shχ.rank (labels b sh) ∧
          ∀ b' sh', (b', sh') ∈ sh.queries → b' ∈ A →
            labels b' sh' < labels b sh ∧ R₁ (labels b' sh') (labels b sh)) :
    (φ.record (mainHeads A E H labels)).MainGuarded R₁ R₂ E B := by
  induction φ with
  | falsum => trivial
  | equal t u => trivial
  | imp φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun e sh h he hH => hyp e sh (Finset.mem_union_left _ h) he hH),
      ihψ (fun e sh h he hH => hyp e sh (Finset.mem_union_right _ h) he hH)⟩
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun e sh h he hH => hyp e sh (Finset.mem_union_left _ h) he hH),
      ihψ (fun e sh h he hH => hyp e sh (Finset.mem_union_right _ h) he hH)⟩
  | disj φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun e sh h he hH => hyp e sh (Finset.mem_union_left _ h) he hH),
      ihψ (fun e sh h he hH => hyp e sh (Finset.mem_union_right _ h) he hH)⟩
  | neg φ ih => exact ih hyp
  | all x φ ih => exact ih hyp
  | ex x φ ih => exact ih hyp
  | know a ψ ih =>
    have inner := ih (fun e sh h he hH => hyp e sh (Finset.mem_insert_of_mem h) he hH)
    by_cases he : a ∈ E
    · by_cases hH : (a, ψ.shape) ∈ H
      · have hlive : mainHeads A E H labels a ψ.shape = .live a := by
          simp only [mainHeads, maskedHeads, he, hH, ↓reduceIte]
        simp only [record, hlive, MainGuarded]
        refine ⟨fun _ => ?_, inner⟩
        have hrank : (ψ.record (mainHeads A E H labels)).erase.shape.rank = ψ.shape.rank := by
          rw [erase_record ψ _ (mainHeads_erase A E H labels)]
        rw [hrank]
        apply indexedGuarded_of_queries R₁ R₂ A E H labels disjoint B ψ.shape.rank ψ
        intro b sh hq hb
        exact hyp a ψ.shape (Finset.mem_insert_self _ _) he hH b sh
          (by simpa only [queries_shape] using hq) hb
      · have hghost : mainHeads A E H labels a ψ.shape = .ghost a := by
          simp only [mainHeads, maskedHeads, he, hH, ↓reduceIte]
        simp only [record, hghost, MainGuarded]
        exact inner
    · simp only [record]
      cases hh : mainHeads A E H labels a ψ.shape with
      | live b =>
        have hb : b = a := by
          simpa only [hh, RecordedHead.erase] using mainHeads_erase A E H labels a ψ.shape
        subst hb
        exact ⟨fun h => absurd h he, inner⟩
      | ghost b => exact inner
      | indexed b ν => exact inner

end Formula

/-- The side conditions of an extension presentation (note 24 §1): the core
and every subordinate code target are outside the active and external sets. -/
structure ExtensionSides (R : Nat → Nat → Prop) (A E : Finset Nat) : Prop where
  disjoint : Disjoint A E
  core_active : 0 ∉ A
  core_external : 0 ∉ E
  codes : ∀ i j, i + 1 ∈ A → R j i → j + 1 ∉ A ∧ j + 1 ∉ E

namespace RecordedStage

variable (P : OrdinalPackage) {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat)

/-- Room copies, their first points and the facts used below. -/
structure RoomCopies (top : P.Label) (k N : Nat) (X : Finset P.Label) where
  copy : Nat → List P.Label
  shape : ∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
    (copy j).Pairwise P.R₂
  points : ∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ P.R₁ y top
  separated : ∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z

namespace RoomCopies

variable {P} {top : P.Label} {k N : Nat} {X : Finset P.Label}

noncomputable def ofRoom (guard : GuardHead P.R₂ (k + 1) top)
    (hX : ∀ x ∈ X, x < top ∧ P.R₁ x top) (N : Nat) : RoomCopies P top k N X := by
  let h := P.room k top guard X hX N
  exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2.1,
    (Classical.choose_spec h).2.2⟩

def first (Y : RoomCopies P top k N X) (d : Nat) : P.Label := (Y.copy d).headD top

theorem copy_eq (Y : RoomCopies P top k N X) {d : Nat} (hd : d < N) :
    Y.copy d = Y.first d :: (Y.copy d).tail := by
  have hl := (Y.shape d hd).1
  unfold first
  cases h : Y.copy d with
  | nil => rw [h] at hl; simp at hl
  | cons y ys => rfl

theorem first_mem (Y : RoomCopies P top k N X) {d : Nat} (hd : d < N) :
    Y.first d ∈ Y.copy d := by
  rw [Y.copy_eq hd]
  exact List.mem_cons_self

theorem first_lt (Y : RoomCopies P top k N X) {d₁ d₂ : Nat} (h : d₁ < d₂) (hd : d₂ < N) :
    Y.first d₁ < Y.first d₂ :=
  Y.separated d₁ d₂ h hd _ (Y.first_mem (lt_trans h hd)) _ (Y.first_mem hd)

theorem first_coherent (Y : RoomCopies P top k N X) {d : Nat} (hd : d < N) :
    Y.first d ∈ P.CoherentBelow top :=
  ⟨(Y.points d hd _ (Y.first_mem hd)).2.1, (Y.points d hd _ (Y.first_mem hd)).2.2⟩

theorem first_R₁ (Y : RoomCopies P top k N X) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) (hd : d₂ < N) :
    P.R₁ (Y.first d₁) (Y.first d₂) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact P.coherentBelow_R₁ top (Y.first_coherent (lt_trans h hd))
      (Y.first_coherent hd) (le_of_lt (Y.first_lt h hd))
  · exact P.R₁_refl _

/-- The points of all copies below depth `D`. -/
noncomputable def pointsBelow (Y : RoomCopies P top k N X) (D : Nat) : Finset P.Label :=
  ((List.range D).flatMap Y.copy).toFinset

theorem mem_pointsBelow (Y : RoomCopies P top k N X) {D d : Nat} (hd : d < D)
    {y : P.Label} (hy : y ∈ Y.copy d) : y ∈ Y.pointsBelow D := by
  simp only [pointsBelow, List.mem_toFinset, List.mem_flatMap, List.mem_range]
  exact ⟨d, hd, hy⟩

theorem pointsBelow_lt (Y : RoomCopies P top k N X) {D : Nat} (hD : D < N) :
    ∀ y ∈ Y.pointsBelow D, y < Y.first D := by
  intro y hy
  simp only [pointsBelow, List.mem_toFinset, List.mem_flatMap, List.mem_range] at hy
  obtain ⟨d, hd, hy⟩ := hy
  exact Y.separated d D hd hD y hy _ (Y.first_mem hD)

theorem pointsBelow_top (Y : RoomCopies P top k N X) {D : Nat} (hD : D ≤ N) :
    ∀ y ∈ Y.pointsBelow D, y < top := by
  intro y hy
  simp only [pointsBelow, List.mem_toFinset, List.mem_flatMap, List.mem_range] at hy
  obtain ⟨d, hd, hy⟩ := hy
  exact (Y.points d (lt_of_lt_of_le hd hD) y hy).2.1

/-- A guard chain of every rank r ≤ k at the first point of copy d. -/
theorem guard (Y : RoomCopies P top k N X) {D d r : Nat} (hd : d < D) (hD : D ≤ N)
    (hr : r ≤ k) : GuardChainIn P.R₂ (Y.pointsBelow D) r (Y.first d) := by
  have hdN : d < N := lt_of_lt_of_le hd hD
  obtain ⟨hl, ho, hR⟩ := Y.shape d hdN
  have heq := Y.copy_eq hdN
  refine ⟨(Y.copy d).tail.take r, ?_, ?_, ?_, ?_⟩
  · have htl : (Y.copy d).tail.length = k := by
      rw [List.length_tail, hl]; rfl
    rw [List.length_take, htl]
    exact min_eq_left hr
  · have hsub : (Y.first d :: (Y.copy d).tail.take r).Sublist (Y.copy d) := by
      conv_rhs => rw [heq]
      exact List.Sublist.cons_cons _ (List.take_sublist r _)
    exact ho.sublist hsub
  · have hsub : (Y.first d :: (Y.copy d).tail.take r).Sublist (Y.copy d) := by
      conv_rhs => rw [heq]
      exact List.Sublist.cons_cons _ (List.take_sublist r _)
    exact hR.sublist hsub
  · intro μ hμ
    apply Y.mem_pointsBelow hd
    rcases List.mem_cons.mp hμ with rfl | hμ
    · exact Y.first_mem hdN
    · rw [heq]
      exact List.mem_cons_of_mem _ (List.mem_of_mem_take hμ)

end RoomCopies

/-- Equation (4), reverse direction: every source theorem of an active holder
is provable at the prescribed guarded labels below the guard base. -/
theorem fixed_label_transport (sides : ExtensionSides R A E) (a : Nat) (ha : a ∈ A)
    (top : P.Label) (k : Nat) (guardTop : GuardHead P.R₂ (k + 1) top)
    (labt : Nat → Shape Nat → P.Label) (β : Formula Nat)
    (hrank : β.shape.rank ≤ k + 1)
    (adm : (β.record (mainHeads A E β.queries labt)).RecordedAdmissible A E)
    (supp : ∀ μ ∈ (β.record (mainHeads A E β.queries labt)).labelSupport,
      μ < top ∧ P.R₁ μ top)
    (s : Assignment) (hsrc : C.family.effective.proves a (β.close s)) :
    cuts C A E P.R₁ P.R₂ a top ((β.record (mainHeads A E β.queries labt)).close s) := by
  classical
  have closed : (β.close s).Closed := β.close_closed s
  obtain ⟨c⟩ := (C.proofs a (β.close s) closed).mp hsrc
  -- the finite depth budget of the whole certificate
  let S := (c.premises.map (fun θ => θ.shape.activeDepth A)).sum
  let N := S + β.shape.activeDepth A + 1
  have sumBound : ∀ (xs : List Nat) (x : Nat), x ∈ xs → x ≤ xs.sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons y ys ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · have hy := ih x hx
        simp only [List.sum_cons]
        omega
  have premiseDepth : ∀ θ ∈ c.premises, θ.shape.activeDepth A < N := by
    intro θ hθ
    have hle : θ.shape.activeDepth A ≤ S :=
      sumBound _ _ (List.mem_map.mpr ⟨θ, hθ, rfl⟩)
    omega
  have targetDepth : β.shape.activeDepth A < N := by omega
  let X := (β.record (mainHeads A E β.queries labt)).labelSupport
  let Y := RoomCopies.ofRoom guardTop (X := X) (fun x hx => supp x hx) N
  let labs := depthLabels A Y.first
  have mono : ∀ d₁ d₂, d₁ < d₂ → d₂ < N → Y.first d₁ < Y.first d₂ :=
    fun d₁ d₂ h hd => Y.first_lt h hd
  -- the canonical lift is provable below `top`
  have canonical : cuts C A E P.R₁ P.R₂ a top
      ((β.close s).record (mainHeads A E β.queries labs)) := by
    apply certificate_cuts_of_requirements C A E P.R₁ P.R₂ a top β.queries labs ha
      (target_queries_hereditary β) sides.disjoint closed c
    intro θ hθ
    obtain ⟨σ, n, hgen, rfl⟩ := c.admitted θ hθ
    have hθN := premiseDepth _ hθ
    have depthθ := Formula.activeDepth_prefix A a ha σ n
    have hσN : σ.shape.activeDepth A < N := by omega
    refine ⟨σ, n, rfl, ?_, ?_, ?_⟩
    · -- room requirements of the generator
      have cutBound : ∀ y ∈ Y.pointsBelow (σ.shape.activeDepth A),
          y < sourceBaseCut a σ labs n top := by
        intro y hy
        cases n with
        | zero => exact Y.pointsBelow_top (le_of_lt hσN) y hy
        | succ n => exact Y.pointsBelow_lt hσN y hy
      have guardData (atom : Formula Nat) (hatom : atom.queries ⊆ σ.queries) :
          GuardRequirements.Bounded P.R₁ P.R₂ (sourceBaseCut a σ labs n top)
            ((atom.record (mainHeads A E β.queries labs)).mainGuardRequirements E) := by
        apply (Formula.mainGuardRequirements_bounded_iff P.R₁ P.R₂ E _ _).mpr
        refine ⟨Y.pointsBelow (σ.shape.activeDepth A), ?_, cutBound⟩
        apply Formula.mainGuarded_of_queries P.R₁ P.R₂ A E β.queries labs sides.disjoint
        intro e shχ hq he hH b sh hb hbA
        have hσq : (b, sh) ∈ σ.queries :=
          Formula.queries_hereditary σ e shχ (hatom hq) hb
        have hdepth : sh.activeDepth A < σ.shape.activeDepth A :=
          (Shape.activeDepth_query A σ.shape b sh (by simpa only [Formula.queries_shape]
            using hσq)).2 hbA
        have hr : shχ.rank ≤ k := by
          have := Shape.rank_query β.shape e shχ (by simpa only [Formula.queries_shape] using hH)
          omega
        refine ⟨Y.guard hdepth (le_of_lt hσN) hr, ?_⟩
        intro b' sh' hq' hb'
        have hd' : sh'.activeDepth A < sh.activeDepth A :=
          (Shape.activeDepth_query A sh b' sh' hq').2 hb'
        exact ⟨mono _ _ hd' (by omega), Y.first_R₁ (le_of_lt hd') (by omega)⟩
      cases hgen with
      | background i h =>
        refine .background h ?_
        intro φ ψ hσ
        subst hσ
        have hq : (a, (Formula.imp φ ψ).shape) ∈
            (Formula.universalClosure (.imp (.know a (.imp φ ψ))
              (.imp (.know a φ) (.know a ψ)))).queries := by
          simp [Formula.queries]
        have hlt := (Shape.activeDepth_query A
          (Formula.universalClosure (.imp (.know a (.imp φ ψ))
            (.imp (.know a φ) (.know a ψ)))).shape a (Formula.imp φ ψ).shape (by
          simpa only [Formula.queries_shape] using hq)).2 ha
        have hN : (Formula.imp φ ψ).shape.activeDepth A < N := lt_trans hlt hσN
        constructor
        · exact Y.first_R₁ (by simp [Formula.shape, Shape.activeDepth]) hN
        · exact Y.first_R₁ (by simp [Formula.shape, Shape.activeDepth]) hN
      | core_mechanical j x e φ fresh distinct =>
        exact absurd ha sides.core_active
      | core_code i φ =>
        exact .main (.know 0 φ.body)
          (.core_code i φ ha sides.core_active sides.core_external)
          (guardData _ (Formula.codeSentence_atom_queries _ _ _ _))
      | subordinate_code i j below φ =>
        have side := sides.codes i j ha below
        exact .main (.know (j + 1) φ.body)
          (.subordinate_code i j φ below ha side.1 side.2)
          (guardData _ (Formula.codeSentence_atom_queries _ _ _ _))
    · exact Shape.labelNesting_depth A Y.first N mono _ (le_of_lt hθN)
    · apply Shape.labelBounds_depth A Y.first top
      intro d hd
      exact (Y.first_coherent (lt_trans hd hθN)).1
  rw [Formula.record_close] at canonical
  -- move the canonical labels to the prescribed ones
  have collapse := cuts_record_coherent C A E P.R₁ P.R₂ a top sides.disjoint β.queries
    labs labt β (P.CoherentBelow top)
    (fun x hx y hy hxy => P.coherentBelow_R₁ top hx hy hxy)
    (by
      intro μ hμ
      obtain ⟨d, hd, rfl⟩ := Formula.record_depth_support A E β.queries Y.first
        sides.disjoint β μ hμ
      exact Y.first_coherent (lt_trans hd targetDepth))
    (fun μ hμ => supp μ hμ)
    (Formula.record_depth_admissible A E β.queries Y.first sides.disjoint N mono β
      (le_of_lt targetDepth))
    adm
    (by
      intro μ hμ
      obtain ⟨d, hd, rfl⟩ := Formula.record_depth_support A E β.queries Y.first
        sides.disjoint β μ hμ
      exact (Y.first_coherent (lt_trans hd targetDepth)).1)
    (fun μ hμ => (supp μ hμ).1) s
  exact collapse.mp canonical

/-- The same transport with an arbitrary hereditary mask containing every
external argument of β. -/
theorem fixed_label_transport_mask (sides : ExtensionSides R A E) (a : Nat) (ha : a ∈ A)
    (top : P.Label) (k : Nat) (guardTop : GuardHead P.R₂ (k + 1) top)
    (H : Finset (Nat × Shape Nat)) (labt : Nat → Shape Nat → P.Label) (β : Formula Nat)
    (hH : ∀ e sh, (e, sh) ∈ β.queries → e ∈ E → (e, sh) ∈ H)
    (hrank : β.shape.rank ≤ k + 1)
    (adm : (β.record (mainHeads A E H labt)).RecordedAdmissible A E)
    (supp : ∀ μ ∈ (β.record (mainHeads A E H labt)).labelSupport, μ < top ∧ P.R₁ μ top)
    (s : Assignment) (hsrc : C.family.effective.proves a (β.close s)) :
    cuts C A E P.R₁ P.R₂ a top ((β.record (mainHeads A E H labt)).close s) := by
  have hrec : β.record (mainHeads A E H labt) = β.record (mainHeads A E β.queries labt) := by
    apply Formula.record_congr_on_queries
    intro b sh hq
    by_cases he : b ∈ E
    · simp only [mainHeads, maskedHeads, he, ↓reduceIte, hH b sh hq he, hq]
    · simp only [mainHeads, maskedHeads, he, ↓reduceIte]
  rw [hrec] at adm supp ⊢
  exact fixed_label_transport P C A E sides a ha top k guardTop labt β hrank adm supp s hsrc

/-- A guarded top of rank k+1 together with N separated room copies below it,
above the empty goal support. Its copy heads label the lifts used in recovery. -/
structure GuardedRoom (k N : Nat) where
  top : P.Label
  guard : GuardHead P.R₂ (k + 1) top
  copies : RoomCopies P top k N ∅

/-- One guarded room for every rank and every number of copies, from `tall`
and `room`. -/
noncomputable def guardedRoom (k N : Nat) : GuardedRoom P k N := by
  let h := P.tall (k + 1)
  exact ⟨Classical.choose h, Classical.choose_spec h,
    RoomCopies.ofRoom (Classical.choose_spec h)
      (fun x hx => absurd hx (Finset.notMem_empty x)) N⟩

namespace GuardedRoom

variable {P} {k N : Nat}

theorem first_mono (Y : GuardedRoom P k N) :
    ∀ d₁ d₂, d₁ < d₂ → d₂ < N → Y.copies.first d₁ < Y.copies.first d₂ :=
  fun _ _ h hd => Y.copies.first_lt h hd

end GuardedRoom

/-- Transport at a guarded top, for lifts labelled by its room copies. -/
theorem room_transport (sides : ExtensionSides R A E) (a : Nat) (ha : a ∈ A)
    {k N : Nat} (Y : GuardedRoom P k N)
    (H : Finset (Nat × Shape Nat)) (labt : Nat → Shape Nat → P.Label) (β : Formula Nat)
    (hH : ∀ e sh, (e, sh) ∈ β.queries → e ∈ E → (e, sh) ∈ H)
    (hrank : β.shape.rank ≤ k + 1)
    (onRoom : ∀ μ ∈ (β.record (mainHeads A E H labt)).labelSupport,
      ∃ d < N, μ = Y.copies.first d)
    (adm : (β.record (mainHeads A E H labt)).RecordedAdmissible A E)
    (s : Assignment) (hsrc : C.family.effective.proves a (β.close s)) :
    cuts C A E P.R₁ P.R₂ a Y.top ((β.record (mainHeads A E H labt)).close s) := by
  apply fixed_label_transport_mask P C A E sides a ha Y.top k Y.guard H labt β hH hrank
    adm _ s hsrc
  intro μ hμ
  obtain ⟨d, hd, rfl⟩ := onRoom μ hμ
  exact Y.copies.first_coherent hd

/-- Exact recovery of an active test at a room-copy label: the stage cut at the
label decides exactly the original source theorems of that skeleton. -/
theorem room_recovery (sides : ExtensionSides R A E) (a : Nat) (ha : a ∈ A)
    {k N : Nat} (Y : GuardedRoom P k N)
    (H : Finset (Nat × Shape Nat)) (labt : Nat → Shape Nat → P.Label) (β : Formula Nat)
    (hH : ∀ e sh, (e, sh) ∈ β.queries → e ∈ E → (e, sh) ∈ H)
    (hrank : β.shape.rank ≤ k + 1) (i : Nat) (hi : i < N)
    (onRoom : ∀ μ ∈ (β.record (mainHeads A E H labt)).labelSupport,
      ∃ d < i, μ = Y.copies.first d)
    (adm : (β.record (mainHeads A E H labt)).RecordedAdmissible A E) (s : Assignment) :
    cuts C A E P.R₁ P.R₂ a (Y.copies.first i) ((β.record (mainHeads A E H labt)).close s) ↔
      C.family.effective.proves a (β.close s) := by
  constructor
  · intro h
    have erased := cuts_erasure C A E P.R₁ P.R₂ a _ h
    simpa only [Formula.erase_close, Formula.erase_record _ _ (mainHeads_erase A E H labt)]
      using erased
  · intro hsrc
    have high := room_transport P C A E sides a ha Y H labt β hH hrank
      (fun μ hμ => by
        obtain ⟨d, hd, rfl⟩ := onRoom μ hμ
        exact ⟨d, lt_trans hd hi, rfl⟩) adm s hsrc
    have hcoh := Y.copies.first_coherent hi
    refine (cuts_collapse C A E P.R₁ P.R₂ a (le_of_lt hcoh.1)
      (P.reflection _ _ hcoh.2) _ ?_).mpr high
    intro μ hμ
    rw [Formula.labelSupport_close] at hμ
    obtain ⟨d, hd, rfl⟩ := onRoom μ hμ
    exact Y.copies.first_lt hd hi

end RecordedStage

end Alexander313
