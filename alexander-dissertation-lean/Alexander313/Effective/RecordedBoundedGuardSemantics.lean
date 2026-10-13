import Alexander313.Effective.RecordedBoundedGuardPrograms

/-!
# Actual ordinal semantics of the bounded guard-room compiler

Below an admitted union-code cut, every ordinal point has a genuine old low
code at that cut's finite level. Thus a displayed ordinal chain can be recoded
without changing its length, order, edges or cut. Conversely every accepted
finite code witness yields the same genuine ordinal chain. The only supplied
algorithm contracts concern the two actual ordinal edge relations.

These are finite proof transformations. They do not construct a Wilken edge
algorithm, prove bounded chain existence or finite reflection, align a whole
source table, or prove recorded-body truth or full source recovery. Uncompiled.
-/

noncomputable section

namespace Alexander313.RecordedBoundedGuardProgram

open RecordedFormula
open Wilken.RelativeTerm.Hereditary
open HereditaryOrdinalFormation (ordinalOrder ordinalOrder_domain Supported)
open HereditaryOrdinalLabels (Label value labelOf labelOf_value label_lt_iff value_injective)

/-- Only admitted original codes are interpreted as inputs to the actual
ordinal edge relation. No semantic claim is imposed on malformed codes. -/
def EdgeCorrect (c : Program) (R : Ordinal.{0} → Ordinal.{0} → Prop) : Prop :=
  ∀ μ ν, unionCheck μ = true → unionCheck ν = true →
    (c.domain (Nat.pair μ ν) ↔ R (unionInterpretation μ) (unionInterpretation ν))

def labelEdge (R : Ordinal.{0} → Ordinal.{0} → Prop) (μ ν : Label) : Prop :=
  R (value μ) (value ν)

private theorem bounded_pairwise_map {α β : Type} (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) (L : List α) (h : L.Pairwise R)
    (convert : ∀ x ∈ L, ∀ y ∈ L, R x y → S (f x) (f y)) :
    (L.map f).Pairwise S := by
  revert h convert
  induction L with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons x L ih =>
    intro h convert
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact convert x List.mem_cons_self y (List.mem_cons_of_mem _ hy) (hx y hy)
    · exact ih ht (fun y hy z hz =>
        convert y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))

private theorem bounded_pairwise_reflect {α β : Type} (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) (L : List α) (h : (L.map f).Pairwise S)
    (convert : ∀ x ∈ L, ∀ y ∈ L, S (f x) (f y) → R x y) :
    L.Pairwise R := by
  revert h convert
  induction L with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons x L ih =>
    intro h convert
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro y hy
      exact convert x List.mem_cons_self y (List.mem_cons_of_mem _ hy)
        (hx _ (List.mem_map.mpr ⟨y, hy, rfl⟩))
    · exact ih ht (fun y hy z hz =>
        convert y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))

theorem code_below_cut (δ : Nat) (hδ : unionCheck δ = true)
    (η : Ordinal.{0}) (hη : η < unionInterpretation δ) :
    ∃ c : Nat, unionCheck c = true ∧ unionInterpretation c = η := by
  have hcut : unionInterpretation δ < finiteBase (δ.unpair.1 + 1) :=
    (lt_nextBase_iff_code δ.unpair.1 _).mpr ⟨δ.unpair.2, hδ, rfl⟩
  obtain ⟨c, hc, hv⟩ := (lt_nextBase_iff_code δ.unpair.1 η).mp (hη.trans hcut)
  exact ⟨Nat.pair δ.unpair.1 c, by simpa only [unionCheck_pair] using hc,
    by simpa only [unionInterpretation_pair] using hv⟩

theorem boundedChain_to_label (c : Program) (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges : EdgeCorrect c R) (δ k ν : Nat)
    (h : letI : LT Nat := Program.orderLT ordinalOrder
      BoundedGuardChain (fun μ η => c.domain (Nat.pair μ η)) δ k ν) :
    BoundedGuardChain (fun μ η : Label => R (value μ) (value η)) (labelOf δ) k (labelOf ν) := by
  letI : LT Nat := Program.orderLT ordinalOrder
  obtain ⟨tail, hl, ho, he, hb⟩ := h
  have checked (μ : Nat) (hμ : μ ∈ ν :: tail) : unionCheck μ = true :=
    ((ordinalOrder_domain μ δ).mp (hb μ hμ)).1
  have hδ : unionCheck δ = true :=
    ((ordinalOrder_domain ν δ).mp (hb ν List.mem_cons_self)).2.1
  refine ⟨tail.map labelOf, by simpa only [List.length_map] using hl, ?_, ?_, ?_⟩
  · apply bounded_pairwise_map (fun μ η => ordinalOrder.domain (Nat.pair μ η))
      (fun μ η : Label => μ < η) labelOf (ν :: tail) ho
    intro μ hμ η hη hm
    apply (label_lt_iff _ _).mpr
    simpa only [labelOf_value μ (checked μ hμ), labelOf_value η (checked η hη)] using
      ((ordinalOrder_domain μ η).mp hm).2.2
  · apply bounded_pairwise_map (fun μ η => c.domain (Nat.pair μ η))
      (fun μ η : Label => R (value μ) (value η)) labelOf (ν :: tail) he
    intro μ hμ η hη hm
    simpa only [labelOf_value μ (checked μ hμ), labelOf_value η (checked η hη)] using
      (edges μ η (checked μ hμ) (checked η hη)).mp hm
  · intro μ hμ
    change μ ∈ (ν :: tail).map labelOf at hμ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hμ
    apply (label_lt_iff _ _).mpr
    simpa only [labelOf_value η (checked η hη), labelOf_value δ hδ] using
      ((ordinalOrder_domain η δ).mp (hb η hη)).2.2

theorem boundedChain_of_label (c : Program) (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges : EdgeCorrect c R) (δ k ν : Nat) (hδ : unionCheck δ = true) (hν : unionCheck ν = true)
    (h : BoundedGuardChain (fun μ η : Label => R (value μ) (value η))
      (labelOf δ) k (labelOf ν)) :
    letI : LT Nat := Program.orderLT ordinalOrder
    BoundedGuardChain (fun μ η => c.domain (Nat.pair μ η)) δ k ν := by
  obtain ⟨tail, hl, ho, he, hb⟩ := h
  have choosePoint (η : Label) (hη : η ∈ tail) :
      ∃ c : Nat, unionCheck c = true ∧ unionInterpretation c = value η := by
    apply code_below_cut δ hδ (value η)
    have hsmall := (label_lt_iff η (labelOf δ)).mp (hb η (List.mem_cons_of_mem _ hη))
    simpa only [labelOf_value δ hδ] using hsmall
  let point : Label → Nat := fun η =>
    if hη : η ∈ tail then Classical.choose (choosePoint η hη) else ν
  have point_spec (η : Label) (hη : η ∈ tail) :
      unionCheck (point η) = true ∧ labelOf (point η) = η := by
    have hs : unionCheck (point η) = true ∧ unionInterpretation (point η) = value η := by
      dsimp only [point]
      rw [dif_pos hη]
      exact Classical.choose_spec (choosePoint η hη)
    exact ⟨hs.1, value_injective (by simpa only [labelOf_value _ hs.1] using hs.2)⟩
  let written := ν :: tail.map point
  have checked (μ : Nat) (hμ : μ ∈ written) : unionCheck μ = true := by
    rcases List.mem_cons.mp hμ with rfl | hμ
    · exact hν
    · obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hμ
      exact (point_spec η hη).1
  have labels : written.map labelOf = labelOf ν :: tail := by
    change labelOf ν :: (tail.map point).map labelOf = _
    rw [List.map_map]
    congr 1
    calc
      tail.map (fun η => labelOf (point η)) = tail.map id :=
        List.map_congr_left (fun η hη => (point_spec η hη).2)
      _ = tail := by simp
  letI : LT Nat := Program.orderLT ordinalOrder
  refine ⟨tail.map point, by simpa only [List.length_map] using hl, ?_, ?_, ?_⟩
  · change written.Pairwise (fun μ η => ordinalOrder.domain (Nat.pair μ η))
    apply bounded_pairwise_reflect _ (fun μ η : Label => μ < η) labelOf written
      (by simpa only [labels] using ho)
    intro μ hμ η hη hm
    apply (ordinalOrder_domain μ η).mpr
    refine ⟨checked μ hμ, checked η hη, ?_⟩
    simpa only [labelOf_value μ (checked μ hμ), labelOf_value η (checked η hη)] using
      (label_lt_iff _ _).mp hm
  · change written.Pairwise (fun μ η => c.domain (Nat.pair μ η))
    apply bounded_pairwise_reflect _ (fun μ η : Label => R (value μ) (value η)) labelOf written
      (by simpa only [labels] using he)
    intro μ hμ η hη hm
    apply (edges μ η (checked μ hμ) (checked η hη)).mpr
    simpa only [labelOf_value μ (checked μ hμ), labelOf_value η (checked η hη)] using hm
  · intro μ hμ
    apply (ordinalOrder_domain μ δ).mpr
    refine ⟨checked μ hμ, hδ, ?_⟩
    have hm : labelOf μ ∈ written.map labelOf := List.mem_map.mpr ⟨μ, hμ, rfl⟩
    rw [labels] at hm
    simpa only [labelOf_value μ (checked μ hμ), labelOf_value δ hδ] using
      (label_lt_iff _ _).mp (hb _ hm)

theorem boundedChain_label_iff (c : Program) (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges : EdgeCorrect c R) (δ k ν : Nat) (hδ : unionCheck δ = true) (hν : unionCheck ν = true) :
    (letI : LT Nat := Program.orderLT ordinalOrder
     BoundedGuardChain (fun μ η => c.domain (Nat.pair μ η)) δ k ν) ↔
      BoundedGuardChain (fun μ η : Label => R (value μ) (value η)) (labelOf δ) k (labelOf ν) :=
  ⟨boundedChain_to_label c R edges δ k ν,
    boundedChain_of_label c R edges δ k ν hδ hν⟩

def labelRequirements (r : GuardRequirements Nat) : GuardRequirements Label :=
  (r.1.map (fun q => (q.1, labelOf q.2)),
    r.2.map (fun q => (labelOf q.1, labelOf q.2)))

def RequirementsSupported (r : GuardRequirements Nat) : Prop :=
  (∀ q ∈ r.1, unionCheck q.2 = true) ∧
    ∀ q ∈ r.2, unionCheck q.1 = true ∧ unionCheck q.2 = true

@[simp] theorem requirementsSupported_append (r s : GuardRequirements Nat) :
    RequirementsSupported (GuardRequirements.append r s) ↔
      RequirementsSupported r ∧ RequirementsSupported s := by
  simp only [RequirementsSupported, GuardRequirements.append, List.mem_append, or_imp, forall_and]
  tauto

@[simp] theorem labelRequirements_append (r s : GuardRequirements Nat) :
    labelRequirements (GuardRequirements.append r s) =
      GuardRequirements.append (labelRequirements r) (labelRequirements s) := by
  simp only [labelRequirements, GuardRequirements.append, List.map_append]

theorem boundedRequirements_to_label (c₁ c₂ : Program)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂)
    (δ : Nat) (r : GuardRequirements Nat)
    (h : letI : LT Nat := Program.orderLT ordinalOrder
      GuardRequirements.Bounded (fun μ ν => c₁.domain (Nat.pair μ ν))
        (fun μ ν => c₂.domain (Nat.pair μ ν)) δ r) :
    GuardRequirements.Bounded (labelEdge R₁) (labelEdge R₂) (labelOf δ) (labelRequirements r) := by
  constructor
  · intro q hq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    exact boundedChain_to_label c₂ R₂ edges₂ δ v.1 v.2 (h.1 v hv)
  · intro q hq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    have hs := (h.2 v hv).1
    have checked := (ordinalOrder_domain v.1 v.2).mp hs
    constructor
    · apply (label_lt_iff _ _).mpr
      simpa only [labelOf_value v.1 checked.1, labelOf_value v.2 checked.2.1] using checked.2.2
    · simpa only [labelEdge, labelOf_value v.1 checked.1, labelOf_value v.2 checked.2.1] using
        (edges₁ v.1 v.2 checked.1 checked.2.1).mp (h.2 v hv).2

theorem boundedRequirements_of_label (c₁ c₂ : Program)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂)
    (δ : Nat) (r : GuardRequirements Nat) (hδ : unionCheck δ = true) (support : RequirementsSupported r)
    (h : GuardRequirements.Bounded (labelEdge R₁) (labelEdge R₂) (labelOf δ) (labelRequirements r)) :
    letI : LT Nat := Program.orderLT ordinalOrder
    GuardRequirements.Bounded (fun μ ν => c₁.domain (Nat.pair μ ν))
      (fun μ ν => c₂.domain (Nat.pair μ ν)) δ r := by
  letI : LT Nat := Program.orderLT ordinalOrder
  constructor
  · intro q hq
    exact boundedChain_of_label c₂ R₂ edges₂ δ q.1 q.2 hδ (support.1 q hq)
      (h.1 _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  · intro q hq
    have hs := h.2 _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    have hc := support.2 q hq
    constructor
    · apply (ordinalOrder_domain q.1 q.2).mpr
      refine ⟨hc.1, hc.2, ?_⟩
      simpa only [labelOf_value q.1 hc.1, labelOf_value q.2 hc.2] using
        (label_lt_iff _ _).mp hs.1
    · apply (edges₁ q.1 q.2 hc.1 hc.2).mpr
      simpa only [labelEdge, labelOf_value q.1 hc.1, labelOf_value q.2 hc.2] using hs.2

theorem indexedRequirements_supported (φ : Syntax) (k : Nat) (support : Supported φ) :
    RequirementsSupported (φ.indexedGuardRequirements k) := by
  revert support
  induction φ generalizing k with
  | falsum => intro _; simp [Formula.indexedGuardRequirements, RequirementsSupported]
  | equal t u => intro _; simp [Formula.indexedGuardRequirements, RequirementsSupported]
  | imp φ ψ ihφ ihψ =>
    intro h
    exact (requirementsSupported_append _ _).mpr
      ⟨ihφ k (fun μ hμ => h μ (Finset.mem_union_left _ hμ)),
        ihψ k (fun μ hμ => h μ (Finset.mem_union_right _ hμ))⟩
  | conj φ ψ ihφ ihψ =>
    intro h
    exact (requirementsSupported_append _ _).mpr
      ⟨ihφ k (fun μ hμ => h μ (Finset.mem_union_left _ hμ)),
        ihψ k (fun μ hμ => h μ (Finset.mem_union_right _ hμ))⟩
  | disj φ ψ ihφ ihψ =>
    intro h
    exact (requirementsSupported_append _ _).mpr
      ⟨ihφ k (fun μ hμ => h μ (Finset.mem_union_left _ hμ)),
        ihψ k (fun μ hμ => h μ (Finset.mem_union_right _ hμ))⟩
  | neg φ ih => intro h; exact ih k h
  | all x φ ih => intro h; exact ih k h
  | ex x φ ih => intro h; exact ih k h
  | know a φ ih =>
    cases a with
    | live a => intro h; exact ih k h
    | ghost a => intro h; exact ih k h
    | indexed a ν =>
      intro h
      have hν := h ν (Finset.mem_insert_self _ _)
      have hφ : Supported φ := fun μ hμ => h μ (Finset.mem_insert_of_mem hμ)
      have hi := ih k hφ
      constructor
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hν
        · exact hi.1 q hq
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hq
          exact ⟨hφ μ ((Formula.mem_labelList_iff φ μ).mp hμ), hν⟩
        · exact hi.2 q hq

theorem mainRequirements_supported (E : Finset Nat) (φ : Syntax) (support : Supported φ) :
    RequirementsSupported (φ.mainGuardRequirements E) := by
  revert support
  induction φ with
  | falsum => intro _; simp [Formula.mainGuardRequirements, RequirementsSupported]
  | equal t u => intro _; simp [Formula.mainGuardRequirements, RequirementsSupported]
  | imp φ ψ ihφ ihψ =>
    intro h
    exact (requirementsSupported_append _ _).mpr
      ⟨ihφ (fun μ hμ => h μ (Finset.mem_union_left _ hμ)),
        ihψ (fun μ hμ => h μ (Finset.mem_union_right _ hμ))⟩
  | conj φ ψ ihφ ihψ =>
    intro h
    exact (requirementsSupported_append _ _).mpr
      ⟨ihφ (fun μ hμ => h μ (Finset.mem_union_left _ hμ)),
        ihψ (fun μ hμ => h μ (Finset.mem_union_right _ hμ))⟩
  | disj φ ψ ihφ ihψ =>
    intro h
    exact (requirementsSupported_append _ _).mpr
      ⟨ihφ (fun μ hμ => h μ (Finset.mem_union_left _ hμ)),
        ihψ (fun μ hμ => h μ (Finset.mem_union_right _ hμ))⟩
  | neg φ ih => intro h; exact ih h
  | all x φ ih => intro h; exact ih h
  | ex x φ ih => intro h; exact ih h
  | know a φ ih =>
    cases a with
    | live e =>
      intro h
      by_cases he : e ∈ E
      · simp only [Formula.mainGuardRequirements, if_pos he]
        exact (requirementsSupported_append _ _).mpr
          ⟨indexedRequirements_supported φ φ.erase.shape.rank h, ih h⟩
      · simpa only [Formula.mainGuardRequirements, if_neg he] using ih h
    | ghost a => intro h; exact ih h
    | indexed a ν =>
      intro h
      exact ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))

@[simp] theorem label_labelList (φ : Syntax) :
    (φ.relabel labelOf).labelList = φ.labelList.map labelOf := by
  induction φ with
  | know a φ ih => cases a <;>
      simp_all [Formula.relabel, Formula.mapOwner, RecordedHead.mapLabel, Formula.labelList]
  | _ => simp_all [Formula.relabel, Formula.mapOwner, Formula.labelList, List.map_append]

theorem label_indexedRequirements (φ : Syntax) (k : Nat) :
    (φ.relabel labelOf).indexedGuardRequirements k =
      labelRequirements (φ.indexedGuardRequirements k) := by
  have labels (ψ : Syntax) :
      (Formula.mapOwner (RecordedHead.mapLabel labelOf) ψ).labelList =
        ψ.labelList.map labelOf := label_labelList ψ
  induction φ with
  | know a φ ih =>
    cases a <;>
      simp_all [Formula.relabel, Formula.mapOwner, RecordedHead.mapLabel,
        Formula.indexedGuardRequirements, labelRequirements, List.map_append, List.map_map,
        label_labelList, labels, Function.comp_def]
  | _ => simp_all [Formula.relabel, Formula.mapOwner, Formula.indexedGuardRequirements,
      labelRequirements_append, labelRequirements, GuardRequirements.append, List.map_append]

theorem label_mainRequirements (E : Finset Nat) (φ : Syntax) :
    (φ.relabel labelOf).mainGuardRequirements E =
      labelRequirements (φ.mainGuardRequirements E) := by
  have erased (ψ : Syntax) :
      (Formula.mapOwner (RecordedHead.mapLabel labelOf) ψ).erase = ψ.erase :=
    Formula.erase_relabel ψ labelOf
  induction φ with
  | know a φ ih =>
    cases a with
    | live e =>
      by_cases he : e ∈ E <;>
        simp [Formula.relabel, Formula.mapOwner, RecordedHead.mapLabel,
          Formula.mainGuardRequirements, he, ← ih, ← label_indexedRequirements,
          labelRequirements_append, Formula.erase_relabel, erased]
    | ghost e => exact ih
    | indexed a ν => exact ih
  | _ => simp_all [Formula.relabel, Formula.mapOwner, Formula.mainGuardRequirements,
      labelRequirements_append, labelRequirements, GuardRequirements.append, List.map_append]

theorem target_label_exact (p : Parameters) (φ : Syntax)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect p.2.1 R₁) (edges₂ : EdgeCorrect p.2.2 R₂) :
    Target p φ ↔ Supported φ ∧ unionCheck p.1.2 = true ∧
      GuardRequirements.Bounded (labelEdge R₁) (labelEdge R₂) (labelOf p.1.2)
        ((φ.relabel labelOf).mainGuardRequirements p.1.1.toFinset) := by
  rw [label_mainRequirements]
  constructor
  · rintro ⟨support, hδ, h⟩
    exact ⟨support, hδ, boundedRequirements_to_label p.2.1 p.2.2 R₁ R₂ edges₁ edges₂ _ _ h⟩
  · rintro ⟨support, hδ, h⟩
    exact ⟨support, hδ, boundedRequirements_of_label p.2.1 p.2.2 R₁ R₂ edges₁ edges₂ _ _ hδ
      (mainRequirements_supported p.1.1.toFinset φ support) h⟩

theorem target_label_room_exact (p : Parameters) (φ : Syntax)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect p.2.1 R₁) (edges₂ : EdgeCorrect p.2.2 R₂) :
    Target p φ ↔ Supported φ ∧ unionCheck p.1.2 = true ∧
      ∃ B : Finset Label, (φ.relabel labelOf).MainGuarded (labelEdge R₁) (labelEdge R₂) p.1.1.toFinset B ∧
        ∀ μ ∈ B, μ < labelOf p.1.2 := by
  rw [target_label_exact p φ R₁ R₂ edges₁ edges₂, Formula.mainGuardRequirements_bounded_iff]

/-- The room bound is the actual original ordinal cut value, through an
injective small ordinal-label carrier rather than a numerical rank. -/
theorem target_room_exact (p : Parameters) (φ : Syntax)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect p.2.1 R₁) (edges₂ : EdgeCorrect p.2.2 R₂) :
    Target p φ ↔ Supported φ ∧ unionCheck p.1.2 = true ∧
      ∃ B : Finset Label, (φ.relabel labelOf).MainGuarded (labelEdge R₁) (labelEdge R₂) p.1.1.toFinset B ∧
        ∀ μ ∈ B, value μ < unionInterpretation p.1.2 := by
  rw [target_label_room_exact p φ R₁ R₂ edges₁ edges₂]
  constructor
  · rintro ⟨support, hδ, B, guard, room⟩
    refine ⟨support, hδ, B, guard, ?_⟩
    intro μ hμ
    simpa only [labelOf_value p.1.2 hδ] using (label_lt_iff _ _).mp (room μ hμ)
  · rintro ⟨support, hδ, B, guard, room⟩
    refine ⟨support, hδ, B, guard, ?_⟩
    intro μ hμ
    apply (label_lt_iff _ _).mpr
    simpa only [labelOf_value p.1.2 hδ] using room μ hμ

/-- The exact original-code domain recognizes actual finite ordinal room.
Both original code-domain guards remain in the semantic theorem. -/
theorem semantic_compiler_exists (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (c₁ c₂ : Program) (edges₁ : EdgeCorrect c₁ R₁) (edges₂ : EdgeCorrect c₂ R₂) :
    ∃ compiler : (List Nat × Nat) → Program, Primrec compiler ∧
      (∀ p φ, (compiler p).domain (φ.code RecordedHead.code) ↔
        Supported φ ∧ unionCheck p.2 = true ∧
          ∃ B : Finset Label, (φ.relabel labelOf).MainGuarded (labelEdge R₁) (labelEdge R₂) p.1.toFinset B ∧
            ∀ μ ∈ B, value μ < unionInterpretation p.2) ∧
      (∀ p query, (compiler p).domain query ↔
        ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ Supported φ ∧ unionCheck p.2 = true ∧
          ∃ B : Finset Label, (φ.relabel labelOf).MainGuarded (labelEdge R₁) (labelEdge R₂) p.1.toFinset B ∧
            ∀ μ ∈ B, value μ < unionInterpretation p.2) := by
  obtain ⟨compiler, hp, typed, raw⟩ := compiler_exists
  refine ⟨fun p => compiler (p, (c₁, c₂)), hp.comp (Primrec.id.pair (Primrec.const (c₁, c₂))), ?_, ?_⟩
  · intro p φ
    exact (typed _ _).trans (target_room_exact _ φ R₁ R₂ edges₁ edges₂)
  · intro p query
    rw [raw]
    exact exists_congr (fun φ => and_congr Iff.rfl (target_room_exact _ φ R₁ R₂ edges₁ edges₂))

theorem target_fresh_markers (p : Parameters) (φ : Syntax)
    (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (edges₁ : EdgeCorrect p.2.1 R₁) (edges₂ : EdgeCorrect p.2.2 R₂)
    (h : Target p φ) (F : Finset (Shape Nat)) :
    ∃ ms : List (Label × Nat), (ms.map Prod.snd).Nodup ∧
      (∀ q ∈ ms, (markerTag Nat q.2).shape ∉ F) ∧
      (φ.relabel labelOf).MainGuarded (labelEdge R₁) (labelEdge R₂) p.1.1.toFinset (markerPoints ms) ∧
        ∀ q ∈ ms, value q.1 < unionInterpretation p.1.2 := by
  have bounded := ((target_label_exact p φ R₁ R₂ edges₁ edges₂).mp h).2.2
  obtain ⟨ms, nodup, fresh, guard, room⟩ := Formula.bounded_main_markers
    (labelEdge R₁) (labelEdge R₂) p.1.1.toFinset (labelOf p.1.2) (φ.relabel labelOf) F bounded
  refine ⟨ms, nodup, fresh, guard, ?_⟩
  intro q hq
  simpa only [labelOf_value p.1.2 h.2.1] using (label_lt_iff _ _).mp (room q hq)

end Alexander313.RecordedBoundedGuardProgram
