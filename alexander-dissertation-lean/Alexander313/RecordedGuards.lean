import Alexander313.RecordedBackground

/-!
# Literal finite guards on the whole distinguished modal atom

A rank-k guard has k+1 actual points, beginning at its indexed label.
Every point is retained in the finite marker set. Inspection traverses all
heads and inspects a live external outer head as well as nested live heads,
including those underneath ghosts. Erasure supplies only the shape rank;
it is never used as a recorded-validity admission test.
-/

namespace Alexander313

private theorem pairwise_map_on {α β : Type} (P : α → α → Prop) (Q : β → β → Prop)
    (f : α → β) (xs : List α) (h : xs.Pairwise P)
    (convert : ∀ x ∈ xs, ∀ y ∈ xs, P x y → Q (f x) (f y)) :
    (xs.map f).Pairwise Q := by
  revert h convert
  induction xs with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons x xs ih =>
    intro h convert
    have hc := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact convert x List.mem_cons_self y (List.mem_cons_of_mem _ hy) (hc.1 y hy)
    · exact ih hc.2 (fun y hy z hz =>
        convert y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))

def GuardChainIn {Label : Type} [LT Label] [DecidableEq Label]
    (R₂ : Label → Label → Prop) (B : Finset Label) (k : Nat) (ν : Label) : Prop :=
  ∃ tail : List Label, tail.length = k ∧
    (ν :: tail).Pairwise (· < ·) ∧ (ν :: tail).Pairwise R₂ ∧
    ∀ μ ∈ ν :: tail, μ ∈ B

theorem GuardChainIn.base_mem {Label : Type} [LT Label] [DecidableEq Label]
    {R₂ : Label → Label → Prop} {B : Finset Label} {k : Nat} {ν : Label}
    (h : GuardChainIn R₂ B k ν) : ν ∈ B := by
  obtain ⟨tail, _, _, _, hb⟩ := h
  exact hb ν List.mem_cons_self

theorem GuardChainIn.relabel {Label : Type} [LinearOrder Label]
    {R₁ R₂ : Label → Label → Prop} {B F : Finset Label} {k : Nat} {ν : Label}
    (h : GuardChainIn R₂ B k ν) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f) (support : B ⊆ F) :
    GuardChainIn R₂ (B.image f) k (f ν) := by
  obtain ⟨tail, hl, ho, hr, hb⟩ := h
  refine ⟨tail.map f, by simpa only [List.length_map] using hl, ?_, ?_, ?_⟩
  · exact pairwise_map_on (· < ·) (· < ·) f (ν :: tail) ho
      (fun x hx y hy => (pattern.2.1 x (support (hb x hx)) y (support (hb y hy))).mpr)
  · exact pairwise_map_on R₂ R₂ f (ν :: tail) hr
      (fun x hx y hy => pattern.2.2.2 x (support (hb x hx)) y (support (hb y hy)))
  · intro μ hμ
    change μ ∈ (ν :: tail).map f at hμ
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hμ
    exact Finset.mem_image.mpr ⟨η, hb η hη, rfl⟩

namespace Formula

def IndexedGuarded {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (B : Finset Label) (k : Nat) :
    Formula (RecordedHead Nat Label) → Prop
  | .falsum => True
  | .equal _ _ => True
  | .imp φ ψ => φ.IndexedGuarded R₁ R₂ B k ∧ ψ.IndexedGuarded R₁ R₂ B k
  | .conj φ ψ => φ.IndexedGuarded R₁ R₂ B k ∧ ψ.IndexedGuarded R₁ R₂ B k
  | .disj φ ψ => φ.IndexedGuarded R₁ R₂ B k ∧ ψ.IndexedGuarded R₁ R₂ B k
  | .neg φ => φ.IndexedGuarded R₁ R₂ B k
  | .all _ φ => φ.IndexedGuarded R₁ R₂ B k
  | .ex _ φ => φ.IndexedGuarded R₁ R₂ B k
  | .know (.live _) φ => φ.IndexedGuarded R₁ R₂ B k
  | .know (.ghost _) φ => φ.IndexedGuarded R₁ R₂ B k
  | .know (.indexed _ ν) φ => GuardChainIn R₂ B k ν ∧
      (∀ μ ∈ φ.labelSupport, μ < ν ∧ R₁ μ ν) ∧ φ.IndexedGuarded R₁ R₂ B k

def MainGuarded {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (E : Finset Nat) (B : Finset Label) :
    Formula (RecordedHead Nat Label) → Prop
  | .falsum => True
  | .equal _ _ => True
  | .imp φ ψ => φ.MainGuarded R₁ R₂ E B ∧ ψ.MainGuarded R₁ R₂ E B
  | .conj φ ψ => φ.MainGuarded R₁ R₂ E B ∧ ψ.MainGuarded R₁ R₂ E B
  | .disj φ ψ => φ.MainGuarded R₁ R₂ E B ∧ ψ.MainGuarded R₁ R₂ E B
  | .neg φ => φ.MainGuarded R₁ R₂ E B
  | .all _ φ => φ.MainGuarded R₁ R₂ E B
  | .ex _ φ => φ.MainGuarded R₁ R₂ E B
  | .know (.indexed _ _) φ => φ.MainGuarded R₁ R₂ E B
  | .know (.ghost _) φ => φ.MainGuarded R₁ R₂ E B
  | .know (.live e) φ =>
      (e ∈ E → φ.IndexedGuarded R₁ R₂ B φ.erase.shape.rank) ∧ φ.MainGuarded R₁ R₂ E B

theorem indexedGuarded_relabel {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) (B F : Finset Label) (k : Nat)
    (φ : Formula (RecordedHead Nat Label)) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f) (points : B ⊆ F)
    (support : φ.labelSupport ⊆ F) (h : φ.IndexedGuarded R₁ R₂ B k) :
    (φ.relabel f).IndexedGuarded R₁ R₂ (B.image f) k := by
  revert support
  revert h
  induction φ with
  | falsum => intro _ _; trivial
  | equal t u => intro _ _; trivial
  | imp φ ψ ihφ ihψ =>
    intro h support
    exact ⟨ihφ h.1 (fun μ hμ => support (Finset.mem_union_left _ hμ)),
      ihψ h.2 (fun μ hμ => support (Finset.mem_union_right _ hμ))⟩
  | conj φ ψ ihφ ihψ =>
    intro h support
    exact ⟨ihφ h.1 (fun μ hμ => support (Finset.mem_union_left _ hμ)),
      ihψ h.2 (fun μ hμ => support (Finset.mem_union_right _ hμ))⟩
  | disj φ ψ ihφ ihψ =>
    intro h support
    exact ⟨ihφ h.1 (fun μ hμ => support (Finset.mem_union_left _ hμ)),
      ihψ h.2 (fun μ hμ => support (Finset.mem_union_right _ hμ))⟩
  | neg φ ih => intro h support; exact ih h support
  | all x φ ih => intro h support; exact ih h support
  | ex x φ ih => intro h support; exact ih h support
  | know a φ ih =>
    intro h support
    cases a with
    | live a => exact ih h support
    | ghost a => exact ih h support
    | indexed a ν =>
      have inner : φ.labelSupport ⊆ F := fun μ hμ => support (Finset.mem_insert_of_mem hμ)
      have hν := support (Finset.mem_insert_self ν φ.labelSupport)
      refine ⟨h.1.relabel f pattern points, ?_, ih h.2.2 inner⟩
      intro μ hμ
      change μ ∈ (φ.relabel f).labelSupport at hμ
      rw [labelSupport_relabel] at hμ
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hμ
      exact ⟨(pattern.2.1 η (inner hη) ν hν).mpr (h.2.1 η hη).1,
        pattern.2.2.1 η (inner hη) ν hν (h.2.1 η hη).2⟩

theorem mainGuarded_relabel {Label : Type} [LinearOrder Label]
    (R₁ R₂ : Label → Label → Prop) (E : Finset Nat) (B F : Finset Label)
    (φ : Formula (RecordedHead Nat Label)) (f : Label → Label)
    (pattern : CoversLabelPattern R₁ R₂ F f) (points : B ⊆ F)
    (support : φ.labelSupport ⊆ F) (h : φ.MainGuarded R₁ R₂ E B) :
    (φ.relabel f).MainGuarded R₁ R₂ E (B.image f) := by
  revert support
  revert h
  induction φ with
  | falsum => intro _ _; trivial
  | equal t u => intro _ _; trivial
  | imp φ ψ ihφ ihψ =>
    intro h support
    exact ⟨ihφ h.1 (fun μ hμ => support (Finset.mem_union_left _ hμ)),
      ihψ h.2 (fun μ hμ => support (Finset.mem_union_right _ hμ))⟩
  | conj φ ψ ihφ ihψ =>
    intro h support
    exact ⟨ihφ h.1 (fun μ hμ => support (Finset.mem_union_left _ hμ)),
      ihψ h.2 (fun μ hμ => support (Finset.mem_union_right _ hμ))⟩
  | disj φ ψ ihφ ihψ =>
    intro h support
    exact ⟨ihφ h.1 (fun μ hμ => support (Finset.mem_union_left _ hμ)),
      ihψ h.2 (fun μ hμ => support (Finset.mem_union_right _ hμ))⟩
  | neg φ ih => intro h support; exact ih h support
  | all x φ ih => intro h support; exact ih h support
  | ex x φ ih => intro h support; exact ih h support
  | know a φ ih =>
    intro h support
    cases a with
    | live e =>
      refine ⟨?_, ih h.2 support⟩
      intro he
      change (φ.relabel f).IndexedGuarded R₁ R₂ (B.image f) (φ.relabel f).erase.shape.rank
      simpa only [erase_relabel] using
        indexedGuarded_relabel R₁ R₂ B F φ.erase.shape.rank φ f pattern points support (h.1 he)
    | ghost e => exact ih h support
    | indexed a ν =>
      exact ih h (fun μ hμ => support (Finset.mem_insert_of_mem hμ))

end Formula
end Alexander313
