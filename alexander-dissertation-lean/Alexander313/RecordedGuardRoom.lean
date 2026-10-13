import Alexander313.RecordedGuardRequirements
import Alexander313.RecordedCertificateLifts

/-!
# Actual finite guard-point sets from bounded chains

Each literal rank/base request receives an actual finite R₂ chain below the
required cut. The union of those written chains is the marker-point set; no
supplied marker set or guard-holding oracle is needed. The equivalence below
identifies the exact remaining ordinal input. It does not prove that the
required bounded chains exist, or identify either relation with a replacement
relation on natural ranks.
-/

namespace Alexander313

def BoundedGuardChain {Label : Type} [LT Label]
    (R₂ : Label → Label → Prop) (δ : Label) (k : Nat) (ν : Label) : Prop :=
  ∃ tail : List Label, tail.length = k ∧
    (ν :: tail).Pairwise (· < ·) ∧ (ν :: tail).Pairwise R₂ ∧
    ∀ μ ∈ ν :: tail, μ < δ

namespace GuardRequirements

def Bounded {Label : Type} [LT Label] (R₁ R₂ : Label → Label → Prop)
    (δ : Label) (p : GuardRequirements Label) : Prop :=
  (∀ q ∈ p.1, BoundedGuardChain R₂ δ q.1 q.2) ∧
    ∀ q ∈ p.2, q.1 < q.2 ∧ R₁ q.1 q.2

/-- This is the finite union of the actual supplied chain lists, including
their base points. Repeated requirements and shared points are harmless. -/
def chainPoints {Label : Type} [DecidableEq Label] (requests : List (Nat × Label))
    (tails : Nat × Label → List Label) : Finset Label :=
  (requests.flatMap (fun q => q.2 :: tails q)).toFinset

@[simp] theorem mem_chainPoints {Label : Type} [DecidableEq Label]
    (requests : List (Nat × Label)) (tails : Nat × Label → List Label) (μ : Label) :
    μ ∈ chainPoints requests tails ↔ ∃ q ∈ requests, μ ∈ q.2 :: tails q := by
  simp only [chainPoints, List.mem_toFinset, List.mem_flatMap]

theorem chainPoints_below {Label : Type} [LT Label] [DecidableEq Label]
    (requests : List (Nat × Label)) (tails : Nat × Label → List Label) (δ : Label)
    (below : ∀ q ∈ requests, ∀ μ ∈ q.2 :: tails q, μ < δ) :
    ∀ μ ∈ chainPoints requests tails, μ < δ := by
  intro μ hμ
  obtain ⟨q, hq, hp⟩ := (mem_chainPoints requests tails μ).mp hμ
  exact below q hq μ hp

theorem holds_chainPoints {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (p : GuardRequirements Label)
    (tails : Nat × Label → List Label)
    (chains : ∀ q ∈ p.1, (tails q).length = q.1 ∧
      (q.2 :: tails q).Pairwise (· < ·) ∧ (q.2 :: tails q).Pairwise R₂)
    (edges : ∀ q ∈ p.2, q.1 < q.2 ∧ R₁ q.1 q.2) :
    Holds R₁ R₂ (chainPoints p.1 tails) p := by
  refine ⟨?_, edges⟩
  intro q hq
  obtain ⟨hl, ho, hr⟩ := chains q hq
  refine ⟨tails q, hl, ho, hr, ?_⟩
  intro μ hμ
  exact (mem_chainPoints p.1 tails μ).mpr ⟨q, hq, hμ⟩

/-- The forward direction constructs the set by a finite union of actual
bounded chain witnesses. The reverse direction records exactly the same
ordinal chain-existence requirement, with no extra point-set hypothesis. -/
theorem bounded_iff_holds_room {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (δ : Label) (p : GuardRequirements Label) :
    Bounded R₁ R₂ δ p ↔
      ∃ B : Finset Label, Holds R₁ R₂ B p ∧ ∀ μ ∈ B, μ < δ := by
  constructor
  · rintro ⟨chains, edges⟩
    let tails : Nat × Label → List Label := fun q =>
      if h : q ∈ p.1 then Classical.choose (chains q h) else []
    have spec (q : Nat × Label) (hq : q ∈ p.1) :
        (tails q).length = q.1 ∧ (q.2 :: tails q).Pairwise (· < ·) ∧
        (q.2 :: tails q).Pairwise R₂ ∧ ∀ μ ∈ q.2 :: tails q, μ < δ := by
      dsimp only [tails]
      rw [dif_pos hq]
      exact Classical.choose_spec (chains q hq)
    refine ⟨chainPoints p.1 tails, holds_chainPoints R₁ R₂ p tails
      (fun q hq => ⟨(spec q hq).1, (spec q hq).2.1, (spec q hq).2.2.1⟩) edges, ?_⟩
    exact chainPoints_below p.1 tails δ (fun q hq => (spec q hq).2.2.2)
  · rintro ⟨B, holds, room⟩
    refine ⟨?_, holds.2⟩
    intro q hq
    obtain ⟨tail, hl, ho, hr, hp⟩ := holds.1 q hq
    exact ⟨tail, hl, ho, hr, fun μ hμ => room μ (hp μ hμ)⟩

@[simp] theorem bounded_empty {Label : Type} [LT Label]
    (R₁ R₂ : Label → Label → Prop) (δ : Label) : Bounded R₁ R₂ δ ([], []) := by
  simp [Bounded]

@[simp] theorem bounded_append {Label : Type} [LT Label]
    (R₁ R₂ : Label → Label → Prop) (δ : Label) (p q : GuardRequirements Label) :
    Bounded R₁ R₂ δ (append p q) ↔ Bounded R₁ R₂ δ p ∧ Bounded R₁ R₂ δ q := by
  simp only [Bounded, append, List.mem_append, or_imp, forall_and]
  tauto

end GuardRequirements

namespace Formula

theorem mainGuardRequirements_bounded_iff {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (E : Finset Nat) (δ : Label)
    (φ : Formula (RecordedHead Nat Label)) :
    GuardRequirements.Bounded R₁ R₂ δ (φ.mainGuardRequirements E) ↔
      ∃ B : Finset Label, φ.MainGuarded R₁ R₂ E B ∧ ∀ μ ∈ B, μ < δ := by
  rw [GuardRequirements.bounded_iff_holds_room]
  exact exists_congr (fun B => and_congr (mainGuardRequirements_exact R₁ R₂ E B φ) Iff.rfl)

/-- Fresh marker syntax is constructed against any displayed finite set of
source shapes, including the shapes from an entire source certificate. -/
theorem bounded_main_markers {Label : Type} [LT Label] [DecidableEq Label]
    (R₁ R₂ : Label → Label → Prop) (E : Finset Nat) (δ : Label)
    (φ : Formula (RecordedHead Nat Label)) (F : Finset (Shape Nat))
    (bounded : GuardRequirements.Bounded R₁ R₂ δ (φ.mainGuardRequirements E)) :
    ∃ ms : List (Label × Nat), (ms.map Prod.snd).Nodup ∧
      (∀ p ∈ ms, (markerTag Nat p.2).shape ∉ F) ∧
      φ.MainGuarded R₁ R₂ E (markerPoints ms) ∧ ∀ p ∈ ms, p.1 < δ := by
  obtain ⟨B, guard, room⟩ := (mainGuardRequirements_bounded_iff R₁ R₂ E δ φ).mp bounded
  obtain ⟨ms, points, nodup, fresh⟩ := freshMarkerBundle F B
  refine ⟨ms, nodup, fresh, by simpa only [points] using guard, ?_⟩
  intro p hp
  apply room p.1
  rw [← points]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)

end Formula

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

/-- Actual guarded main-cut membership now requires only the literal finite
edge checks and bounded chain witnesses. Its marker set is constructed. -/
theorem main_source_bounded_cuts (a : Nat) (δ : Label) (σ atom : Formula Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (source : RecordedMainSource C A E a σ atom)
    (hereditary : HereditaryQueries H) (disjoint : Disjoint A E)
    (bounded : GuardRequirements.Bounded R₁ R₂ δ
      ((atom.record (mainHeads A E H labels)).mainGuardRequirements E))
    (hadm : (σ.record (mainHeads A E H labels)).RecordedAdmissible A E)
    (below : ∀ μ ∈ (σ.record (mainHeads A E H labels)).labelSupport, μ < δ) :
    cuts C A E R₁ R₂ a δ (σ.record (mainHeads A E H labels)) := by
  obtain ⟨B, guard, room⟩ :=
    (Formula.mainGuardRequirements_bounded_iff R₁ R₂ E δ _).mp bounded
  exact main_source_cuts C A E R₁ R₂ a δ σ atom H labels B source hereditary disjoint
    guard hadm below room

end RecordedStage
end Alexander313
