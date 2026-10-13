import Alexander313.FiniteCertificateTransport
import Alexander313.RecordedGuardRoom
import Alexander313.Computability

/-!
# The effective order-2 ordinal input as one explicit interface

Note 24 §1 lists what the stage argument consumes from the ordinal package
O₂*: a recursive well-ordered domain, positively enumerable `<`, ≤₁ and ≤₂,
finite covering reflection along R₁, connectedness, separated guard
room and long strict <₂-chains. This file states that list as a structure. It
is an *input* to the conditional assembly in `Thesis313FromPackage`; it is not
a new axiom and no instance is asserted here.

Labels are natural-number codes. A type synonym carries the package order, so
the ordinary order on `Nat` never enters instance search for stage labels. The
three programs recognise the order and both relations positively, which is all
that `RecordedLabelCutProgram.stage_exact` needs.

The room clause is the form used in note 24 §5: a rank-(k+1) guard at `top`
gives arbitrarily many separated rank-k guard copies below `top`, above any
finite goal support that is already ≤₁-below `top`, with every copy point
≤₁-below `top`. For pure R₂ this is the Σ₂ room argument of note 25 §6.

**Weakening of the hand proof's chain.** Note 25 asks for an infinite strict
<₂-chain, which lies beyond the core of R₂ (υ₂ <₂ υ₃ <₂ ⋯ below υω). The stage
argument only ever uses one guarded top per formula, of rank above that
formula's rank, and labels the formula's lift with the top's own room copies
(`RecordedStage.GuardedRoom`). So the clause `tall` asks only that guards of
every finite rank exist. This interface does not itself prove finite tallness.
`Carlson.CoreTallness.exists_guard_in_core` places every finite guard in the
same whole core, and `Carlson.EffectiveCorePackage.package_exists` constructs
the effective package. A semantic chain in an unspecified countable interval
would not establish that bound.

**Forward reflection (2026-10-09).** The `reflection` clause asks for
coverings (`FiniteLabelCovering`): a copy below α of each finite set below β
that fixes the part below α, keeps equality and order exactly, and carries R₁
and R₂ forward. Every generator relabelling in the stage chain uses only these
directions. True Σ-elementarity gives two-way copies, which
`FiniteLabelReflection.covering` converts. Carlson's covering-based order-2
relations (*Patterns of resemblance of order 2*, Definitions 5.2–5.4) give
exactly the forward version.
-/

namespace Alexander313

/-- Natural-number codes ordered by a supplied linear order. -/
def CodedLabel (_order : LinearOrder Nat) : Type := Nat

instance CodedLabel.instLinearOrder (order : LinearOrder Nat) :
    LinearOrder (CodedLabel order) := order

/-- A rank-k guard head: k further points above ν, pairwise ordered and
pairwise R₂-related, starting at ν. No marker set is attached. -/
def GuardHead {Label : Type} [LT Label] (R₂ : Label → Label → Prop) (k : Nat)
    (ν : Label) : Prop :=
  ∃ tail : List Label, tail.length = k ∧
    (ν :: tail).Pairwise (· < ·) ∧ (ν :: tail).Pairwise R₂

theorem GuardChainIn.guardHead {Label : Type} [LT Label] [DecidableEq Label]
    {R₂ : Label → Label → Prop} {B : Finset Label} {k : Nat} {ν : Label}
    (h : GuardChainIn R₂ B k ν) : GuardHead R₂ k ν := by
  obtain ⟨tail, hl, ho, hr, _⟩ := h
  exact ⟨tail, hl, ho, hr⟩

structure OrdinalPackage where
  order : LinearOrder Nat
  R₁ : CodedLabel order → CodedLabel order → Prop
  R₂ : CodedLabel order → CodedLabel order → Prop
  wf : WellFounded ((· < ·) : CodedLabel order → CodedLabel order → Prop)
  ltProgram : Program
  R₁Program : Program
  R₂Program : Program
  lt_program : ∀ μ ν : CodedLabel order,
    ltProgram.domain (Nat.pair μ ν) ↔ μ < ν
  R₁_program : ∀ μ ν : CodedLabel order,
    R₁Program.domain (Nat.pair μ ν) ↔ R₁ μ ν
  R₂_program : ∀ μ ν : CodedLabel order,
    R₂Program.domain (Nat.pair μ ν) ↔ R₂ μ ν
  R₁_refl : ∀ α, R₁ α α
  R₁_le : ∀ α β, R₁ α β → α ≤ β
  reflection : ∀ α β, R₁ α β → FiniteLabelCovering R₁ R₂ α β
  connected : ∀ p q r, R₁ p r → p ≤ q → q ≤ r → R₁ p q
  room : ∀ (k : Nat) (top : CodedLabel order), GuardHead R₂ (k + 1) top →
    ∀ X : Finset (CodedLabel order), (∀ x ∈ X, x < top ∧ R₁ x top) → ∀ N : Nat,
    ∃ copy : Nat → List (CodedLabel order),
      (∀ j < N, (copy j).length = k + 1 ∧ (copy j).Pairwise (· < ·) ∧
        (copy j).Pairwise R₂) ∧
      (∀ j < N, ∀ y ∈ copy j, (∀ x ∈ X, x < y) ∧ y < top ∧ R₁ y top) ∧
      (∀ i j, i < j → j < N → ∀ y ∈ copy i, ∀ z ∈ copy j, y < z)
  tall : ∀ k, ∃ top : CodedLabel order, GuardHead R₂ k top

namespace OrdinalPackage

variable (P : OrdinalPackage)

/-- The label type of the package, with its own order. -/
abbrev Label : Type := CodedLabel P.order

/-- The form consumed by the existing background and contextual truth lemmas. -/
theorem reflectionLink : ∀ μ ν : P.Label, P.R₁ μ ν →
    μ ≤ ν ∧ FiniteLabelCovering P.R₁ P.R₂ μ ν :=
  fun μ ν h => ⟨P.R₁_le μ ν h, P.reflection μ ν h⟩

/-- Every pair of points that are both ≤₁-below a common top is ≤₁-related in
increasing order. This is the coherent chain of note 24 §5. -/
theorem coherent {top x y : P.Label} (hx : P.R₁ x top) (hy : y ≤ top) (hxy : x ≤ y) :
    P.R₁ x y :=
  P.connected x y top hx hxy hy

def CoherentBelow (top : P.Label) : Set P.Label := fun y => y < top ∧ P.R₁ y top

theorem coherentBelow_R₁ (top : P.Label) {x y : P.Label}
    (hx : x ∈ P.CoherentBelow top) (hy : y ∈ P.CoherentBelow top) (hxy : x ≤ y) :
    P.R₁ x y :=
  P.coherent hx.2 (le_of_lt hy.1) hxy

end OrdinalPackage

end Alexander313
