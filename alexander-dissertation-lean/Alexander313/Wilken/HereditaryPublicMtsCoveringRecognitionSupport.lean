import Alexander313.Wilken.HereditaryPublicMtsCoveringSupport

/-!
# A concrete finite edge fold for the independent public covering

The fold records the literal current code and tests every independent
public-mu adjacency. Its exact proof reconstructs the original Covering
recurrence from genuine root admission and every tested edge, without
using mts or an assigned tracker as the definition. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringRecognitionSupport

open CoveringSupport (Covering)

abbrev State := Nat × Bool

def step (state : State) (current : Nat) : State :=
  (current, state.2 && PublicTrackingSequences.adjacencyCheck state.1 current)

def run (gamma : Nat) (tail : List Nat) : State := tail.foldl step (gamma, true)

inductive Steps : Nat → List Nat → Nat → Prop
  | nil (previous : Nat) : Steps previous [] previous
  | cons (previous current last : Nat) (tail : List Nat)
      (he : PublicTrackingSequences.adjacencyCheck previous current = true)
      (ht : Steps current tail last) : Steps previous (current :: tail) last

theorem fold_valid (state : State) (tail : List Nat) :
    (tail.foldl step state).2 = true ↔
      state.2 = true ∧ Steps state.1 tail (tail.foldl step state).1 := by
  induction tail generalizing state with
  | nil =>
    constructor
    · intro hs; exact ⟨hs, .nil _⟩
    · intro hs; exact hs.1
  | cons current rest ih =>
    change (rest.foldl step (step state current)).2 = true ↔ _
    rw [ih]
    constructor
    · rintro ⟨hs, ht⟩
      have he := Bool.and_eq_true.mp hs
      exact ⟨he.1, .cons _ current _ rest he.2 ht⟩
    · rintro ⟨hs, ht⟩
      cases ht with
      | cons previous current last rest he hrest =>
        exact ⟨Bool.and_eq_true.mpr ⟨hs, he⟩, hrest⟩

theorem run_valid (gamma : Nat) (tail : List Nat) :
    (run gamma tail).2 = true ↔ Steps gamma tail (run gamma tail).1 := by
  constructor
  · intro h; exact ((fold_valid (gamma, true) tail).mp h).2
  · intro h; exact (fold_valid (gamma, true) tail).mpr ⟨rfl, h⟩

theorem Steps.append_one {gamma previous : Nat} {tail : List Nat}
    (ht : Steps gamma tail previous) (current : Nat)
    (he : PublicTrackingSequences.adjacencyCheck previous current = true) :
    Steps gamma (tail ++ [current]) current := by
  revert he
  induction ht with
  | nil previous =>
    intro he
    exact .cons previous current current [] he (.nil current)
  | cons gamma next previous rest hedge hrest ih =>
    intro he
    exact .cons gamma next current (rest ++ [current]) hedge (ih he)

theorem Steps.covering {gamma previous last : Nat} {tail codes : List Nat}
    (ht : Steps previous tail last) (hc : Covering gamma previous codes) :
    Covering gamma last (codes ++ tail) := by
  revert hc
  induction ht generalizing codes with
  | nil previous =>
    intro hc
    simpa only [List.append_nil] using hc
  | cons previous current last rest he ht ih =>
    intro hc
    have hn := ih (codes ++ [current]) (Covering.append previous current codes hc he)
    simpa only [List.append_assoc, List.singleton_append] using hn

theorem covering_steps {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) :
    ∃ tail, codes = gamma :: tail ∧ Steps gamma tail current := by
  induction hc with
  | root hg => exact ⟨[], rfl, .nil gamma⟩
  | append previous current codes hp he ih =>
    obtain ⟨tail, hs, ht⟩ := ih
    exact ⟨tail ++ [current], by simp only [hs, List.cons_append], ht.append_one current he⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringRecognitionSupport
