import Alexander313.Carlson.ComputableFairSequence
import Alexander313.Carlson.FairOrdinalRealization

/-!
# Executable finite searches in a computed fair limit

Membership and both relations in the union of a computed fair sequence have
total finite-stage searches. A search accepts exactly when its queried fact
holds in one of the requested stages. Increasing the bound preserves every
positive answer; existence of an accepting bound characterizes the union.

Relation checks include membership of both endpoints, so stored off-carrier
edges cannot create a limit relation. Once both points have appeared, their
relation is settled by that finite stage and every later search agrees.
An unbounded search for a point that never appears need not terminate.

Covered initial patterns also inherit the existing exact ordinal-realization
theorem. That conclusion is classical; no algorithm for ordinal labels,
representation in the `Program` language, or finite tallness is asserted.
-/

namespace Alexander313.Carlson.Finite.ComputableFairSequence

/-- Search stages strictly below `bound` for a rational carrier point. -/
def containsBelow (P : RationalPresentation) (x : ℚ) (bound : ℕ) : Bool :=
  acceptsBelow (fun n => decide (x ∈ (stage P n).U)) bound

/-- Search stages strictly below `bound` for a relation edge with both
endpoints in the finite stage carrier. -/
def relatesBelow (P : RationalPresentation) (level : Lvl) (x y : ℚ)
    (bound : ℕ) : Bool :=
  acceptsBelow (fun n =>
    let T := stage P n
    decide (x ∈ T.U ∧ y ∈ T.U) &&
      match level with
      | .one => decide ((x, y) ∈ T.r₁)
      | .two => decide ((x, y) ∈ T.r₂)) bound

@[simp] theorem containsBelow_zero (P : RationalPresentation) (x : ℚ) :
    containsBelow P x 0 = false := rfl

@[simp] theorem relatesBelow_zero (P : RationalPresentation) (level : Lvl) (x y : ℚ) :
    relatesBelow P level x y 0 = false := rfl

/-- Finite carrier search has an exact bounded-stage specification. -/
@[simp] theorem containsBelow_eq_true (P : RationalPresentation) (x : ℚ) (bound : ℕ) :
    containsBelow P x bound = true ↔
      ∃ n, n < bound ∧ x ∈ (stage P n).U := by
  simp only [containsBelow, acceptsBelow_eq_true, decide_eq_true_eq]

/-- Finite relation search has an exact bounded-stage specification,
including the membership of both queried endpoints. -/
@[simp] theorem relatesBelow_eq_true (P : RationalPresentation) (level : Lvl)
    (x y : ℚ) (bound : ℕ) :
    relatesBelow P level x y bound = true ↔
      ∃ n, n < bound ∧ x ∈ (stage P n).U ∧ y ∈ (stage P n).U ∧
        (stage P n).toStr.rel level x y := by
  cases level <;>
    simp only [relatesBelow, acceptsBelow_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Str.rel, RationalPresentation.toStr, and_assoc]

theorem containsBelow_mono {P : RationalPresentation} {x : ℚ} {m n : ℕ}
    (hmn : m ≤ n) (h : containsBelow P x m = true) :
    containsBelow P x n = true :=
  acceptsBelow_mono hmn h

theorem relatesBelow_mono {P : RationalPresentation} {level : Lvl}
    {x y : ℚ} {m n : ℕ} (hmn : m ≤ n)
    (h : relatesBelow P level x y m = true) : relatesBelow P level x y n = true :=
  acceptsBelow_mono hmn h

/-- Positive finite carrier search eventually succeeds exactly for the
points of the generated union. -/
theorem mem_limit_iff_eventually_contains (P : RationalPresentation)
    (hP : P.toStr.IsPattern) (x : ℚ) :
    x ∈ (toGeneratingSequence P hP).carrier ↔
      ∃ bound, containsBelow P x bound = true := by
  constructor
  · rintro ⟨n, hx⟩
    exact ⟨n + 1, (containsBelow_eq_true P x (n + 1)).mpr
      ⟨n, Nat.lt_succ_self n, hx⟩⟩
  · rintro ⟨bound, h⟩
    obtain ⟨n, _, hx⟩ := (containsBelow_eq_true P x bound).mp h
    exact ⟨n, hx⟩

/-- Positive finite relation search eventually succeeds exactly for the
carrier-restricted relation in the generated union. -/
theorem limit_rel_iff_eventually_relates (P : RationalPresentation)
    (hP : P.toStr.IsPattern) (level : Lvl) (x y : ℚ) :
    (toGeneratingSequence P hP).rel level x y ↔
      ∃ bound, relatesBelow P level x y bound = true := by
  constructor
  · rintro ⟨n, hx, hy, hr⟩
    exact ⟨n + 1, (relatesBelow_eq_true P level x y (n + 1)).mpr
      ⟨n, Nat.lt_succ_self n, hx, hy, hr⟩⟩
  · rintro ⟨bound, h⟩
    obtain ⟨n, _, hx, hy, hr⟩ := (relatesBelow_eq_true P level x y bound).mp h
    exact ⟨n, hx, hy, hr⟩

/-- A bounded carrier search is already settled at its last stage because
the stage carriers increase. -/
theorem containsBelow_succ_iff (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (x : ℚ) (n : ℕ) :
    containsBelow P x (n + 1) = true ↔ x ∈ (stage P n).U := by
  constructor
  · intro h
    obtain ⟨m, hm, hx⟩ := (containsBelow_eq_true P x (n + 1)).mp h
    exact (toGeneratingSequence P hP).mem_mono (Nat.lt_succ_iff.mp hm) hx
  · intro hx
    exact (containsBelow_eq_true P x (n + 1)).mpr ⟨n, Nat.lt_succ_self n, hx⟩

/-- A bounded relation search agrees with its last stage, including
endpoint membership, because every generating step is a substructure. -/
theorem relatesBelow_succ_iff (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (level : Lvl) (x y : ℚ) (n : ℕ) :
    relatesBelow P level x y (n + 1) = true ↔
      x ∈ (stage P n).U ∧ y ∈ (stage P n).U ∧ (stage P n).toStr.rel level x y := by
  constructor
  · intro h
    obtain ⟨m, hm, hx, hy, hr⟩ := (relatesBelow_eq_true P level x y (n + 1)).mp h
    have hs := (toGeneratingSequence P hP).isSub (Nat.lt_succ_iff.mp hm)
    exact ⟨hs.1 hx, hs.1 hy, (hs.rel_iff hx hy level).mp hr⟩
  · rintro ⟨hx, hy, hr⟩
    exact (relatesBelow_eq_true P level x y (n + 1)).mpr
      ⟨n, Nat.lt_succ_self n, hx, hy, hr⟩

/-- Once a stage contains both endpoints, every search including that
stage gives the exact answer for their relation in the whole limit. -/
theorem relatesBelow_iff_limit_of_captured (P : RationalPresentation)
    (hP : P.toStr.IsPattern) (level : Lvl) {x y : ℚ} {n bound : ℕ}
    (hn : n < bound) (hx : x ∈ (stage P n).U) (hy : y ∈ (stage P n).U) :
    relatesBelow P level x y bound = true ↔
      (toGeneratingSequence P hP).rel level x y := by
  constructor
  · intro h
    exact (limit_rel_iff_eventually_relates P hP level x y).mpr ⟨bound, h⟩
  · intro h
    exact (relatesBelow_eq_true P level x y bound).mpr
      ⟨n, hn, hx, hy, ((toGeneratingSequence P hP).rel_iff n hx hy level).mp h⟩

/-- The relation between captured points can be read from their capture
stage; later search bounds cannot change either a positive or negative answer. -/
theorem relatesBelow_iff_stage_of_captured (P : RationalPresentation)
    (hP : P.toStr.IsPattern) (level : Lvl) {x y : ℚ} {n bound : ℕ}
    (hn : n < bound) (hx : x ∈ (stage P n).U) (hy : y ∈ (stage P n).U) :
    relatesBelow P level x y bound = true ↔ (stage P n).toStr.rel level x y :=
  (relatesBelow_iff_limit_of_captured P hP level hn hx hy).trans
    ((toGeneratingSequence P hP).rel_iff n hx hy level)

/-- Covered initial data give the computed fair sequence an exact ordinal
realization by the existing classical semantic theorem. -/
theorem ordinalRealization (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (hcovered : Str.Covered P.toStr) :
    Nonempty (GeneratingSequence.OrdinalRealization (toGeneratingSequence P hP)) :=
  (fair P hP).ordinalRealization hcovered

end Alexander313.Carlson.Finite.ComputableFairSequence
