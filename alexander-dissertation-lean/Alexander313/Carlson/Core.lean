import Alexander313.Carlson.UnconditionalRealization

/-!
# A common countable initial segment for all minimal finite copies

Take the supremum of the ordinal initial segments realized from all encoded
rational patterns. There are countably many seeds, and each segment is
countable. Every point of their union occurs in a finite stage and is the
pointwise least label of that stage's encoded pattern. Thus the union is
exactly the set of labels in these least finite copies, and is an initial
segment closed under both actual ordinal relations.

This constructs the classical core domain. Computable relation programs
and a presentation by all natural numbers are not asserted here.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal
open Finite

abbrev CoreSeed := {P : RationalPresentation // P.toStr.IsPattern}

def coreRealization (P : CoreSeed) : PatternRealization P.1.toStr :=
  PatternRealization.ofPattern P.1.toStr P.2

/-- The common ordinal bound of the countable family of least realizations. -/
def coreBound : Ordinal.{0} := ⨆ P : CoreSeed, (coreRealization P).bound

theorem coreBound_lt_omega_one : coreBound < ω₁ :=
  Ordinal.iSup_lt_omega_one fun P => (coreRealization P).bound_lt_omega_one P.2

/-- A label in a pointwise least exact ordinal copy of an encoded pattern. -/
def CorePoint (a : Ordinal.{0}) : Prop :=
  ∃ P : CoreSeed, ∃ x ∈ P.1.U, (coreRealization P).label x = a

theorem core_label_lt (P : CoreSeed) {x : ℚ} (hx : x ∈ P.1.U) :
    (coreRealization P).label x < coreBound :=
  ((coreRealization P).seed_label_lt_bound hx).trans_le (Ordinal.le_iSup _ P)

private theorem covering_iff_of_iso_id {P Q : Str ℚ} (e : Str.IsIso P Q id)
    (g : ℚ → Ordinal.{0}) : P.CoveringR g ↔ Q.CoveringR g := by
  have forward {P Q : Str ℚ} (e : Str.IsIso P Q id)
      (h : P.CoveringR g) : Q.CoveringR g := by
    have hU := e.universe_eq_of_id
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [← hU] at hx hy
      exact h.1 x hx y hy hxy
    · intro x hx y hy hxy
      rw [← hU] at hx hy
      exact h.2.1 x hx y hy ((e.2.2 x hx y hy).1.mpr hxy)
    · intro x hx y hy hxy
      rw [← hU] at hx hy
      exact h.2.2 x hx y hy ((e.2.2 x hx y hy).2.mpr hxy)
  exact ⟨forward e, forward e.symm_id⟩

/-- A label from any finite stage of any seed's realization is the least
label of an encoded finite pattern, hence belongs to the common core. -/
theorem stage_label_corePoint (P : CoreSeed) (n : ℕ) {x : ℚ}
    (hx : x ∈ ((coreRealization P).sequence.stage n).U) :
    CorePoint ((coreRealization P).label x) := by
  let A := coreRealization P
  let T := A.sequence.stage n
  let Q := RationalPresentation.encode T
  have e : Str.IsIso T Q.toStr id := RationalPresentation.presentation_iso T
  let q : CoreSeed := ⟨Q, e.isPattern (A.sequence.pattern n)⟩
  let B := coreRealization q
  have hxQ : x ∈ Q.U := hx
  have hB : T.CoveringR B.label :=
    (covering_iff_of_iso_id e B.label).mpr B.seed_covering
  have hA : Q.toStr.CoveringR A.label :=
    (covering_iff_of_iso_id e A.label).mp (A.ordinal.stage_covering n)
  have heq : B.label x = A.label x :=
    (B.seed_minimal hA hxQ).antisymm (A.ordinal.label_le_covering n hB hx)
  exact ⟨q, x, hxQ, heq⟩

/-- The core of least finite-copy labels is exactly one initial segment. -/
theorem corePoint_iff_lt_coreBound (a : Ordinal.{0}) : CorePoint a ↔ a < coreBound := by
  constructor
  · rintro ⟨P, x, hx, rfl⟩
    exact core_label_lt P hx
  · intro ha
    obtain ⟨P, hP⟩ := Ordinal.lt_iSup_iff.mp ha
    let A := coreRealization P
    let x : A.sequence.Limit := A.ordinal.orderIso.symm ⟨a, hP⟩
    have heq : A.label x.val = a := by
      change A.ordinal.label x.val = a
      rw [A.ordinal.label_eq x]
      exact congrArg Subtype.val (A.ordinal.orderIso.apply_symm_apply ⟨a, hP⟩)
    obtain ⟨n, hx⟩ := x.property
    exact heq ▸ stage_label_corePoint P n hx

theorem core_lt_of_R1 {a b : Ordinal.{0}} (ha : a < coreBound) (hab : R1 a b) :
    b < coreBound := by
  obtain ⟨P, hP⟩ := Ordinal.lt_iSup_iff.mp ha
  exact ((coreRealization P).ordinal.lt_bound_of_R1 hP hab).trans_le
    (Ordinal.le_iSup _ P)

theorem core_lt_of_R2 {a b : Ordinal.{0}} (ha : a < coreBound) (hab : R2 a b) :
    b < coreBound := core_lt_of_R1 ha (R2_R1 hab)

theorem corePoint_of_R1 {a b : Ordinal.{0}} (ha : CorePoint a) (hab : R1 a b) :
    CorePoint b :=
  (corePoint_iff_lt_coreBound b).mpr (core_lt_of_R1
    ((corePoint_iff_lt_coreBound a).mp ha) hab)

theorem corePoint_of_R2 {a b : Ordinal.{0}} (ha : CorePoint a) (hab : R2 a b) :
    CorePoint b := corePoint_of_R1 ha (R2_R1 hab)

/-- Every rational pattern has a least exact copy inside the same core
initial segment, including patterns with arbitrary off-carrier relations. -/
theorem exists_minimal_copy_in_core (P : Str ℚ) (hP : P.IsPattern) :
    ∃ h : ℚ → Ordinal.{0},
      Str.IsIso P (Str.ofOrdinals (P.U.image h)) h ∧
      (∀ x ∈ P.U, h x < coreBound) ∧
      ∀ g : ℚ → Ordinal.{0}, P.CoveringR g → ∀ x ∈ P.U, h x ≤ g x := by
  let Q := RationalPresentation.encode P
  have e : Str.IsIso P Q.toStr id := RationalPresentation.presentation_iso P
  let q : CoreSeed := ⟨Q, e.isPattern hP⟩
  let A := coreRealization q
  refine ⟨A.label, ⟨rfl, A.seed_isIso.2.1, ?_⟩,
    fun x hx => core_label_lt q hx, ?_⟩
  · intro x hx y hy
    have h₁ := e.2.2 x hx y hy
    have h₂ := A.seed_isIso.2.2 x hx y hy
    exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  · intro g hg x hx
    exact A.seed_minimal ((covering_iff_of_iso_id e g).mp hg) hx

end Alexander313.Carlson
