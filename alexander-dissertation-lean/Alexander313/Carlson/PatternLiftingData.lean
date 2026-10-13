import Alexander313.Carlson.ContinuityAnchors

/-!
# The common-carrier candidate for a continuous pattern lifting

Carlson, *Patterns of resemblance of order 2*, Lemma 12.6, pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 49–56 of the author's October 16, 2008 manuscript.

The arithmetic lifting has been normalized so that both maps are the
identity. The old target and the extended source meet exactly in the base.
Mixed relations are expressed using their least old upper bounds. These are
the normal forms of the relations in Claims 1–4 of Carlson's proof.
-/

noncomputable section

namespace Alexander313.Carlson
namespace PatternLiftingConstruction

variable {α : Type*} [LinearOrder α]

/-- The normalized data for the finite continuous lifting construction. -/
structure Data (P Pplus Q : Str α) (U : Finset α) : Prop where
  source_pattern : Pplus.IsPattern
  target_pattern : Q.IsPattern
  source_cont : Str.Continuous P Pplus
  target_cont : Str.Continuous P Q
  arithmetic : ArithmeticLifting P.U Pplus.U Q.U U id id

namespace Data

variable {P Pplus Q : Str α} {U : Finset α} (D : Data P Pplus Q U)

/-- The candidate retains both given relations on their original carriers.
An incoming second-level edge may first reach a source point and then
follow a source second-level edge. -/
def candidate (_D : Data P Pplus Q U) : Str α :=
  { U := U
    r₁ := fun x y =>
      if x ∈ Q.U then
        if y ∈ Q.U then Q.r₁ x y
        else x ≤ y ∧ Q.r₁ x (Str.up P.U y)
      else
        if y ∈ Q.U then
          Pplus.r₁ x (Str.up P.U x) ∧ Q.r₁ (Str.up P.U x) y
        else Pplus.r₁ x y
    r₂ := fun x y =>
      if x ∈ Q.U then
        if y ∈ Q.U then Q.r₂ x y
        else ∃ a ∈ Pplus.U, x ≤ a ∧ Pplus.r₁ a (Str.up P.U a) ∧
          Q.r₂ x (Str.up P.U a) ∧ Pplus.r₂ a y
      else
        if y ∈ Q.U then
          Pplus.r₂ x (Str.up P.U x) ∧ Q.r₂ (Str.up P.U x) y
        else Pplus.r₂ x y }

@[simp] theorem candidate_U : D.candidate.U = U := rfl

-- These lemmas use the lifting hypotheses only in their proofs.
include D

theorem source_mem {x : α} (hx : x ∈ Pplus.U) : x ∈ U :=
  D.arithmetic.mem x hx

theorem target_mem {x : α} (hx : x ∈ Q.U) : x ∈ U :=
  D.arithmetic.target_sub hx

theorem base_source_mem {x : α} (hx : x ∈ P.U) : x ∈ Pplus.U :=
  D.source_cont.1.1 hx

theorem base_target_mem {x : α} (hx : x ∈ P.U) : x ∈ Q.U :=
  D.target_cont.1.1 hx

theorem source_of_not_target {x : α} (hx : x ∈ U) (hxQ : x ∉ Q.U) :
    x ∈ Pplus.U := by
  have hU : U = Q.U ∪ Pplus.U := by
    simpa only [Finset.image_id] using D.arithmetic.carrier_eq
  rw [hU] at hx
  exact (Finset.mem_union.mp hx).resolve_left hxQ

theorem source_target_iff {x : α} (hx : x ∈ Pplus.U) :
    x ∈ Q.U ↔ x ∈ P.U :=
  D.arithmetic.image_mem_base_iff hx

theorem up_source {x : α} (hx : x ∈ Pplus.U) :
    Str.LeastGE P.U x (Str.up P.U x) :=
  Str.up_spec (D.source_cont.2.1 x hx)

theorem up_target {x : α} (hx : x ∈ Q.U) :
    Str.LeastGE P.U x (Str.up P.U x) :=
  Str.up_spec (D.target_cont.2.1 x hx)

theorem up_source_target {x : α} (hx : x ∈ Pplus.U) :
    Str.LeastGE Q.U x (Str.up P.U x) :=
  D.arithmetic.leastGE_image hx (D.up_source hx)

theorem up_source_mem {x : α} (hx : x ∈ Pplus.U) :
    Str.up P.U x ∈ Pplus.U :=
  D.base_source_mem (D.up_source hx).1

theorem up_target_mem {x : α} (hx : x ∈ Pplus.U) :
    Str.up P.U x ∈ Q.U :=
  D.base_target_mem (D.up_source hx).1

theorem old_le_source_up {x y : α} (hx : x ∈ Q.U) (hy : y ∈ Pplus.U)
    (hyQ : y ∉ Q.U) (hxy : x ≤ y) : x < Str.up P.U y := by
  have hyP : y ∉ P.U := fun hyP => hyQ (D.base_target_mem hyP)
  have hlt : y < Str.up P.U y := (D.arithmetic.source_justBelow hy hyP).2.1
  exact hxy.trans_lt hlt

theorem source_le_old_up {x y : α} (hx : x ∈ Pplus.U) (hy : y ∈ Q.U)
    (hxy : x ≤ y) : Str.up P.U x ≤ y :=
  (D.up_source_target hx).2.2 y hy hxy

theorem old_lt_source_of_lt_up {x y : α} (hx : x ∈ Q.U) (hy : y ∈ Pplus.U)
    (hyQ : y ∉ Q.U) (hxy : x < Str.up P.U y) : x < y := by
  have hyP : y ∉ P.U := fun hyP => hyQ (D.base_target_mem hyP)
  exact (D.arithmetic.old_lt_image_iff hy hyP hx).mpr hxy

end Data
end PatternLiftingConstruction
end Alexander313.Carlson
