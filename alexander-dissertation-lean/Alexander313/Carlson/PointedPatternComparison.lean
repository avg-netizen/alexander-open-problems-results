import Alexander313.Carlson.Core
import Alexander313.Carlson.AmalgamationUniqueness

/-!
# Pointed rational patterns and their actual core labels

Carlson's pointed-pattern map sends a finite pattern with a distinguished
carrier point to that point in its least ordinal copy. The domain below
uses the existing encoded rational seeds and their actual least
realizations; its image is exactly the common classical core.

Lemma 15.10(1), printed p. 76, identifies equality, order, and both
reflection relations of these labels with the finite relations in any
rational amalgamation. Exactness and the actual least-copy theorem prove
the comparison; no comparison procedure or supplied comparison oracle is
assumed. The pure language has no further function-symbol obligation.
-/

noncomputable section

namespace Alexander313.Carlson

/-- A finitely presented pattern with one distinguished carrier point. -/
structure PointedPattern where
  seed : CoreSeed
  point : ℚ
  mem : point ∈ seed.val.U

namespace PointedPattern

/-- Carlson's pointed-pattern map into the actual ordinal core. -/
def iota (p : PointedPattern) : Ordinal.{0} :=
  (coreRealization p.seed).label p.point

theorem corePoint (p : PointedPattern) : CorePoint p.iota :=
  ⟨p.seed, p.point, p.mem, rfl⟩

theorem lt_coreBound (p : PointedPattern) : p.iota < coreBound :=
  core_label_lt p.seed p.mem

end PointedPattern

/-- Pointed finite seeds present every element of the same classical core. -/
theorem corePoint_iff_pointed (a : Ordinal.{0}) :
    CorePoint a ↔ ∃ p : PointedPattern, p.iota = a := by
  constructor
  · rintro ⟨P, x, hx, hxa⟩
    exact ⟨⟨P, x, hx⟩, hxa⟩
  · rintro ⟨p, rfl⟩
    exact p.corePoint

namespace Str

variable {n : ℕ} {p : Fin n → PointedPattern} {Q : Str ℚ}
variable {f : Fin n → ℚ → ℚ}

private theorem Amalgamation.pointed_label
    (d : Amalgamation (fun i => (p i).seed.val.toStr) Q f)
    (B : PatternRealization Q) (i : Fin n) :
    B.label (f i (p i).point) = (p i).iota :=
  (d.embeddings i).exact_least_copy_agrees
    (hxExact := d.exact i) (A := coreRealization (p i).seed) (B := B)
    (p i).point (p i).mem

/-- Equality of core labels is exactly equality of the distinguished
points' images in any finite rational amalgamation. -/
theorem Amalgamation.pointed_eq_iff
    (d : Amalgamation (fun i => (p i).seed.val.toStr) Q f) (i j : Fin n) :
    (p i).iota = (p j).iota ↔ f i (p i).point = f j (p j).point := by
  let B := PatternRealization.ofPattern Q d.pattern
  rw [← d.pointed_label B i, ← d.pointed_label B j]
  exact ⟨B.seed_isIso.injOn (d.mem i (p i).mem) (d.mem j (p j).mem),
    congrArg B.label⟩

/-- The core order is the finite amalgamation order on these images. -/
theorem Amalgamation.pointed_le_iff
    (d : Amalgamation (fun i => (p i).seed.val.toStr) Q f) (i j : Fin n) :
    (p i).iota ≤ (p j).iota ↔ f i (p i).point ≤ f j (p j).point := by
  let B := PatternRealization.ofPattern Q d.pattern
  rw [← d.pointed_label B i, ← d.pointed_label B j]
  exact B.seed_isIso.le_iff (d.mem i (p i).mem) (d.mem j (p j).mem)

/-- The corresponding strict order comparison, derived from the same
finite isomorphism rather than an independent comparison assumption. -/
theorem Amalgamation.pointed_lt_iff
    (d : Amalgamation (fun i => (p i).seed.val.toStr) Q f) (i j : Fin n) :
    (p i).iota < (p j).iota ↔ f i (p i).point < f j (p j).point := by
  let B := PatternRealization.ofPattern Q d.pattern
  rw [← d.pointed_label B i, ← d.pointed_label B j]
  exact B.seed_isIso.lt_iff (d.mem i (p i).mem) (d.mem j (p j).mem)

/-- The actual ordinal R1 relation is read from either distinguished
image pair in any rational amalgamation. -/
theorem Amalgamation.pointed_one_iff
    (d : Amalgamation (fun i => (p i).seed.val.toStr) Q f) (i j : Fin n) :
    R1 (p i).iota (p j).iota ↔ Q.r₁ (f i (p i).point) (f j (p j).point) := by
  let B := PatternRealization.ofPattern Q d.pattern
  rw [← d.pointed_label B i, ← d.pointed_label B j]
  exact (B.seed_isIso.2.2 _ (d.mem i (p i).mem) _ (d.mem j (p j).mem)).1.symm

/-- The actual ordinal R2 relation is read from the same finite
amalgamation, including negative instances. -/
theorem Amalgamation.pointed_two_iff
    (d : Amalgamation (fun i => (p i).seed.val.toStr) Q f) (i j : Fin n) :
    R2 (p i).iota (p j).iota ↔ Q.r₂ (f i (p i).point) (f j (p j).point) := by
  let B := PatternRealization.ofPattern Q d.pattern
  rw [← d.pointed_label B i, ← d.pointed_label B j]
  exact (B.seed_isIso.2.2 _ (d.mem i (p i).mem) _ (d.mem j (p j).mem)).2.symm

end Str

end Alexander313.Carlson
