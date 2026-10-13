import Alexander313.Carlson.DenseGenerationTransport
import Alexander313.Carlson.ExactLeastCopyAgreement

/-!
# Characterization of generation by validity and continuity

Carlson, Theorem 14.11 and Corollary 14.12, pure rational case.
Agreement of the actual least copies, together with the largest-point
condition, gives generation. The ordinal proof is transported across its
entire finite support, including the hidden chain witnesses.
-/

noncomputable section

namespace Alexander313.Carlson
namespace Str

/-- Bounded induced extensions whose actual least copies agree are generated.
The largest-point condition is stated without choosing a maximum, so empty
carriers are covered as well. -/
theorem Generates.of_least_copy_agreement {P Q : Str ℚ} (hsub : IsSub P Q)
    (A : PatternRealization P) (B : PatternRealization Q)
    (hagree : ∀ x ∈ P.U, B.label x = A.label x)
    (hbounded : ∀ z ∈ Q.U, ∃ p ∈ P.U, z ≤ p) : Generates P Q := by
  classical
  let U := P.U.image A.label
  let V := Q.U.image B.label
  have hUV : U ⊆ V := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [← hagree x hx]
    exact Finset.mem_image_of_mem B.label (hsub.1 hx)
  have hb : ∀ z ∈ V, ∃ p ∈ U, z ≤ p := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p, hp, hxp⟩ := hbounded x hx
    refine ⟨A.label p, Finset.mem_image_of_mem A.label hp, ?_⟩
    rw [← hagree p hp]
    exact (B.seed_isIso.le_iff hx (hsub.1 hp)).mpr hxp
  have d : Generates (ofOrdinals U) (ofOrdinals V) :=
    A.image_isominimal.generates hUV hb
  obtain ⟨gA, eA, hA, _⟩ := A.seed_isIso.exists_inverse
  obtain ⟨gB, eB, hB, _⟩ := B.seed_isIso.exists_inverse
  apply d.of_rational_isos eA eB
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  rw [← hagree x hx, hB x (hsub.1 hx), hagree x hx, hA x hx]

/-- Theorem 14.11, least-copy formulation. Continuity's two correctness
clauses follow from leastness once the source bounds the target. -/
theorem Generates.iff_bounded_and_least_copy_agrees {P Q : Str ℚ}
    (hsub : IsSub P Q) (A : PatternRealization P) (B : PatternRealization Q) :
    Generates P Q ↔ (∀ z ∈ Q.U, ∃ p ∈ P.U, z ≤ p) ∧
      (∀ x ∈ P.U, B.label x = A.label x) :=
  ⟨fun d => ⟨d.continuous.2.1, d.valid.least_copy_agrees A B⟩,
    fun h => Generates.of_least_copy_agreement hsub A B h.2 h.1⟩

/-- Theorem 14.11, validity formulation, for every pair of pure rational
patterns. No oracle for a generation witness or covering is assumed. -/
theorem Generates.iff_valid_continuous {P Q : Str ℚ}
    (hP : P.IsPattern) (hQ : Q.IsPattern) :
    Generates P Q ↔ Valid P Q ∧ Continuous P Q := by
  constructor
  · intro d
    exact ⟨d.valid, d.continuous⟩
  · rintro ⟨hv, hc⟩
    let A := PatternRealization.ofPattern P hP
    let B := PatternRealization.ofPattern Q hQ
    exact Generates.of_least_copy_agreement hv.1 A B
      (hv.least_copy_agrees A B) hc.2.1

/-- Theorem 14.11, cofinal-validity formulation. -/
theorem Generates.iff_cofinallyValid_continuous {P Q : Str ℚ}
    (hP : P.IsPattern) (hQ : Q.IsPattern) :
    Generates P Q ↔ CofinallyValid P Q ∧ Continuous P Q := by
  constructor
  · intro d
    exact ⟨d.cofinallyValid, d.continuous⟩
  · rintro ⟨hv, hc⟩
    exact (Generates.iff_valid_continuous hP hQ).mpr ⟨hv.valid, hc⟩

/-- Corollary 14.12: actual generation composes in the pure rational case. -/
theorem Generates.trans {P Q R : Str ℚ} (d : Generates P Q) (e : Generates Q R) :
    Generates P R :=
  (Generates.iff_valid_continuous d.source_pattern e.target_pattern).mpr
    ⟨d.valid.trans e.valid, d.continuous.trans e.continuous⟩

end Str
end Alexander313.Carlson
