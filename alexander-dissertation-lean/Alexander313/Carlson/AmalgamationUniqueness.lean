import Alexander313.Carlson.AmalgamationExistence
import Alexander313.Carlson.ExactLeastCopyAgreement
import Alexander313.Carlson.FiniteIsomorphism

/-!
# Uniqueness of finite rational amalgamations

Carlson, Theorem 15.9(2), printed pp. 75--76. Exactness identifies each
input image in an amalgamation's least ordinal copy with the input's own
least copy. The union condition then identifies the entire ordinal image.
Taking one finite inverse constructs an isomorphism compatible with every
given input embedding, including when inputs overlap or the family is empty.
-/

noncomputable section

namespace Alexander313.Carlson.Str

variable {n : ℕ} {P : Fin n → Str ℚ} {Q Q' : Str ℚ}
variable {f f' : Fin n → ℚ → ℚ}

/-- Each supplied input embedding lands in the whole amalgamation. -/
theorem Amalgamation.mem (d : Amalgamation P Q f) (i : Fin n)
    {x : ℚ} (hx : x ∈ (P i).U) : f i x ∈ Q.U :=
  (d.exact i).isSub.1 ((d.embeddings i).mem hx)

/-- The least image of any amalgamation is exactly the union of the
least images of its inputs, with their given embeddings accounted for. -/
theorem Amalgamation.least_image (d : Amalgamation P Q f)
    (A : ∀ i, PatternRealization (P i)) (B : PatternRealization Q) :
    Q.U.image B.label = Finset.univ.biUnion (fun i => (P i).U.image (A i).label) := by
  classical
  have hagree (i : Fin n) : ∀ x ∈ (P i).U, B.label (f i x) = (A i).label x :=
    (d.embeddings i).exact_least_copy_agrees (hxExact := d.exact i) (A := A i) (B := B)
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [d.union] at hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨x, hx, (hagree i x hx).symm⟩⟩
  · intro hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨f i x, d.mem i hx, hagree i x hx⟩

/-- Theorem 15.9(2): there is an actual isomorphism between any two
rational amalgamations, compatible pointwise with every input embedding. -/
theorem Amalgamation.exists_compatible_iso (d : Amalgamation P Q f)
    (d' : Amalgamation P Q' f') (hP : ∀ i, (P i).IsPattern) :
    ∃ g : ℚ → ℚ, IsIso Q Q' g ∧
      ∀ i, ∀ x ∈ (P i).U, g (f i x) = f' i x := by
  let A (i : Fin n) := PatternRealization.ofPattern (P i) (hP i)
  let B := PatternRealization.ofPattern Q d.pattern
  let B' := PatternRealization.ofPattern Q' d'.pattern
  have hU : Q.U.image B.label = Q'.U.image B'.label :=
    (d.least_image A B).trans (d'.least_image A B').symm
  have e' : IsIso Q' (ofOrdinals (Q.U.image B.label)) B'.label :=
    hU.symm ▸ B'.seed_isIso
  obtain ⟨g, hg, hcomm⟩ := B.seed_isIso.between_copies e'
  refine ⟨g, hg, ?_⟩
  intro i x hx
  apply B'.seed_isIso.injOn (hg.mem (d.mem i hx)) (d'.mem i hx)
  calc
    B'.label (g (f i x)) = B.label (f i x) := hcomm _ (d.mem i hx)
    _ = (A i).label x :=
      (d.embeddings i).exact_least_copy_agrees
        (hxExact := d.exact i) (A := A i) (B := B) x hx
    _ = B'.label (f' i x) :=
      ((d'.embeddings i).exact_least_copy_agrees
        (hxExact := d'.exact i) (A := A i) (B := B') x hx).symm

end Alexander313.Carlson.Str
