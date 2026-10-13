import Alexander313.Carlson.AmalgamationUniqueness
import Alexander313.Carlson.DenseGenerationTransport

/-!
# Rational presentations of finite amalgamations

The ordinal union in Theorem 15.9(1) has a finite rational relabeling.
Transporting the entire finite generation support into the dense rational
order preserves exactness, not just the visible endpoint pattern. Thus
every finite family of rational patterns has a rational amalgamation.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β] [Nonempty β]
variable {n : ℕ} {P : Fin n → Str α} {Q : Str β} {Q' : Str ℚ}
variable {f : Fin n → α → β} {g : β → ℚ}

/-- Relabeling a whole amalgamation into rational endpoints preserves
each input's exactness as well as the embeddings and union condition. -/
theorem Amalgamation.of_rational_iso (d : Amalgamation P Q f)
    (eplus : IsIso Q Q' g) : Amalgamation P Q' (fun i => g ∘ f i) := by
  classical
  have ei (i : Fin n) :
      IsIso (Q.restrict ((P i).U.image (f i)))
        (Q'.restrict ((P i).U.image (g ∘ f i))) g := by
    refine ⟨?_, ?_, ?_⟩
    · change ((P i).U.image (f i)).image g = (P i).U.image (g ∘ f i)
      exact Finset.image_image
    · intro x hx y hy hxy
      exact eplus.2.1 x ((d.exact i).isSub.1 hx) y ((d.exact i).isSub.1 hy) hxy
    · intro x hx y hy
      exact eplus.2.2 x ((d.exact i).isSub.1 hx) y ((d.exact i).isSub.1 hy)
  refine ⟨eplus.isPattern d.pattern, fun i => (ei i).comp (d.embeddings i), ?_, ?_⟩
  · rw [← eplus.1, d.union, Finset.biUnion_image]
    simp only [Finset.image_image]
  · intro i
    exact (d.exact i).of_rational_isos (ei i) eplus (fun _ _ => rfl)

end Str

/-- Every finite family of rational patterns has a rational amalgamation,
including empty families and overlapping input images. -/
theorem exists_rational_amalgamation {n : ℕ} (P : Fin n → Str ℚ)
    (hP : ∀ i, (P i).IsPattern) :
    ∃ (Q : Str ℚ) (f : Fin n → ℚ → ℚ), Str.Amalgamation P Q f := by
  obtain ⟨U, f, d, _, _⟩ := exists_ordinal_amalgamation P hP
  let F := ordinalRationalRelabeling U
  have e : Str.IsIso (Str.ofOrdinals U) ((Str.ofOrdinals U).map F.toFun) F.toFun :=
    F.isIso (Finset.Subset.refl U)
  exact ⟨(Str.ofOrdinals U).map F.toFun, fun i => F.toFun ∘ f i, d.of_rational_iso e⟩

/-- The target may be chosen in the existing finite-edge rational
presentation format, rather than as an arbitrary relation-valued record. -/
theorem exists_presented_amalgamation {n : ℕ} (P : Fin n → Str ℚ)
    (hP : ∀ i, (P i).IsPattern) :
    ∃ (Q : Finite.RationalPresentation) (f : Fin n → ℚ → ℚ),
      Str.Amalgamation P Q.toStr f := by
  obtain ⟨Q, f, d⟩ := exists_rational_amalgamation P hP
  exact ⟨Finite.RationalPresentation.encode Q, fun i => id ∘ f i,
    d.of_rational_iso (Finite.RationalPresentation.presentation_iso Q)⟩

end Alexander313.Carlson
