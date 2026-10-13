import Alexander313.Carlson.PatternLiftingConstruction
import Alexander313.Carlson.PatternLiftingNormalization
import Alexander313.Carlson.ArithmeticLiftingExistence

/-!
# Existence of continuous minimal pattern liftings

The normalized construction transports back along the source's finite image
isomorphism. It therefore supplies a continuous pattern lifting on every
given arithmetic lifting carrier, for arbitrary ambient linear orders.
Taking the least relations preserves continuity and gives a minimal lifting.

For rational labels, arithmetic lifting existence also supplies the carrier
and the map. This proves the existence and continuity assertions of
Carlson's Lemma 12.6 in the bounded pure case. Combining this result with
the already proved transfer of cofinal validity gives Lemma 13.8's lifting
conclusion for rational patterns, without an assumed pattern lifting.

Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 49–56 and §13 of the author's October 16, 2008 manuscript.
-/

noncomputable section

namespace Alexander313.Carlson
namespace PatternLifting

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A continuous source rule lifts continuously along a continuous base
embedding, on any supplied arithmetic carrier. -/
theorem exists_continuous_of_arithmetic
    {P Pplus : Str α} {Q : Str β} {U : Finset β} {h f : α → β}
    (A : ArithmeticLifting P.U Pplus.U Q.U U h f)
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h) :
    ∃ R : Str β, R.U = U ∧ PatternLifting P Pplus Q R h f ∧ Str.Continuous Q R := by
  let D := A.normalizedData hS hQ hC hE
  have eplus := Pplus.map_isIso f A.mono
  have L : PatternLifting P Pplus Q D.candidate h f :=
    { source_pattern := hS
      target_pattern := D.candidate_isPattern
      source_sub := hC.1
      target_sub := D.candidate_target_sub
      arithmetic := A
      relations := by
        intro x hx y hy
        have hsource := D.candidate_source_sub.2 (f x) (eplus.mem hx) (f y) (eplus.mem hy)
        have himage := eplus.2.2 x hx y hy
        exact ⟨himage.1.trans hsource.1, himage.2.trans hsource.2⟩ }
  exact ⟨D.candidate, rfl, L, D.candidate_continuous⟩

/-- Lemma 12.6, pure case, on a fixed arithmetic carrier: a continuous
minimal pattern lifting exists and uses the supplied arithmetic map. -/
theorem exists_minimal_continuous_of_arithmetic
    {P Pplus : Str α} {Q : Str β} {U : Finset β} {h f : α → β}
    (A : ArithmeticLifting P.U Pplus.U Q.U U h f)
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h) :
    ∃ R : Str β, R.U = U ∧ PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.Continuous Q R := by
  obtain ⟨S, hSU, LS, hCS⟩ := exists_continuous_of_arithmetic A hS hQ hC hE
  obtain ⟨R, hRS, LR, hM, hCR⟩ := LS.exists_minimal_continuous hCS
  exact ⟨R, hRS.trans hSU, LR, hM, hCR⟩

/-- Every minimal lifting of a continuous source rule along a continuous
base embedding is continuous over the old target. -/
theorem IsMinimal.continuous_of_continuous_source
    {P Pplus : Str α} {Q Qplus : Str β} {h f : α → β}
    (hM : IsMinimal P Pplus Q Qplus h)
    (L : PatternLifting P Pplus Q Qplus h f)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h) :
    Str.Continuous Q Qplus := by
  obtain ⟨R, hU, LR, hCR⟩ :=
    exists_continuous_of_arithmetic L.arithmetic L.source_pattern L.base_target_pattern hC hE
  exact hM.continuous_of_lifting L LR hU hCR

/-- For rational labels, neither the arithmetic carrier nor the new source
map needs to be supplied. -/
theorem exists_minimal_continuous_rat
    {P Pplus Q : Str ℚ} {h : ℚ → ℚ}
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h) :
    ∃ (R : Str ℚ) (f : ℚ → ℚ), PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.Continuous Q R := by
  have hmem : ∀ x ∈ P.U, h x ∈ Q.U := by
    intro x hx
    exact hE.2.1.1 (hE.1.mem hx)
  obtain ⟨U, f, A⟩ := ArithmeticLifting.exists_rat hC.1.1 hC.2.1 hE.1.2.1 hmem
  obtain ⟨R, _, L, hM, hCR⟩ := exists_minimal_continuous_of_arithmetic A hS hQ hC hE
  exact ⟨R, f, L, hM, hCR⟩

/-- The extension point is carried to its base image in the rational
existence construction, as asserted in Lemma 12.6(3). -/
theorem exists_minimal_continuous_extensionAt_rat
    {P Pplus Q : Str ℚ} {h : ℚ → ℚ} {a : ℚ}
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h)
    (hAt : Str.ExtensionAt P Pplus a) :
    ∃ (R : Str ℚ) (f : ℚ → ℚ), PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.Continuous Q R ∧ Str.ExtensionAt Q R (h a) := by
  obtain ⟨R, f, L, hM, hCR⟩ := exists_minimal_continuous_rat hS hQ hC hE
  exact ⟨R, f, L, hM, hCR, L.extensionAt hAt⟩

/-- Cofinal validity and continuity both pass to a minimal lifting on the
given arithmetic carrier. -/
theorem exists_minimal_continuous_cofinallyValid_of_arithmetic
    {P Pplus : Str α} {Q : Str β} {U : Finset β} {h f : α → β}
    (A : ArithmeticLifting P.U Pplus.U Q.U U h f)
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h)
    (hcv : Str.CofinallyValid P Pplus) :
    ∃ R : Str β, R.U = U ∧ PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.Continuous Q R ∧ Str.CofinallyValid Q R := by
  obtain ⟨R, hU, L, hM, hCR⟩ := exists_minimal_continuous_of_arithmetic A hS hQ hC hE
  exact ⟨R, hU, L, hM, hCR, L.cofinallyValid hM hcv⟩

/-- Lemma 13.8's lifting conclusion for rational pure patterns: a
continuous, cofinally valid source rule has a continuous, cofinally valid
minimal lifting along every continuous base embedding. -/
theorem exists_minimal_continuous_cofinallyValid_rat
    {P Pplus Q : Str ℚ} {h : ℚ → ℚ}
    (hS : Pplus.IsPattern) (hQ : Q.IsPattern)
    (hC : Str.Continuous P Pplus) (hE : Str.ContinuousEmbedding P Q h)
    (hcv : Str.CofinallyValid P Pplus) :
    ∃ (R : Str ℚ) (f : ℚ → ℚ), PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.Continuous Q R ∧ Str.CofinallyValid Q R := by
  obtain ⟨R, f, L, hM, hCR⟩ := exists_minimal_continuous_rat hS hQ hC hE
  exact ⟨R, f, L, hM, hCR, L.cofinallyValid hM hcv⟩

end PatternLifting
end Alexander313.Carlson
