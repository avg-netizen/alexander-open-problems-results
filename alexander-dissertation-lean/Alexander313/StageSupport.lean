import Mathlib.Data.Finset.Max

/-!
# Soundness by finite label support

Empty support is handled separately. The proof uses a greatest point of
each nonempty finite support, never a computable rank for the hierarchy.
The generator step must still be established from the concrete generator
table, transport, reconstruction and ordinal library.
-/

namespace Alexander313

def CutSound {Label Statement : Type} [LinearOrder Label]
    (support : Statement → Finset Label) (generator : Statement → Prop)
    (holds : Statement → Prop) (ν : Label) : Prop :=
  ∀ σ, generator σ → (∀ x ∈ support σ, x < ν) → holds σ

theorem finite_support_soundness {Label Statement : Type} [LinearOrder Label]
    (wf : WellFounded ((· < ·) : Label → Label → Prop))
    (support : Statement → Finset Label) (generator : Statement → Prop)
    (holds : Statement → Prop)
    (empty : ∀ σ, generator σ → support σ = ∅ → holds σ)
    (step : ∀ ν, CutSound support generator holds ν →
      ∀ σ, generator σ → ν ∈ support σ →
        (∀ x ∈ support σ, x ≤ ν) → holds σ) :
    ∀ σ, generator σ → holds σ := by
  classical
  have cuts : ∀ ν, CutSound support generator holds ν := by
    intro ν
    induction ν using wf.induction with
    | h ν ih =>
      intro σ hgen hbelow
      by_cases hempty : support σ = ∅
      · exact empty σ hgen hempty
      · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (support σ) id
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        exact step m (ih m (hbelow m hm)) σ hgen hm hmax
  intro σ hgen
  by_cases hempty : support σ = ∅
  · exact empty σ hgen hempty
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (support σ) id
      (Finset.nonempty_iff_ne_empty.mpr hempty)
    exact step m (cuts m) σ hgen hm hmax

end Alexander313
