import Alexander313.Carlson.Core

/-!
# The common initial segment is Carlson's isominimal core

The core is originally defined as the union of finite isominimal induced
ordinal substructures. Pointwise least seed copies are isominimal by the
existing realization theorem. Conversely, relabel a finite isominimal
ordinal set by rational ranks and take its least exact copy. The new copy
is pointwise below the original, so isominimality makes the carriers equal.
-/

noncomputable section

namespace Alexander313.Carlson

/-- Isominimality of an induced finite ordinal substructure, in the
pointwise order on its increasing labels. -/
def IsominimalOrdinalSet (U : Finset Ordinal.{0}) : Prop :=
  ∀ (T : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}),
    Str.IsIso (Str.ofOrdinals U) (Str.ofOrdinals T) f →
    (∀ z ∈ U, f z ≤ z) → T = U

/-- Any finite ordinal carrier admits an exact change to rational ranks. -/
def ordinalRationalRelabeling (U : Finset Ordinal.{0}) : FiniteRelabeling U ℚ := by
  classical
  let index (z : Ordinal.{0}) (hz : z ∈ U) := (U.orderIsoOfFin rfl).symm ⟨z, hz⟩
  let f (z : Ordinal.{0}) : ℚ := if hz : z ∈ U then (index z hz).val else 0
  have hf (z : Ordinal.{0}) (hz : z ∈ U) : f z = ((index z hz).val : ℚ) := by
    simp only [f, hz, ↓reduceDIte]
  have mono : ∀ x ∈ U, ∀ y ∈ U, x < y → f x < f y := by
    intro x hx y hy hxy
    rw [hf x hx, hf y hy]
    exact Nat.cast_lt.mpr ((U.orderIsoOfFin rfl).symm.strictMono hxy)
  have inj : ∀ x ∈ U, ∀ y ∈ U, f x = f y → x = y := by
    intro x hx y hy heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (mono x hx y hy hlt).ne heq
    · exact (mono y hy x hx hlt).ne heq.symm
  let g (y : ℚ) : Ordinal.{0} :=
    if hy : y ∈ U.image f then Classical.choose (Finset.mem_image.mp hy) else 0
  refine ⟨f, g, ?_, mono⟩
  intro z hz
  have hm : f z ∈ U.image f := Finset.mem_image_of_mem f hz
  have hs := Classical.choose_spec (Finset.mem_image.mp hm)
  change g (f z) = z
  simp only [g, hm, ↓reduceDIte]
  exact inj _ hs.1 z hz hs.2

theorem corePoint_iff_isominimal (a : Ordinal.{0}) :
    CorePoint a ↔ ∃ U : Finset Ordinal.{0}, a ∈ U ∧ IsominimalOrdinalSet U := by
  constructor
  · rintro ⟨P, x, hx, heq⟩
    let A := coreRealization P
    let U := (A.ordinal.stagePattern 0).U
    have hx₀ : x ∈ (A.sequence.stage 0).U := by
      simpa only [A.seed, Finite.RationalPresentation.toStr_U] using hx
    have ha : a ∈ U := by
      rw [← heq]
      exact Finset.mem_image_of_mem A.label hx₀
    refine ⟨U, ha, fun T f e hle => ?_⟩
    exact A.ordinal.stage_isominimal 0 e hle
  · rintro ⟨U, ha, hminimal⟩
    let F := ordinalRationalRelabeling U
    let P := Str.ofOrdinals U
    let Q := P.map F.toFun
    have e : Str.IsIso P Q F.toFun := F.isIso (Finset.Subset.refl U)
    have eback : Str.IsIso Q P F.invFun := F.inverse_isIso (Finset.Subset.refl U)
    obtain ⟨h, eh, hcore, hleast⟩ := exists_minimal_copy_in_core Q
      (e.isPattern (Str.ofOrdinals_isPattern U))
    have hg : Q.CoveringR F.invFun :=
      ⟨eback.2.1, fun x hx y hy => (eback.2.2 x hx y hy).1.mp,
        fun x hx y hy => (eback.2.2 x hx y hy).2.mp⟩
    let k := h ∘ F.toFun
    let T := U.image k
    have ek : Str.IsIso P (Str.ofOrdinals T) k := by
      refine ⟨rfl, ?_, ?_⟩
      · intro x hx y hy hxy
        exact eh.2.1 _ (e.mem hx) _ (e.mem hy) (e.2.1 x hx y hy hxy)
      · intro x hx y hy
        have e₁ := e.2.2 x hx y hy
        have e₂ := eh.2.2 _ (e.mem hx) _ (e.mem hy)
        exact ⟨e₁.1.trans e₂.1, e₁.2.trans e₂.2⟩
    have hle : ∀ z ∈ U, k z ≤ z := by
      intro z hz
      have h := hleast F.invFun hg (F.toFun z) (e.mem hz)
      simpa only [k, Function.comp_apply, F.left_inv z hz] using h
    have hT : T = U := hminimal T k ek hle
    have haT : a ∈ T := hT.symm ▸ ha
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp haT
    apply (corePoint_iff_lt_coreBound a).mpr
    rw [← heq]
    exact hcore _ (e.mem hz)

/-- Carlson's core, defined as the union of its isominimal finite
substructures, is the countable initial segment `[0, coreBound)`. -/
theorem isominimal_core_iff_lt (a : Ordinal.{0}) :
    (∃ U : Finset Ordinal.{0}, a ∈ U ∧ IsominimalOrdinalSet U) ↔ a < coreBound :=
  (corePoint_iff_isominimal a).symm.trans (corePoint_iff_lt_coreBound a)

end Alexander313.Carlson
