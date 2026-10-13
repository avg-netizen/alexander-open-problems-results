import Alexander313.Carlson.UpwardCofinality
import Alexander313.Carlson.DownwardExistence

/-!
# Existence of upward reflections on rational labels

An upward reflection copies the new block of a continuous extension at `a`
to just below `b`. On rational labels this placement always exists. Translate
the original block into an interval starting at `b`, apply the finite-copy
construction from `DownwardExistence`, and undo the translation in the matching
map.

`UpData.exists_rat` constructs the placement from the source extension and
`a <₂ b`. `exists_upward_extension_rat` supplies the resulting pattern and
continuous extension at `b`. The new structure has exactly as many points as
the source extension. `exists_cofinally_valid_upward_extension_rat` also
preserves cofinal validity of the source rule, using Lemma 10.3.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

namespace UpData

variable {α : Type*} [LinearOrder α]
variable {P Q : Str α} {a b : α} {N : Finset α} {g : α → α}

/-- The copied block has the same size as the source extension's new block. -/
theorem card_new (D : UpData P Q a b N g) : N.card = (Q.U \ P.U).card := by
  classical
  have hinj : Set.InjOn g N := by
    intro x hx y hy hxy
    exact le_antisymm ((D.g_le_iff hx hy).mp hxy.le) ((D.g_le_iff hy hx).mp hxy.ge)
  calc
    N.card = (N.image g).card := (Finset.card_image_iff.mpr hinj).symm
    _ = (Q.U \ P.U).card := congrArg Finset.card D.himage

/-- Upward reflection preserves the cardinality of the source extension. -/
theorem card_universe (D : UpData P Q a b N g) :
    (P.upward Q a b N g).U.card = Q.U.card := by
  classical
  have hdisj : Disjoint P.U N := Finset.disjoint_left.mpr (fun n hnP hnN => D.hNP n hnN hnP)
  change (P.U ∪ N).card = Q.U.card
  calc
    (P.U ∪ N).card = P.U.card + (Q.U \ P.U).card := by
      rw [Finset.card_union_of_disjoint hdisj, D.card_new]
    _ = (Q.U \ P.U).card + P.U.card := Nat.add_comm _ _
    _ = (Q.U ∪ P.U).card := Finset.card_sdiff_add_card Q.U P.U
    _ = Q.U.card := by rw [Finset.union_eq_left.mpr D.cont.1.1]

/-- The source hypotheses suffice to place an upward copy on rational labels. -/
theorem exists_rat {P Q : Str ℚ} {a b : ℚ}
    (hQ : Q.IsPattern) (hcont : Continuous P Q) (hext : ExtensionAt P Q a)
    (hb : b ∈ P.U) (hab : a < b) (hrel : P.r₂ a b) :
    ∃ (N : Finset ℚ) (g : ℚ → ℚ), UpData P Q a b N g := by
  classical
  let X := Q.U \ P.U
  have hXne : X.Nonempty := by
    obtain ⟨x, hxQ, hxP⟩ := hext.2.2.1
    exact ⟨x, Finset.mem_sdiff.mpr ⟨hxQ, hxP⟩⟩
  have hXa (x : ℚ) (hx : x ∈ X) : x < a := by
    obtain ⟨hxQ, hxP⟩ := Finset.mem_sdiff.mp hx
    exact (hext.2.2.2 x hxQ hxP).2.1
  let m := X.min' hXne
  have hma : m < a := hXa m (X.min'_mem hXne)
  let f : ℚ → ℚ := fun x => b + (x - m)
  let c : ℚ := b + (a - m)
  let Y := X.image f
  have hbc : b < c := by
    dsimp only [c]
    linarith
  have hY (y : ℚ) (hy : y ∈ Y) : b ≤ y ∧ y < c := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hmx : m ≤ x := X.min'_le x hx
    have hxa : x < a := hXa x hx
    change b ≤ b + (x - m) ∧ b + (x - m) < b + (a - m)
    constructor <;> linarith
  obtain ⟨N, g', hbelow, himage, hmono⟩ := exists_copy_justBelow_rat P.U Y hb hbc hY
  let g : ℚ → ℚ := fun n => m + (g' n - b)
  have hundo (x : ℚ) : m + (f x - b) = x := by
    dsimp only [f]
    ring
  refine ⟨N, g, hQ, hcont, hext, hb, hab, hrel, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (hbelow n hn).not_mem
  · intro n hn
    exact (hbelow n hn).2.1
  · intro n hn
    exact (hbelow n hn).2.2
  · change N.image g = X
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hgn : g' n ∈ Y := by
        rw [← himage]
        exact Finset.mem_image_of_mem g' hn
      obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp hgn
      change m + (g' n - b) ∈ X
      rw [← hzg, hundo]
      exact hz
    · intro hx
      have hfx : f x ∈ N.image g' := by
        rw [himage]
        exact Finset.mem_image_of_mem f hx
      obtain ⟨n, hn, hnfx⟩ := Finset.mem_image.mp hfx
      refine Finset.mem_image.mpr ⟨n, hn, ?_⟩
      change m + (g' n - b) = x
      rw [hnfx, hundo]
  · intro x hx y hy hxy
    change m + (g' x - b) < m + (g' y - b)
    have hxy' := hmono x hx y hy hxy
    linarith

end UpData

/-- Every eligible continuous extension on rational labels admits an upward
reflection, with the same number of points, as a continuous extension at `b`. -/
theorem exists_upward_extension_rat {P Q : Str ℚ} {a b : ℚ}
    (hQ : Q.IsPattern) (hcont : Continuous P Q) (hext : ExtensionAt P Q a)
    (hb : b ∈ P.U) (hab : a < b) (hrel : P.r₂ a b) :
    ∃ R : Str ℚ, R.IsPattern ∧ Continuous P R ∧ ExtensionAt P R b ∧
      R.U.card = Q.U.card := by
  obtain ⟨N, g, D⟩ := UpData.exists_rat hQ hcont hext hb hab hrel
  exact ⟨P.upward Q a b N g, D.isPattern, D.continuous, D.extensionAt, D.card_universe⟩

/-- A cofinally valid continuous extension on rational labels admits an
upward reflection that is again cofinally valid and continuous, with the same
number of points as the source extension. -/
theorem exists_cofinally_valid_upward_extension_rat {P Q : Str ℚ} {a b : ℚ}
    (hQ : Q.IsPattern) (hcont : Continuous P Q) (hext : ExtensionAt P Q a)
    (hb : b ∈ P.U) (hab : a < b) (hrel : P.r₂ a b) (hcv : CofinallyValid P Q) :
    ∃ R : Str ℚ, R.IsPattern ∧ Continuous P R ∧ ExtensionAt P R b ∧
      CofinallyValid P R ∧ R.U.card = Q.U.card := by
  obtain ⟨N, g, D⟩ := UpData.exists_rat hQ hcont hext hb hab hrel
  exact ⟨P.upward Q a b N g, D.isPattern, D.continuous, D.extensionAt,
    D.cofinallyValid hcv, D.card_universe⟩

end Str

end Alexander313.Carlson
