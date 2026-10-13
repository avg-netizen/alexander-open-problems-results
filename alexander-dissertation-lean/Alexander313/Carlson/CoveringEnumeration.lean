import Alexander313.Carlson.Patterns

/-!
# Finite coverings and their increasing enumerations

The semantic second relation uses `CoversStructure`, whose source relations
are indexed by `Fin n`. Pattern rules instead use maps on a finite carrier.
This file proves that the two representations give exactly the same
coverings, with the target set equal to the image of the covering map.

This is the enumeration bridge needed to apply the cofinal-copy clause of
Carlson's Definition 5.3 to finite pattern rules, as in Lemma 10.3 of
*Patterns of resemblance of order 2*.
-/

noncomputable section

namespace Alexander313.Carlson.Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- The first relation of a finite structure on its increasing enumeration. -/
def indexedFirst (P : Str α) (i j : Fin P.U.card) : Prop :=
  P.r₁ (P.U.orderEmbOfFin rfl i) (P.U.orderEmbOfFin rfl j)

/-- The second relation of a finite structure on its increasing enumeration. -/
def indexedSecond (P : Str α) (i j : Fin P.U.card) : Prop :=
  P.r₂ (P.U.orderEmbOfFin rfl i) (P.U.orderEmbOfFin rfl j)

/-- The image of a covering realizes the indexed source structure. -/
theorem IsCovering.coversStructure_image {P : Str α} {S₁ S₂ : β → β → Prop}
    {h : α → β} (hh : IsCovering P S₁ S₂ h) :
    CoversStructure S₁ S₂ (P.U.image h) P.indexedFirst P.indexedSecond := by
  have hcard : (P.U.image h).card = P.U.card := card_image_of_mono P.U h hh.1
  refine ⟨hcard, fun i j => ?_⟩
  rw [orderEmbOfFin_image P.U h hh.1 rfl hcard i,
    orderEmbOfFin_image P.U h hh.1 rfl hcard j]
  exact ⟨fun hij => hh.2.1 _ (P.U.orderEmbOfFin_mem rfl i)
      _ (P.U.orderEmbOfFin_mem rfl j) hij,
    fun hij => hh.2.2 _ (P.U.orderEmbOfFin_mem rfl i)
      _ (P.U.orderEmbOfFin_mem rfl j) hij⟩

/-- An indexed finite covering yields a covering map with exactly that image.
Nonemptiness of the target type supplies values off the finite source carrier. -/
theorem exists_covering_of_coversStructure [Nonempty β] {P : Str α}
    {S₁ S₂ : β → β → Prop} {T : Finset β}
    (hc : CoversStructure S₁ S₂ T P.indexedFirst P.indexedSecond) :
    ∃ h : α → β, P.U.image h = T ∧ IsCovering P S₁ S₂ h := by
  classical
  obtain ⟨hcard, hrel⟩ := hc
  let index : P.U → Fin P.U.card := (P.U.orderIsoOfFin rfl).symm
  have index_value (x : α) (hx : x ∈ P.U) :
      P.U.orderEmbOfFin rfl (index ⟨x, hx⟩) = x :=
    congrArg Subtype.val ((P.U.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
  have index_enum (i : Fin P.U.card) :
      index ⟨P.U.orderEmbOfFin rfl i, P.U.orderEmbOfFin_mem rfl i⟩ = i := by
    change (P.U.orderIsoOfFin rfl).symm ((P.U.orderIsoOfFin rfl) i) = i
    exact (P.U.orderIsoOfFin rfl).symm_apply_apply i
  let h : α → β := fun x =>
    if hx : x ∈ P.U then T.orderEmbOfFin hcard (index ⟨x, hx⟩)
    else Classical.choice (inferInstance : Nonempty β)
  have h_mem (x : α) (hx : x ∈ P.U) :
      h x = T.orderEmbOfFin hcard (index ⟨x, hx⟩) := by
    simp only [h, dif_pos hx]
  have h_enum (i : Fin P.U.card) :
      h (P.U.orderEmbOfFin rfl i) = T.orderEmbOfFin hcard i := by
    rw [h_mem _ (P.U.orderEmbOfFin_mem rfl i), index_enum]
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [h_mem x hx]
      exact T.orderEmbOfFin_mem hcard _
    · intro hy
      let i : Fin P.U.card := (T.orderIsoOfFin hcard).symm ⟨y, hy⟩
      refine Finset.mem_image.mpr ⟨P.U.orderEmbOfFin rfl i,
        P.U.orderEmbOfFin_mem rfl i, ?_⟩
      rw [h_enum]
      exact congrArg Subtype.val ((T.orderIsoOfFin hcard).apply_symm_apply ⟨y, hy⟩)
  · intro x hx y hy hxy
    rw [h_mem x hx, h_mem y hy]
    exact (T.orderEmbOfFin hcard).strictMono
      ((P.U.orderIsoOfFin rfl).symm.strictMono (show (⟨x, hx⟩ : P.U) < ⟨y, hy⟩ from hxy))
  · intro x hx y hy hxy
    rw [h_mem x hx, h_mem y hy]
    apply (hrel (index ⟨x, hx⟩) (index ⟨y, hy⟩)).1
    change P.r₁ (P.U.orderEmbOfFin rfl (index ⟨x, hx⟩))
      (P.U.orderEmbOfFin rfl (index ⟨y, hy⟩))
    rwa [index_value, index_value]
  · intro x hx y hy hxy
    rw [h_mem x hx, h_mem y hy]
    apply (hrel (index ⟨x, hx⟩) (index ⟨y, hy⟩)).2
    change P.r₂ (P.U.orderEmbOfFin rfl (index ⟨x, hx⟩))
      (P.U.orderEmbOfFin rfl (index ⟨y, hy⟩))
    rwa [index_value, index_value]

/-- Equivalence of the indexed and finite-carrier descriptions of a covering. -/
theorem coversStructure_iff [Nonempty β] (P : Str α) (S₁ S₂ : β → β → Prop)
    (T : Finset β) :
    CoversStructure S₁ S₂ T P.indexedFirst P.indexedSecond ↔
      ∃ h : α → β, P.U.image h = T ∧ IsCovering P S₁ S₂ h := by
  constructor
  · exact exists_covering_of_coversStructure
  · rintro ⟨h, rfl, hh⟩
    exact hh.coversStructure_image

end Alexander313.Carlson.Str
