import Alexander313.Carlson.CoveringEnumeration

/-!
# Extending a prescribed covering on an initial finite block

An increasing bijection between two finite linear orders carries equally sized
initial blocks onto each other. Consequently an indexed covering of a finite
structure can be chosen to agree with a prescribed increasing map on its initial
block, when the target of that block lies below every remaining target point.

This is the finite order argument needed to turn a cofinal copy of an indexed
structure into an extension of an already prescribed covering map.
-/

noncomputable section

namespace Alexander313.Carlson.Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- An indexed covering extends the prescribed increasing map on an initial
block. Every remaining source point lands in the separated remaining target
block. The target type is nonempty so the covering has values off the finite
source carrier. -/
theorem exists_covering_extension_of_coversStructure [Nonempty β]
    {A : Str α} {X : Finset α} {Y : Finset β} {h : α → β}
    {S₁ S₂ : β → β → Prop}
    (hX : X ⊆ A.U)
    (hsource : ∀ x ∈ X, ∀ z ∈ A.U, z ∉ X → x < z)
    (hmono : ∀ x ∈ X, ∀ y ∈ X, x < y → h x < h y)
    (htarget : ∀ x ∈ X, ∀ y ∈ Y, h x < y)
    (hc : CoversStructure S₁ S₂ (X.image h ∪ Y) A.indexedFirst A.indexedSecond) :
    ∃ f : α → β, IsCovering A S₁ S₂ f ∧ (∀ x ∈ X, f x = h x) ∧
      (∀ z ∈ A.U, z ∉ X → f z ∈ Y) := by
  classical
  obtain ⟨f, himage, hf⟩ := exists_covering_of_coversStructure (P := A) hc
  have hfX : ∀ x ∈ X, ∀ y ∈ X, x < y → f x < f y :=
    fun x hx y hy hxy => hf.1 x (hX hx) y (hX hy) hxy
  have hcardf : (X.image f).card = X.card := card_image_of_mono X f hfX
  have hcardh : (X.image h).card = X.card := card_image_of_mono X h hmono
  have hcards : (X.image f).card = (X.image h).card := hcardf.trans hcardh.symm
  have hsubset : X.image f ⊆ X.image h := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    by_contra hnot
    have hfx : f x ∈ X.image h ∪ Y := by
      rw [← himage]
      exact Finset.mem_image_of_mem f (hX hx)
    have hfxY : f x ∈ Y := (Finset.mem_union.mp hfx).resolve_left hnot
    have hsubset' : X.image h ⊆ X.image f := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      have hhu : h u ∈ A.U.image f := by
        rw [himage]
        exact Finset.mem_union_left Y (Finset.mem_image_of_mem h hu)
      obtain ⟨z, hz, hzf⟩ := Finset.mem_image.mp hhu
      by_cases hzX : z ∈ X
      · have hzmem : f z ∈ X.image f := Finset.mem_image_of_mem f hzX
        rwa [hzf] at hzmem
      · have hsmall : f z < f x := by
          rw [hzf]
          exact htarget u hu (f x) hfxY
        have hlarge : f x < f z :=
          hf.1 x (hX hx) z hz (hsource x hx z hz hzX)
        exact (lt_asymm hlarge hsmall).elim
    have hsame : X.image h = X.image f :=
      Finset.eq_of_subset_of_card_le hsubset' hcards.le
    apply hnot
    rw [hsame]
    exact Finset.mem_image_of_mem f hx
  have hprefix : X.image f = X.image h :=
    Finset.eq_of_subset_of_card_le hsubset hcards.ge
  have hfenum : (fun i : Fin X.card => f (X.orderEmbOfFin rfl i)) =
      (X.image h).orderEmbOfFin hcardh := by
    apply Finset.orderEmbOfFin_unique hcardh
    · intro i
      rw [← hprefix]
      exact Finset.mem_image_of_mem f (X.orderEmbOfFin_mem rfl i)
    · intro i j hij
      exact hfX _ (X.orderEmbOfFin_mem rfl i) _ (X.orderEmbOfFin_mem rfl j)
        ((X.orderEmbOfFin rfl).strictMono hij)
  have hfix : ∀ x ∈ X, f x = h x := by
    intro x hx
    let i : Fin X.card := (X.orderIsoOfFin rfl).symm ⟨x, hx⟩
    have hei : X.orderEmbOfFin rfl i = x :=
      congrArg Subtype.val ((X.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    calc
      f x = f (X.orderEmbOfFin rfl i) := congrArg f hei.symm
      _ = (X.image h).orderEmbOfFin hcardh i := congrFun hfenum i
      _ = h (X.orderEmbOfFin rfl i) := orderEmbOfFin_image X h hmono rfl hcardh i
      _ = h x := congrArg h hei
  refine ⟨f, hf, hfix, ?_⟩
  intro z hz hzX
  have hfz : f z ∈ X.image h ∪ Y := by
    rw [← himage]
    exact Finset.mem_image_of_mem f hz
  rcases Finset.mem_union.mp hfz with hfz | hfz
  · obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hfz
    have hlt : f x < f z := hf.1 x (hX hx) z hz (hsource x hx z hz hzX)
    exact (hlt.ne ((hfix x hx).trans hxz)).elim
  · exact hfz

end Alexander313.Carlson.Str
