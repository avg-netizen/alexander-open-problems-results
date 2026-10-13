import Alexander313.Carlson.SemanticTransport
import Alexander313.Carlson.ReflectionConditions

/-!
# Reflection conditions in an initial segment

The intrinsic finite-copy conditions at two points below `o` have the
same meaning in the initial segment `Set.Iio o` and in the ambient linear
order. Every finite source is already below the upper endpoint, every
downward image is below the lower endpoint, and every cofinal-copy image
is below its specified endpoint. Thus all witnesses remain in the segment.

The proofs work for arbitrary relations and linear orders. Specializing
them to Carlson's ordinal relations gives the intrinsic first and second
reflection equations on every ordinal initial segment.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α : Type*} [LinearOrder α] {S₁ S₂ : α → α → Prop} {o : α}

private theorem image_Iio_subtype (F : Finset α) (hF : ∀ z ∈ F, z < o) :
    (F.subtype (· ∈ Set.Iio o)).image Subtype.val = F := by
  classical
  simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
    (Finset.subtype_map_of_mem (show ∀ z ∈ F, z ∈ Set.Iio o from hF))

/-- A finite ambient copy whose target is below `o` lifts to the initial
segment. The lifted map agrees with the original map on the finite source. -/
theorem CoveringCopy.exists_Iio_lift {F : Finset (Set.Iio o)} {f : α → α}
    {a : Set.Iio o}
    (h : CoveringCopy S₁ S₂ (F.image Subtype.val) f a.val) :
    ∃ g : Set.Iio o → Set.Iio o,
      CoveringCopy (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) F g a ∧
      ∀ z ∈ F, (g z).val = f z.val := by
  classical
  have hmem (z : Set.Iio o) (hz : z ∈ F) : z.val ∈ F.image Subtype.val :=
    Finset.mem_image_of_mem Subtype.val hz
  let g : Set.Iio o → Set.Iio o := fun z =>
    if hz : z ∈ F then ⟨f z.val, (h.1 z.val (hmem z hz)).trans a.property⟩ else z
  have hg (z : Set.Iio o) (hz : z ∈ F) : (g z).val = f z.val := by
    simp only [g, dif_pos hz]
  refine ⟨g, ⟨?_, ?_, ?_, ?_, ?_⟩, hg⟩
  · intro z hz
    change (g z).val < a.val
    rw [hg z hz]
    exact h.1 z.val (hmem z hz)
  · intro z hz hza
    apply Subtype.ext
    rw [hg z hz]
    exact h.2.1 z.val (hmem z hz) hza
  · intro z hz w hw hzw
    change (g z).val < (g w).val
    rw [hg z hz, hg w hw]
    exact h.2.2.1 z.val (hmem z hz) w.val (hmem w hw) hzw
  · intro z hz w hw hzw
    rw [hg z hz, hg w hw]
    exact h.2.2.2.1 z.val (hmem z hz) w.val (hmem w hw) hzw
  · intro z hz w hw hzw
    rw [hg z hz, hg w hw]
    exact h.2.2.2.2 z.val (hmem z hz) w.val (hmem w hw) hzw

/-- A finite copy in an initial segment extends to an ambient map. Only
its values on the segment matter for the covering and linking conditions. -/
theorem CoveringCopy.exists_Iio_extension {F : Finset (Set.Iio o)}
    {f : Set.Iio o → Set.Iio o} {a : Set.Iio o}
    (h : CoveringCopy (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) F f a) :
    ∃ g : α → α, CoveringCopy S₁ S₂ (F.image Subtype.val) g a.val ∧
      ∀ z : Set.Iio o, g z.val = (f z).val := by
  classical
  let g : α → α := fun z => if hz : z ∈ Set.Iio o then (f ⟨z, hz⟩).val else z
  have hg (z : Set.Iio o) : g z.val = (f z).val := by
    simp only [g, dif_pos z.property]
  refine ⟨g, ⟨?_, ?_, ?_, ?_, ?_⟩, hg⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [hg x]
    exact h.1 x hx
  · intro z hz hza
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [hg x]
    exact congrArg Subtype.val (h.2.1 x hx hza)
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [hg x, hg y]
    exact h.2.2.1 x hx y hy hzw
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [hg x, hg y]
    exact h.2.2.2.1 x hx y hy hzw
  · intro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [hg x, hg y]
    exact h.2.2.2.2 x hx y hy hzw

/-- Linked finite copies are unchanged when interpreted in an initial
segment containing both endpoints. No assumptions on the predicates are needed. -/
theorem linkedCondition_Iio_iff {upper lower : α → Prop} (a b : Set.Iio o) :
    LinkedCondition (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val)
        (fun x => upper x.val) (fun x => lower x.val) a b ↔
      LinkedCondition S₁ S₂ upper lower a.val b.val := by
  classical
  constructor
  · intro h F hF
    have hFo : ∀ z ∈ F, z < o := fun z hz => (hF z hz).trans b.property
    let G := F.subtype (· ∈ Set.Iio o)
    have hG (z : Set.Iio o) : z ∈ G ↔ z.val ∈ F := Finset.mem_subtype
    have himage : G.image Subtype.val = F := image_Iio_subtype F hFo
    obtain ⟨f, hf, hlink⟩ := h G (fun z hz => hF z.val ((hG z).mp hz))
    obtain ⟨g, hg, hval⟩ := hf.exists_Iio_extension
    rw [himage] at hg
    refine ⟨g, hg, ?_⟩
    intro z hz haz huz
    let x : Set.Iio o := ⟨z, hFo z hz⟩
    rw [hval x]
    exact hlink x ((hG x).mpr hz) haz huz
  · intro h F hF
    have hbelow : ∀ z ∈ F.image Subtype.val, z < b.val := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact hF x hx
    obtain ⟨f, hf, hlink⟩ := h (F.image Subtype.val) hbelow
    obtain ⟨g, hg, hval⟩ := hf.exists_Iio_lift
    refine ⟨g, hg, ?_⟩
    intro z hz haz huz
    rw [hval z hz]
    exact hlink z.val (Finset.mem_image_of_mem Subtype.val hz) haz huz

/-- The first finite-copy condition is unchanged on an initial segment. -/
theorem firstCondition_Iio_iff (a b : Set.Iio o) :
    FirstCondition (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) a b ↔
      FirstCondition S₁ S₂ a.val b.val := by
  simpa [LinkedCondition, FirstCondition] using
    (linkedCondition_Iio_iff (S₁ := S₁) (S₂ := S₂)
      (upper := fun _ => False) (lower := fun _ => False) a b)

/-- Cofinal indexed copies in an initial segment correspond exactly to
ambient copies of the image of their fixed finite block. -/
theorem cofinalCopies_Iio_iff (X : Finset (Set.Iio o)) {n : ℕ}
    (P₁ P₂ : Fin n → Fin n → Prop) (c : Set.Iio o) :
    CofinalCopies (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) X P₁ P₂ c ↔
      CofinalCopies S₁ S₂ (X.image Subtype.val) P₁ P₂ c.val := by
  classical
  constructor
  · intro h ξ hξ
    let x : Set.Iio o := ⟨ξ, hξ.trans c.property⟩
    obtain ⟨Y, hY, hcover⟩ := h x hξ
    refine ⟨Y.image Subtype.val, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact hY y hy
    · have hc := (coversStructure_subtype_val_iff (X ∪ Y) P₁ P₂).mp hcover
      rw [Finset.image_union] at hc
      exact hc
  · intro h ξ hξ
    obtain ⟨Y, hY, hcover⟩ := h ξ.val hξ
    have hYo : ∀ y ∈ Y, y < o := fun y hy => (hY y hy).2.trans c.property
    let Z := Y.subtype (· ∈ Set.Iio o)
    have hZ (z : Set.Iio o) : z ∈ Z ↔ z.val ∈ Y := Finset.mem_subtype
    have himage : Z.image Subtype.val = Y := image_Iio_subtype Y hYo
    refine ⟨Z, fun z hz => hY z.val ((hZ z).mp hz), ?_⟩
    apply (coversStructure_subtype_val_iff (X ∪ Z) P₁ P₂).mpr
    rw [Finset.image_union, himage]
    exact hcover

/-- The implication between cofinal-copy conditions is unchanged on an
initial segment containing its endpoints. -/
theorem cofinalCondition_Iio_iff (a b : Set.Iio o) :
    CofinalCondition (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) a b ↔
      CofinalCondition S₁ S₂ a.val b.val := by
  classical
  constructor
  · intro h X hX n P₁ P₂ hcof
    have hXo : ∀ z ∈ X, z < o := fun z hz => (hX z hz).trans a.property
    let Z := X.subtype (· ∈ Set.Iio o)
    have hZ (z : Set.Iio o) : z ∈ Z ↔ z.val ∈ X := Finset.mem_subtype
    have himage : Z.image Subtype.val = X := image_Iio_subtype X hXo
    have hc : CofinalCopies (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val)
        Z P₁ P₂ a := by
      apply (cofinalCopies_Iio_iff Z P₁ P₂ a).mpr
      rw [himage]
      exact hcof
    have hres := h Z (fun z hz => hX z.val ((hZ z).mp hz)) n P₁ P₂ hc
    have hres' := (cofinalCopies_Iio_iff Z P₁ P₂ b).mp hres
    rw [himage] at hres'
    exact hres'
  · intro h X hX n P₁ P₂ hcof
    have hbelow : ∀ z ∈ X.image Subtype.val, z < a.val := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact hX x hx
    apply (cofinalCopies_Iio_iff X P₁ P₂ b).mpr
    exact h (X.image Subtype.val) hbelow n P₁ P₂
      ((cofinalCopies_Iio_iff X P₁ P₂ a).mp hcof)

/-- Both intrinsic second-relation clauses are unchanged on an initial segment. -/
theorem secondCondition_Iio_iff (a b : Set.Iio o) :
    SecondCondition (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) a b ↔
      SecondCondition S₁ S₂ a.val b.val := by
  unfold SecondCondition
  exact and_congr Iff.rfl (and_congr
    (linkedCondition_Iio_iff (S₁ := S₁) (S₂ := S₂)
      (upper := fun y => S₁ y b.val) (lower := fun y => S₁ y a.val) a b)
    (cofinalCondition_Iio_iff a b))

/-- The global ordinal first relation obeys its intrinsic finite-copy
equation inside any ordinal initial segment. -/
theorem R1_Iio_iff_firstCondition {o : Ordinal.{0}} (a b : Set.Iio o) :
    R1 a.val b.val ↔ a ≤ b ∧
      FirstCondition (fun x y : Set.Iio o => R1 x.val y.val)
        (fun x y : Set.Iio o => R2 x.val y.val) a b := by
  rw [firstCondition_Iio_iff]
  exact R1_iff_firstCondition a.val b.val

/-- The global ordinal second relation obeys both intrinsic reflection
clauses inside any ordinal initial segment. -/
theorem R2_Iio_iff_secondCondition {o : Ordinal.{0}} (a b : Set.Iio o) :
    R2 a.val b.val ↔
      SecondCondition (fun x y : Set.Iio o => R1 x.val y.val)
        (fun x y : Set.Iio o => R2 x.val y.val) a b := by
  rw [secondCondition_Iio_iff]
  exact R2_iff_secondCondition a.val b.val

end Alexander313.Carlson
