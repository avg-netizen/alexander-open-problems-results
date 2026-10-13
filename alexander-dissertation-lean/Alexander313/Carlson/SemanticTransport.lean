import Alexander313.Carlson.PatternTransport

/-!
# Transport of finite semantic coverings and reflection conditions

Increasing finite images preserve the indexed covering conditions used in
the ordinal semantics. The statements keep relation hypotheses on the
finite carrier and therefore impose no restrictions away from that carrier.
Order isomorphisms that identify both relations transport the first, linked,
and cofinal reflection conditions. Finite isomorphisms also admit total
inverses whose inverse laws hold on their carriers.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- A strictly increasing finite image carries indexed coverings forward,
even when the source and target ambient types differ. -/
theorem CoversStructure.image {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {F : Finset α} {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop}
    (h : CoversStructure S₁ S₂ F P₁ P₂) (f : α → β)
    (mono : ∀ x ∈ F, ∀ y ∈ F, x < y → f x < f y)
    (rel₁ : ∀ x ∈ F, ∀ y ∈ F, S₁ x y → T₁ (f x) (f y))
    (rel₂ : ∀ x ∈ F, ∀ y ∈ F, S₂ x y → T₂ (f x) (f y)) :
    CoversStructure T₁ T₂ (F.image f) P₁ P₂ := by
  obtain ⟨hcard, hrel⟩ := h
  have hcard' : (F.image f).card = n := (card_image_of_mono F f mono).trans hcard
  refine ⟨hcard', fun i j => ?_⟩
  rw [orderEmbOfFin_image F f mono hcard hcard' i,
    orderEmbOfFin_image F f mono hcard hcard' j]
  exact ⟨fun hp => rel₁ _ (F.orderEmbOfFin_mem hcard i)
      _ (F.orderEmbOfFin_mem hcard j) ((hrel i j).1 hp),
    fun hp => rel₂ _ (F.orderEmbOfFin_mem hcard i)
      _ (F.orderEmbOfFin_mem hcard j) ((hrel i j).2 hp)⟩

/-- Relation agreement on a strictly increasing finite image gives
equivalence of the indexed covering conditions. -/
theorem coversStructure_image_iff {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {F : Finset α} {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop} (f : α → β)
    (mono : ∀ x ∈ F, ∀ y ∈ F, x < y → f x < f y)
    (rel₁ : ∀ x ∈ F, ∀ y ∈ F, S₁ x y ↔ T₁ (f x) (f y))
    (rel₂ : ∀ x ∈ F, ∀ y ∈ F, S₂ x y ↔ T₂ (f x) (f y)) :
    CoversStructure S₁ S₂ F P₁ P₂ ↔ CoversStructure T₁ T₂ (F.image f) P₁ P₂ := by
  constructor
  · intro h
    exact h.image f mono (fun x hx y hy => (rel₁ x hx y hy).mp)
      (fun x hx y hy => (rel₂ x hx y hy).mp)
  · rintro ⟨hcard, hrel⟩
    have hcard' : F.card = n := (card_image_of_mono F f mono).symm.trans hcard
    refine ⟨hcard', fun i j => ?_⟩
    have hi := hrel i j
    rw [orderEmbOfFin_image F f mono hcard' hcard i,
      orderEmbOfFin_image F f mono hcard' hcard j] at hi
    exact ⟨fun hp => (rel₁ _ (F.orderEmbOfFin_mem hcard' i)
        _ (F.orderEmbOfFin_mem hcard' j)).mpr (hi.1 hp),
      fun hp => (rel₂ _ (F.orderEmbOfFin_mem hcard' i)
        _ (F.orderEmbOfFin_mem hcard' j)).mpr (hi.2 hp)⟩

/-- A finite set in a subtype and its image in the ambient order have
identical indexed covering conditions. -/
theorem coversStructure_subtype_val_iff {p : α → Prop} {S₁ S₂ : α → α → Prop}
    (F : Finset {x // p x}) {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) :
    CoversStructure (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val) F P₁ P₂ ↔
      CoversStructure S₁ S₂ (F.image Subtype.val) P₁ P₂ :=
  coversStructure_image_iff Subtype.val (fun _ _ _ _ h => h)
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

namespace Str

/-- A finite isomorphism has a total inverse whose two inverse laws hold
on the respective carriers. Nonemptiness supplies arbitrary values off
the target carrier. -/
theorem IsIso.exists_inverse [Nonempty α] {P : Str α} {Q : Str β} {h : α → β}
    (e : IsIso P Q h) :
    ∃ f : β → α, IsIso Q P f ∧
      (∀ x ∈ P.U, f (h x) = x) ∧ (∀ y ∈ Q.U, h (f y) = y) := by
  classical
  let f : β → α := fun y =>
    if hy : y ∈ Q.U then Classical.choose (e.preimage hy)
    else Classical.choice (inferInstance : Nonempty α)
  have hmem (y : β) (hy : y ∈ Q.U) : f y ∈ P.U := by
    dsimp only [f]
    rw [dif_pos hy]
    exact (Classical.choose_spec (e.preimage hy)).1
  have hright (y : β) (hy : y ∈ Q.U) : h (f y) = y := by
    dsimp only [f]
    rw [dif_pos hy]
    exact (Classical.choose_spec (e.preimage hy)).2
  have hinj (x : α) (hx : x ∈ P.U) (y : α) (hy : y ∈ P.U)
      (heq : h x = h y) : x = y :=
    le_antisymm ((e.le_iff hx hy).mp heq.le) ((e.le_iff hy hx).mp heq.symm.le)
  have hleft (x : α) (hx : x ∈ P.U) : f (h x) = x :=
    hinj _ (hmem _ (e.mem hx)) _ hx (hright _ (e.mem hx))
  refine ⟨f, ⟨?_, ?_, ?_⟩, hleft, hright⟩
  · ext x
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hmem y hy
    · intro hx
      exact Finset.mem_image.mpr ⟨h x, e.mem hx, hleft x hx⟩
  · intro x hx y hy hxy
    apply (e.lt_iff (hmem x hx) (hmem y hy)).mp
    rwa [hright x hx, hright y hy]
  · intro x hx y hy
    have hr := e.2.2 _ (hmem x hx) _ (hmem y hy)
    rw [hright x hx, hright y hy] at hr
    exact ⟨hr.1.symm, hr.2.symm⟩

end Str

/-- An order isomorphism preserving both relations preserves indexed finite coverings. -/
theorem coversStructure_orderIso_iff
    {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    (e : α ≃o β) (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y))
    (F : Finset α) {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) :
    CoversStructure S₁ S₂ F P₁ P₂ ↔ CoversStructure T₁ T₂ (F.image e) P₁ P₂ :=
  coversStructure_image_iff e (fun _ _ _ _ h => e.strictMono h)
    (fun x _ y _ => rel₁ x y) (fun x _ y _ => rel₂ x y)

/-- A finite carrier contained in a subtype can be viewed in either ambient type. -/
theorem coversStructure_subtype_iff {p : α → Prop} [DecidablePred p]
    {S₁ S₂ : α → α → Prop} (F : Finset α) (hF : ∀ x ∈ F, p x)
    {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) :
    CoversStructure S₁ S₂ F P₁ P₂ ↔
      CoversStructure (fun x y => S₁ x.val y.val) (fun x y => S₂ x.val y.val)
        (F.subtype p) P₁ P₂ := by
  have himage : (F.subtype p).image Subtype.val = F := by
    simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
      (Finset.subtype_map_of_mem hF)
  simpa only [himage] using (coversStructure_subtype_val_iff (F.subtype p) P₁ P₂).symm

/-- Transport a finite copy by conjugating its map with an order isomorphism. -/
theorem CoveringCopy.orderIso {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {F : Finset α} {f : α → α} {a : α}
    (h : CoveringCopy S₁ S₂ F f a) (e : α ≃o β)
    (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y)) :
    CoveringCopy T₁ T₂ (F.image e) (fun y => e (f (e.symm y))) (e a) := by
  obtain ⟨hb, hfix, hmono, hr₁, hr₂⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simpa using e.strictMono (hb x hx)
  · intro y hy hya
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simpa using congrArg e (hfix x hx (e.lt_iff_lt.mp hya))
  · intro y hy z hz hyz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    simpa using e.strictMono (hmono x hx w hw (e.lt_iff_lt.mp hyz))
  · intro y hy z hz hyz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    simpa using (rel₁ (f x) (f w)).mp (hr₁ x hx w hw ((rel₁ x w).mpr hyz))
  · intro y hy z hz hyz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    simpa using (rel₂ (f x) (f w)).mp (hr₂ x hx w hw ((rel₂ x w).mpr hyz))

/-- Conjugation by an order isomorphism is an equivalence on finite copies. -/
theorem coveringCopy_orderIso_iff
    {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    (e : α ≃o β) (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y))
    (F : Finset α) (f : α → α) (a : α) :
    CoveringCopy S₁ S₂ F f a ↔
      CoveringCopy T₁ T₂ (F.image e) (fun y => e (f (e.symm y))) (e a) := by
  constructor
  · exact fun h => h.orderIso e rel₁ rel₂
  · intro h
    have h₁ : ∀ x y, T₁ x y ↔ S₁ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₁ (e.symm x) (e.symm y)).symm
    have h₂ : ∀ x y, T₂ x y ↔ S₂ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₂ (e.symm x) (e.symm y)).symm
    simpa [Finset.image_image, Function.comp_def] using h.orderIso e.symm h₁ h₂

/-- Transport the first reflection condition along an order isomorphism. -/
theorem FirstCondition.orderIso {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {a b : α} (h : FirstCondition S₁ S₂ a b) (e : α ≃o β)
    (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y)) :
    FirstCondition T₁ T₂ (e a) (e b) := by
  intro F hF
  have hbelow : ∀ x ∈ F.image e.symm, x < b := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using e.symm.strictMono (hF y hy)
  obtain ⟨f, hf⟩ := h (F.image e.symm) hbelow
  refine ⟨fun y => e (f (e.symm y)), ?_⟩
  simpa [Finset.image_image, Function.comp_def] using hf.orderIso e rel₁ rel₂

/-- The first reflection condition is invariant under a relation-preserving order isomorphism. -/
theorem firstCondition_orderIso_iff {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    (e : α ≃o β) (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y)) (a b : α) :
    FirstCondition S₁ S₂ a b ↔ FirstCondition T₁ T₂ (e a) (e b) := by
  constructor
  · exact fun h => h.orderIso e rel₁ rel₂
  · intro h
    have h₁ : ∀ x y, T₁ x y ↔ S₁ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₁ (e.symm x) (e.symm y)).symm
    have h₂ : ∀ x y, T₂ x y ↔ S₂ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₂ (e.symm x) (e.symm y)).symm
    simpa using h.orderIso e.symm h₁ h₂

/-- Transport linked copies, including the upper and lower endpoint predicates. -/
theorem LinkedCondition.orderIso {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {upper lower : α → Prop} {upper' lower' : β → Prop} {a b : α}
    (h : LinkedCondition S₁ S₂ upper lower a b) (e : α ≃o β)
    (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y))
    (hupper : ∀ x, upper x ↔ upper' (e x))
    (hlower : ∀ x, lower x ↔ lower' (e x)) :
    LinkedCondition T₁ T₂ upper' lower' (e a) (e b) := by
  intro F hF
  have hbelow : ∀ x ∈ F.image e.symm, x < b := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using e.symm.strictMono (hF y hy)
  obtain ⟨f, hf, hlink⟩ := h (F.image e.symm) hbelow
  refine ⟨fun y => e (f (e.symm y)), ?_, ?_⟩
  · simpa [Finset.image_image, Function.comp_def] using hf.orderIso e rel₁ rel₂
  · intro y hy hay hupy
    apply (hlower (f (e.symm y))).mp
    apply hlink _ (Finset.mem_image_of_mem e.symm hy)
    · simpa using e.symm.monotone hay
    · apply (hupper (e.symm y)).mpr
      simpa using hupy

/-- Linked reflection conditions agree when both relations and endpoint predicates agree. -/
theorem linkedCondition_orderIso_iff
    {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {upper lower : α → Prop} {upper' lower' : β → Prop}
    (e : α ≃o β) (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y))
    (hupper : ∀ x, upper x ↔ upper' (e x))
    (hlower : ∀ x, lower x ↔ lower' (e x)) (a b : α) :
    LinkedCondition S₁ S₂ upper lower a b ↔
      LinkedCondition T₁ T₂ upper' lower' (e a) (e b) := by
  constructor
  · exact fun h => h.orderIso e rel₁ rel₂ hupper hlower
  · intro h
    have h₁ : ∀ x y, T₁ x y ↔ S₁ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₁ (e.symm x) (e.symm y)).symm
    have h₂ : ∀ x y, T₂ x y ↔ S₂ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₂ (e.symm x) (e.symm y)).symm
    have hu : ∀ x, upper' x ↔ upper (e.symm x) := by
      intro x
      simpa using (hupper (e.symm x)).symm
    have hl : ∀ x, lower' x ↔ lower (e.symm x) := by
      intro x
      simpa using (hlower (e.symm x)).symm
    simpa using h.orderIso e.symm h₁ h₂ hu hl

/-- Transport a cofinal family together with its fixed finite part. -/
theorem CofinalCopies.orderIso {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {X : Finset α} {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop} {c : α}
    (h : CofinalCopies S₁ S₂ X P₁ P₂ c) (e : α ≃o β)
    (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y)) :
    CofinalCopies T₁ T₂ (X.image e) P₁ P₂ (e c) := by
  intro y hy
  have hpre : e.symm y < c := by simpa using e.symm.strictMono hy
  obtain ⟨Y, hY, hcov⟩ := h (e.symm y) hpre
  refine ⟨Y.image e, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hlo, hhi⟩ := hY x hx
    exact ⟨by simpa using e.strictMono hlo, e.strictMono hhi⟩
  · have hc := hcov.image e (fun _ _ _ _ hlt => e.strictMono hlt)
      (fun x _ z _ => (rel₁ x z).mp) (fun x _ z _ => (rel₂ x z).mp)
    simpa only [Finset.image_union] using hc

/-- Cofinality of indexed finite copies is invariant under an order isomorphism. -/
theorem cofinalCopies_orderIso_iff
    {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    (e : α ≃o β) (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y))
    (X : Finset α) {n : ℕ} (P₁ P₂ : Fin n → Fin n → Prop) (c : α) :
    CofinalCopies S₁ S₂ X P₁ P₂ c ↔ CofinalCopies T₁ T₂ (X.image e) P₁ P₂ (e c) := by
  constructor
  · exact fun h => h.orderIso e rel₁ rel₂
  · intro h
    have h₁ : ∀ x y, T₁ x y ↔ S₁ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₁ (e.symm x) (e.symm y)).symm
    have h₂ : ∀ x y, T₂ x y ↔ S₂ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₂ (e.symm x) (e.symm y)).symm
    simpa [Finset.image_image, Function.comp_def] using h.orderIso e.symm h₁ h₂

/-- Transport the implication between cofinal-copy conditions at two endpoints. -/
theorem CofinalCondition.orderIso {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    {a b : α} (h : CofinalCondition S₁ S₂ a b) (e : α ≃o β)
    (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y)) :
    CofinalCondition T₁ T₂ (e a) (e b) := by
  intro X hX n P₁ P₂ hcof
  have hbelow : ∀ x ∈ X.image e.symm, x < a := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using e.symm.strictMono (hX y hy)
  have h₁ : ∀ x y, T₁ x y ↔ S₁ (e.symm x) (e.symm y) := by
    intro x y
    simpa using (rel₁ (e.symm x) (e.symm y)).symm
  have h₂ : ∀ x y, T₂ x y ↔ S₂ (e.symm x) (e.symm y) := by
    intro x y
    simpa using (rel₂ (e.symm x) (e.symm y)).symm
  have hcof' : CofinalCopies S₁ S₂ (X.image e.symm) P₁ P₂ a := by
    simpa using hcof.orderIso e.symm h₁ h₂
  have hres := h (X.image e.symm) hbelow n P₁ P₂ hcof'
  simpa [Finset.image_image, Function.comp_def] using hres.orderIso e rel₁ rel₂

/-- The second relation's cofinality condition is invariant under an order isomorphism. -/
theorem cofinalCondition_orderIso_iff {S₁ S₂ : α → α → Prop} {T₁ T₂ : β → β → Prop}
    (e : α ≃o β) (rel₁ : ∀ x y, S₁ x y ↔ T₁ (e x) (e y))
    (rel₂ : ∀ x y, S₂ x y ↔ T₂ (e x) (e y)) (a b : α) :
    CofinalCondition S₁ S₂ a b ↔ CofinalCondition T₁ T₂ (e a) (e b) := by
  constructor
  · exact fun h => h.orderIso e rel₁ rel₂
  · intro h
    have h₁ : ∀ x y, T₁ x y ↔ S₁ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₁ (e.symm x) (e.symm y)).symm
    have h₂ : ∀ x y, T₂ x y ↔ S₂ (e.symm x) (e.symm y) := by
      intro x y
      simpa using (rel₂ (e.symm x) (e.symm y)).symm
    simpa using h.orderIso e.symm h₁ h₂

end Alexander313.Carlson
