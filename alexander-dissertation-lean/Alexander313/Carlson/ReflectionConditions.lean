import Alexander313.Carlson.CoveringEnumeration

/-!
# Restricting intrinsic reflection conditions

The finite-copy clauses of Carlson's Definition 5.3 are interpreted in
an arbitrary linear order with two given relations. Their restriction
properties do not require the ambient order to consist of ordinals.

The cofinal-copy argument is the pure relational version of the proof of
Lemma 5.5(6), also used in the second-relation converse of Lemma 14.8(8).
To descend cofinal copies through a first-condition edge, include the
desired lower bound in the finite set being copied. The copy fixes that
bound and the old lower block, so strict monotonicity keeps the new block
above the bound.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α : Type*} [LinearOrder α] {S₁ S₂ : α → α → Prop}

/-- Carlson's second finite-copy condition interpreted intrinsically
in a structure whose first and second relations are `S₁` and `S₂`. -/
def SecondCondition (S₁ S₂ : α → α → Prop) (a b : α) : Prop :=
  a ≤ b ∧
    LinkedCondition S₁ S₂ (fun y => S₁ y b) (fun y => S₁ y a) a b ∧
    CofinalCondition S₁ S₂ a b

/-- The linked-copy clause includes the first finite-copy condition. -/
theorem SecondCondition.firstCondition {a b : α} (h : SecondCondition S₁ S₂ a b) :
    FirstCondition S₁ S₂ a b := by
  intro F hF
  obtain ⟨f, hf, _⟩ := h.2.1 F hF
  exact ⟨f, hf⟩

/-- Every finite structure below the upper endpoint of a first-condition
edge has cofinally many coverings below its lower endpoint, fixing the
original part below that lower endpoint. The source relations are the
increasing enumeration of the given finite carrier. -/
theorem FirstCondition.cofinalCopies {a d : α}
    (h : FirstCondition S₁ S₂ a d) (had : a ≤ d) (F : Finset α)
    (hF : ∀ z ∈ F, z < d) :
    CofinalCopies S₁ S₂ (F.filter (· < a))
      (Str.mk F S₁ S₂).indexedFirst (Str.mk F S₁ S₂).indexedSecond a := by
  classical
  intro ξ hξ
  let X := F.filter (· < a)
  let Y := F.filter (a ≤ ·)
  have hpartition : X ∪ Y = F := by
    ext z
    simp only [X, Y, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro hz
      rcases lt_or_ge z a with hza | haz
      · exact Or.inl ⟨hz, hza⟩
      · exact Or.inr ⟨hz, haz⟩
  let G := insert ξ F
  have hG : ∀ z ∈ G, z < d := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hξ.trans_le had
    · exact hF z hz
  obtain ⟨f, hf⟩ := h G hG
  have inG (z : α) (hz : z ∈ F) : z ∈ G := Finset.mem_insert_of_mem hz
  have hXimage : X.image f = X := by
    calc
      X.image f = X.image id := Finset.image_congr fun x hx =>
        hf.2.1 x (inG x (Finset.mem_filter.mp hx).1) (Finset.mem_filter.mp hx).2
      _ = X := Finset.image_id
  refine ⟨Y.image f, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzF : z ∈ F := (Finset.mem_filter.mp hz).1
    have haz : a ≤ z := (Finset.mem_filter.mp hz).2
    refine ⟨?_, hf.1 z (inG z hzF)⟩
    have hfix : f ξ = ξ := hf.2.1 ξ (Finset.mem_insert_self ξ _) hξ
    have hm := hf.2.2.1 ξ (Finset.mem_insert_self ξ _) z (inG z hzF)
      (hξ.trans_le haz)
    rwa [hfix] at hm
  · have hcover : Str.IsCovering (Str.mk F S₁ S₂) S₁ S₂ f :=
      ⟨fun x hx y hy hxy => hf.2.2.1 x (inG x hx) y (inG y hy) hxy,
        fun x hx y hy hxy => hf.2.2.2.1 x (inG x hx) y (inG y hy) hxy,
        fun x hx y hy hxy => hf.2.2.2.2 x (inG x hx) y (inG y hy) hxy⟩
    have hc := hcover.coversStructure_image
    change CoversStructure S₁ S₂ (F.image f)
      (Str.mk F S₁ S₂).indexedFirst (Str.mk F S₁ S₂).indexedSecond at hc
    have himage : F.image f = X ∪ Y.image f := by
      rw [← hpartition, Finset.image_union, hXimage]
    rwa [himage] at hc

/-- Cofinal copies descend through the finite-copy condition of the
first relation while preserving any fixed finite block below the target. -/
theorem CofinalCopies.of_firstCondition {a b : α} {X : Finset α}
    {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop}
    (h : CofinalCopies S₁ S₂ X P₁ P₂ b) (hab : a ≤ b)
    (hfirst : FirstCondition S₁ S₂ a b) (hX : ∀ x ∈ X, x < a) :
    CofinalCopies S₁ S₂ X P₁ P₂ a := by
  classical
  rcases hab.lt_or_eq with hab | rfl
  · intro ξ hξ
    obtain ⟨Y, hY, hcover⟩ := h a hab
    let F := insert ξ (X ∪ Y)
    have hF : ∀ z ∈ F, z < b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hξ.trans hab
      · rcases Finset.mem_union.mp hz with hz | hz
        · exact (hX z hz).trans hab
        · exact (hY z hz).2
    obtain ⟨f, hcopy⟩ := hfirst F hF
    have inF (z : α) (hz : z ∈ X ∪ Y) : z ∈ F := Finset.mem_insert_of_mem hz
    refine ⟨Y.image f, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hzF : z ∈ F := inF z (Finset.mem_union_right X hz)
      refine ⟨?_, hcopy.1 z hzF⟩
      have hfix : f ξ = ξ := hcopy.2.1 ξ (Finset.mem_insert_self ξ _) hξ
      have hm := hcopy.2.2.1 ξ (Finset.mem_insert_self ξ _) z hzF
        (hξ.trans (hY z hz).1)
      rwa [hfix] at hm
    · have himage : (X ∪ Y).image f = X ∪ Y.image f := by
        rw [Finset.image_union]
        congr 1
        calc
          X.image f = X.image id := Finset.image_congr fun x hx =>
            hcopy.2.1 x (inF x (Finset.mem_union_left Y hx)) (hX x hx)
          _ = X := Finset.image_id
      rw [← himage]
      exact hcover.transport f
        (fun x hx y hy hxy => hcopy.2.2.1 x (inF x hx) y (inF y hy) hxy)
        (fun x hx y hy hxy => hcopy.2.2.2.1 x (inF x hx) y (inF y hy) hxy)
        (fun x hx y hy hxy => hcopy.2.2.2.2 x (inF x hx) y (inF y hy) hxy)
  · exact h

/-- The upward-cofinality clause of the second relation restricts its
upper endpoint through the first finite-copy condition. -/
theorem CofinalCondition.restrict_right {a b c : α}
    (h : CofinalCondition S₁ S₂ a c) (hab : a ≤ b) (hbc : b ≤ c)
    (hfirst : FirstCondition S₁ S₂ b c) : CofinalCondition S₁ S₂ a b := by
  intro X hX n P₁ P₂ hcof
  exact (h X hX n P₁ P₂ hcof).of_firstCondition hbc hfirst
    (fun x hx => (hX x hx).trans_le hab)

/-- The linked-copy clause restricts its upper endpoint along an edge
of a transitive first relation. -/
theorem LinkedCondition.restrict_right {a b c : α}
    (h : LinkedCondition S₁ S₂ (fun y => S₁ y c) (fun y => S₁ y a) a c)
    (htrans : ∀ {x y z}, S₁ x y → S₁ y z → S₁ x z)
    (hbc : b ≤ c) (hrel : S₁ b c) :
    LinkedCondition S₁ S₂ (fun y => S₁ y b) (fun y => S₁ y a) a b := by
  intro F hF
  obtain ⟨f, hcopy, hlinks⟩ := h F (fun z hz => (hF z hz).trans_le hbc)
  exact ⟨f, hcopy, fun z hz haz hzb => hlinks z hz haz (htrans hzb hrel)⟩

/-- Intrinsic second conditions respect a first-relation edge when that
edge has the first finite-copy property and the first relation is transitive. -/
theorem SecondCondition.respects_first {a b c : α}
    (h : SecondCondition S₁ S₂ a c)
    (htrans : ∀ {x y z}, S₁ x y → S₁ y z → S₁ x z)
    (hab : a ≤ b) (hbc : b ≤ c) (hrel : S₁ b c)
    (hfirst : FirstCondition S₁ S₂ b c) : SecondCondition S₁ S₂ a b :=
  ⟨hab, h.2.1.restrict_right htrans hbc hrel,
    h.2.2.restrict_right hab hbc hfirst⟩

/-- The ordinal first relation in the global, intrinsic finite-copy
form, equivalent to its recursive definition using prefix relations. -/
theorem R1_iff_firstCondition (a b : Ordinal.{0}) :
    R1 a b ↔ a ≤ b ∧ FirstCondition R1 R2 a b := by
  constructor
  · intro h
    exact ⟨R1_le h, R1_copy' h⟩
  · rintro ⟨hab, h⟩
    refine (R1_iff a b).mpr ⟨hab, ?_⟩
    intro F hF
    obtain ⟨f, hf⟩ := h F hF
    exact ⟨f, hf.prefix hab⟩

/-- The intrinsic second condition agrees with the actual ordinal
second relation, including reflexive endpoints. -/
theorem R2_iff_secondCondition (a b : Ordinal.{0}) :
    R2 a b ↔ SecondCondition R1 R2 a b := by
  constructor
  · intro h
    exact ⟨R2_le h, R2_copy' h, fun X hX _ P₁ P₂ => R2_cofinal h X hX P₁ P₂⟩
  · intro h
    exact R2_of_global h.1 h.2.1 h.2.2

end Alexander313.Carlson
