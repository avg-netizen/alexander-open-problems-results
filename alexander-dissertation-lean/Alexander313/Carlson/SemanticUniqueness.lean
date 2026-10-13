import Alexander313.Carlson.ReflectionConditions
import Alexander313.Carlson.SemanticTransport
import Alexander313.Carlson.InitialSegmentSemantics

/-!
# Uniqueness of the intrinsic semantic equations

The two finite-copy equations determine their relations on a well-ordered
linear order. The induction runs on the upper endpoint. The first equation
at an endpoint only reads relations below that endpoint. Once that entire
first-relation column is known, the linked clause of the second equation
is also determined.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α : Type*} [LinearOrder α]
variable {S₁ S₂ T₁ T₂ : α → α → Prop}

/-- A finite copy is unchanged when the relations agree below an upper
bound containing both its source carrier and its image. -/
theorem CoveringCopy.congr_below {F : Finset α} {f : α → α} {a b : α}
    (h : CoveringCopy S₁ S₂ F f a) (hab : a ≤ b)
    (hF : ∀ x ∈ F, x < b)
    (h₁ : ∀ x y, y < b → (S₁ x y ↔ T₁ x y))
    (h₂ : ∀ x y, y < b → (S₂ x y ↔ T₂ x y)) :
    CoveringCopy T₁ T₂ F f a := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · intro x hx y hy hxy
    exact (h₁ (f x) (f y) ((h.1 y hy).trans_le hab)).mp
      (h.2.2.2.1 x hx y hy ((h₁ x y (hF y hy)).mpr hxy))
  · intro x hx y hy hxy
    exact (h₂ (f x) (f y) ((h.1 y hy).trans_le hab)).mp
      (h.2.2.2.2 x hx y hy ((h₂ x y (hF y hy)).mpr hxy))

/-- The first finite-copy condition only uses relations whose upper
endpoint is strictly below its upper bound. -/
theorem firstCondition_congr_below {a b : α} (hab : a ≤ b)
    (h₁ : ∀ x y, y < b → (S₁ x y ↔ T₁ x y))
    (h₂ : ∀ x y, y < b → (S₂ x y ↔ T₂ x y)) :
    FirstCondition S₁ S₂ a b ↔ FirstCondition T₁ T₂ a b := by
  constructor
  · intro h F hF
    obtain ⟨f, hf⟩ := h F hF
    exact ⟨f, hf.congr_below hab hF h₁ h₂⟩
  · intro h F hF
    obtain ⟨f, hf⟩ := h F hF
    exact ⟨f, hf.congr_below hab hF
      (fun x y hy => (h₁ x y hy).symm) (fun x y hy => (h₂ x y hy).symm)⟩

/-- The linked finite-copy condition depends on the relations below
its upper bound and on the two endpoint predicates on their respective
initial segments. -/
theorem linkedCondition_congr_below {a b : α} (hab : a ≤ b)
    {upper lower upper' lower' : α → Prop}
    (h₁ : ∀ x y, y < b → (S₁ x y ↔ T₁ x y))
    (h₂ : ∀ x y, y < b → (S₂ x y ↔ T₂ x y))
    (hupper : ∀ x, x < b → (upper x ↔ upper' x))
    (hlower : ∀ x, x < a → (lower x ↔ lower' x)) :
    LinkedCondition S₁ S₂ upper lower a b ↔
      LinkedCondition T₁ T₂ upper' lower' a b := by
  constructor
  · intro h F hF
    obtain ⟨f, hf, hlinks⟩ := h F hF
    refine ⟨f, hf.congr_below hab hF h₁ h₂, ?_⟩
    intro x hx hax hup
    exact (hlower (f x) (hf.1 x hx)).mp
      (hlinks x hx hax ((hupper x (hF x hx)).mpr hup))
  · intro h F hF
    obtain ⟨f, hf, hlinks⟩ := h F hF
    refine ⟨f, hf.congr_below hab hF
      (fun x y hy => (h₁ x y hy).symm) (fun x y hy => (h₂ x y hy).symm), ?_⟩
    intro x hx hax hup
    exact (hlower (f x) (hf.1 x hx)).mpr
      (hlinks x hx hax ((hupper x (hF x hx)).mp hup))

/-- Cofinal copies below a bound depend only on relations below that
bound, including on the fixed finite lower block. -/
theorem cofinalCopies_congr_below {b c : α} (hcb : c ≤ b)
    (X : Finset α) (hX : ∀ x ∈ X, x < b) {n : ℕ}
    (P₁ P₂ : Fin n → Fin n → Prop)
    (h₁ : ∀ x y, y < b → (S₁ x y ↔ T₁ x y))
    (h₂ : ∀ x y, y < b → (S₂ x y ↔ T₂ x y)) :
    CofinalCopies S₁ S₂ X P₁ P₂ c ↔ CofinalCopies T₁ T₂ X P₁ P₂ c := by
  have below (Y : Finset α) (hY : ∀ y ∈ Y, y < c) :
      ∀ z ∈ X ∪ Y, z < b := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hX z hz
    · exact (hY z hz).trans_le hcb
  constructor
  · intro h ξ hξ
    obtain ⟨Y, hY, hcover⟩ := h ξ hξ
    refine ⟨Y, hY, (CoversStructure.congr ?_ ?_).mp hcover⟩
    · exact fun x _ y hy => h₁ x y (below Y (fun y hy => (hY y hy).2) y hy)
    · exact fun x _ y hy => h₂ x y (below Y (fun y hy => (hY y hy).2) y hy)
  · intro h ξ hξ
    obtain ⟨Y, hY, hcover⟩ := h ξ hξ
    refine ⟨Y, hY, (CoversStructure.congr ?_ ?_).mpr hcover⟩
    · exact fun x _ y hy => h₁ x y (below Y (fun y hy => (hY y hy).2) y hy)
    · exact fun x _ y hy => h₂ x y (below Y (fun y hy => (hY y hy).2) y hy)

/-- The upward-cofinality condition only reads relations below its
upper endpoint. -/
theorem cofinalCondition_congr_below {a b : α} (hab : a ≤ b)
    (h₁ : ∀ x y, y < b → (S₁ x y ↔ T₁ x y))
    (h₂ : ∀ x y, y < b → (S₂ x y ↔ T₂ x y)) :
    CofinalCondition S₁ S₂ a b ↔ CofinalCondition T₁ T₂ a b := by
  constructor
  · intro h X hX n P₁ P₂ hcof
    have hXb : ∀ x ∈ X, x < b := fun x hx => (hX x hx).trans_le hab
    exact (cofinalCopies_congr_below le_rfl X hXb P₁ P₂ h₁ h₂).mp
      (h X hX n P₁ P₂
        ((cofinalCopies_congr_below hab X hXb P₁ P₂ h₁ h₂).mpr hcof))
  · intro h X hX n P₁ P₂ hcof
    have hXb : ∀ x ∈ X, x < b := fun x hx => (hX x hx).trans_le hab
    exact (cofinalCopies_congr_below le_rfl X hXb P₁ P₂ h₁ h₂).mpr
      (h X hX n P₁ P₂
        ((cofinalCopies_congr_below hab X hXb P₁ P₂ h₁ h₂).mp hcof))

/-- On a well-founded linear order, Carlson's two intrinsic semantic
equations determine both relations uniquely. The only hypotheses are the
two defining equations for each candidate pair. -/
theorem semantic_equations_unique (wf : WellFounded ((· < ·) : α → α → Prop))
    (hS₁ : ∀ a b, S₁ a b ↔ a ≤ b ∧ FirstCondition S₁ S₂ a b)
    (hS₂ : ∀ a b, S₂ a b ↔ SecondCondition S₁ S₂ a b)
    (hT₁ : ∀ a b, T₁ a b ↔ a ≤ b ∧ FirstCondition T₁ T₂ a b)
    (hT₂ : ∀ a b, T₂ a b ↔ SecondCondition T₁ T₂ a b) :
    ∀ a b, (S₁ a b ↔ T₁ a b) ∧ (S₂ a b ↔ T₂ a b) := by
  have uniqueColumn : ∀ b a, (S₁ a b ↔ T₁ a b) ∧ (S₂ a b ↔ T₂ a b) := by
    intro b
    apply wf.induction b
    intro b ih
    have hprev₁ : ∀ x y, y < b → (S₁ x y ↔ T₁ x y) :=
      fun x y hy => (ih y hy x).1
    have hprev₂ : ∀ x y, y < b → (S₂ x y ↔ T₂ x y) :=
      fun x y hy => (ih y hy x).2
    have hfirst : ∀ a, S₁ a b ↔ T₁ a b := by
      intro a
      rw [hS₁ a b, hT₁ a b]
      exact and_congr_right fun hab => firstCondition_congr_below hab hprev₁ hprev₂
    intro a
    refine ⟨hfirst a, ?_⟩
    rw [hS₂ a b, hT₂ a b]
    unfold SecondCondition
    apply and_congr_right
    intro hab
    have hfirst_a : ∀ x, S₁ x a ↔ T₁ x a := by
      rcases hab.lt_or_eq with hab | rfl
      · exact fun x => hprev₁ x a hab
      · exact hfirst
    exact and_congr
      (linkedCondition_congr_below hab hprev₁ hprev₂
        (fun x _ => hfirst x) (fun x _ => hfirst_a x))
      (cofinalCondition_congr_below hab hprev₁ hprev₂)
  exact fun a b => uniqueColumn b a

/-- On an ordinal initial segment, any pair satisfying Carlson's
intrinsic semantic equations is precisely the restriction of the actual
ordinal relations. No additional relation or saturation hypothesis is
needed. -/
theorem ordinalRelations_unique {o : Ordinal.{0}}
    {T₁ T₂ : Set.Iio o → Set.Iio o → Prop}
    (h1 : ∀ a b, T₁ a b ↔ a ≤ b ∧ FirstCondition T₁ T₂ a b)
    (h2 : ∀ a b, T₂ a b ↔ SecondCondition T₁ T₂ a b) :
    ∀ a b, (T₁ a b ↔ R1 a.val b.val) ∧ (T₂ a b ↔ R2 a.val b.val) := by
  exact semantic_equations_unique (InvImage.wf Subtype.val Ordinal.lt_wf) h1 h2
    R1_Iio_iff_firstCondition R2_Iio_iff_secondCondition

end Alexander313.Carlson
