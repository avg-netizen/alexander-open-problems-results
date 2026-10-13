import Alexander313.Carlson.SemanticTransport
import Mathlib.Order.Hom.Set

/-!
# Isomorphisms between finite ordered carriers

An increasing finite isomorphism induces an order isomorphism of its
carriers. Such an order isomorphism is unique. The inverse and composition
constructions below are used to identify two finite copies of the same
ordinal structure in Carlson's Theorem 15.9(2).
-/

noncomputable section

namespace Alexander313.Carlson.Str

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
variable {P : Str α} {Q : Str β} {T : Str γ}
variable {f : α → β} {g : β → γ}

theorem IsIso.injOn (e : IsIso P Q f) : Set.InjOn f P.U := by
  intro x hx y hy hxy
  exact le_antisymm ((e.le_iff hx hy).mp hxy.le) ((e.le_iff hy hx).mp hxy.ge)

/-- Composition retains every carrier, order and relation requirement. -/
theorem IsIso.comp (d : IsIso Q T g) (e : IsIso P Q f) :
    IsIso P T (g ∘ f) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.image_image, e.1, d.1]
  · intro x hx y hy hxy
    exact d.2.1 (f x) (e.mem hx) (f y) (e.mem hy) (e.2.1 x hx y hy hxy)
  · intro x hx y hy
    have h := e.2.2 x hx y hy
    have h' := d.2.2 (f x) (e.mem hx) (f y) (e.mem hy)
    exact ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- The actual order isomorphism of the finite carriers. -/
def IsIso.orderIso (e : IsIso P Q f) : P.U ≃o Q.U :=
  StrictMono.orderIsoOfSurjective
    (fun x : P.U => (⟨f x.val, e.mem x.property⟩ : Q.U))
    (fun x y hxy => e.2.1 x.val x.property y.val y.property hxy)
    (by
      intro y
      obtain ⟨x, hx, hxy⟩ := e.preimage y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

/-- Finite linear order leaves no freedom in an isomorphism's values on
the carrier. Its arbitrary values away from the carrier are irrelevant. -/
theorem IsIso.eqOn {g : α → β} (e : IsIso P Q f) (d : IsIso P Q g) :
    Set.EqOn f g P.U := by
  intro x hx
  have h := congrArg (fun E : P.U ≃o Q.U => (E ⟨x, hx⟩).val)
    (Subsingleton.elim e.orderIso d.orderIso)
  exact h

/-- Two copies onto the same finite structure are identified by an actual
finite isomorphism whose composition with the second copy is the first. -/
theorem IsIso.between_copies [Nonempty β] {h : α → γ} {k : β → γ}
    (e : IsIso P T h) (d : IsIso Q T k) :
    ∃ f : α → β, IsIso P Q f ∧ ∀ x ∈ P.U, k (f x) = h x := by
  obtain ⟨g, hg, _, hright⟩ := d.exists_inverse
  exact ⟨g ∘ h, hg.comp e, fun x hx => hright (h x) (e.mem hx)⟩

end Alexander313.Carlson.Str
