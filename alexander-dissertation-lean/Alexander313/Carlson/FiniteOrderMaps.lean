import Alexander313.Carlson.Order

/-!
# Uniqueness of increasing maps on finite carriers

An increasing map on a finite linear order is determined by its image: it
must match the increasing source and target enumerations. The equality is
on the finite carrier, since total maps may differ outside that carrier.

This elementary fact supplies the map uniqueness used by arithmetic liftings
in the pure language of finite linear orders.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Two strictly increasing maps on a finite carrier with the same exact
image agree at every point of that carrier. -/
theorem eqOn_of_strictMonoOn_image_eq {S : Finset α} {f g : α → β}
    (hf : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y)
    (hg : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y)
    (hi : S.image f = S.image g) : ∀ x ∈ S, f x = g x := by
  have hcard : (S.image g).card = S.card := card_image_of_mono S g hg
  have hfenum : (fun i : Fin S.card => f (S.orderEmbOfFin rfl i)) =
      (S.image g).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro i
      rw [← hi]
      exact Finset.mem_image_of_mem f (S.orderEmbOfFin_mem rfl i)
    · intro i j hij
      exact hf _ (S.orderEmbOfFin_mem rfl i) _ (S.orderEmbOfFin_mem rfl j)
        ((S.orderEmbOfFin rfl).strictMono hij)
  intro x hx
  let i : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
  have hei : S.orderEmbOfFin rfl i = x :=
    congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
  calc
    f x = f (S.orderEmbOfFin rfl i) := congrArg f hei.symm
    _ = (S.image g).orderEmbOfFin hcard i := congrFun hfenum i
    _ = g (S.orderEmbOfFin rfl i) := orderEmbOfFin_image S g hg rfl hcard i
    _ = g x := congrArg g hei

end Alexander313.Carlson
