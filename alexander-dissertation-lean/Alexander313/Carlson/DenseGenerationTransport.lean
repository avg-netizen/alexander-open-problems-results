import Alexander313.Carlson.GeneratingRelabeling
import Alexander313.Carlson.FiniteIsomorphism
import Alexander313.Carlson.Exactness
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Algebra.Order.Field.Basic

/-!
# Transport of generation and exactness into rational labels

A finite endpoint map is extended across the entire finite support of a
generation proof before transporting its hidden witnesses. Density and
absence of endpoints provide room for those extra labels. No arbitrary
extension of the endpoint map is assumed to preserve order.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

private def castFiniteEmbedding {S T : Finset α} (h : S = T) (f : S ↪o β) : T ↪o β :=
  OrderEmbedding.ofStrictMono
    (fun x => f ⟨x.val, h.symm ▸ x.property⟩)
    (fun _x _y hxy => f.strictMono hxy)

/-- A finite increasing map into an unbounded dense order extends across
any larger finite carrier while retaining every prescribed value. -/
theorem exists_finite_order_extension [DenselyOrdered β] [NoMinOrder β]
    [NoMaxOrder β] [Nonempty β] {A S : Finset α} (hAS : A ⊆ S) (f : A ↪o β) :
    ∃ g : S ↪o β, ∀ x (hx : x ∈ A), g ⟨x, hAS hx⟩ = f ⟨x, hx⟩ := by
  classical
  have h (T : Finset α) : ∃ g : (A ∪ T : Finset α) ↪o β,
      ∀ x (hx : x ∈ A), g ⟨x, Finset.mem_union_left T hx⟩ = f ⟨x, hx⟩ := by
    induction T using Finset.induction_on with
    | empty =>
        exact ⟨castFiniteEmbedding (Finset.union_empty A).symm f, fun _ _ => rfl⟩
    | @insert a T ha ih =>
      obtain ⟨g, hg⟩ := ih
      obtain ⟨k, hk⟩ := Order.exists_orderEmbedding_insert (A ∪ T) g a
      have hfix (x : α) (hx : x ∈ A) :
          k ⟨x, Finset.mem_insert_of_mem (Finset.mem_union_left T hx)⟩ = f ⟨x, hx⟩ := by
        have he := congrFun hk (⟨x, Finset.mem_union_left T hx⟩ : (A ∪ T : Finset α))
        exact he.trans (hg x hx)
      have he : A ∪ insert a T = insert a (A ∪ T) := by
        ext z
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      exact ⟨castFiniteEmbedding he.symm k, hfix⟩
  have he : A ∪ S = S := Finset.union_eq_right.mpr hAS
  obtain ⟨g, hg⟩ := h S
  exact ⟨castFiniteEmbedding he g, hg⟩

/-- Extend the total labels of a finite map to a relabeling of its proof frame.
Only the finite carrier values of the resulting inverse matter. -/
theorem exists_rational_relabeling_extending [Nonempty α] {A S : Finset α}
    (hAS : A ⊆ S) (f : α → ℚ)
    (hmono : ∀ x ∈ A, ∀ y ∈ A, x < y → f x < f y) :
    ∃ F : FiniteRelabeling S ℚ, ∀ x ∈ A, F.toFun x = f x := by
  classical
  let e : A ↪o ℚ := OrderEmbedding.ofStrictMono (fun x => f x.val)
    (fun x y hxy => hmono x.val x.property y.val y.property hxy)
  obtain ⟨k, hk⟩ := exists_finite_order_extension hAS e
  let g (x : α) : ℚ := if hx : x ∈ S then k ⟨x, hx⟩ else 0
  have hg (x : α) (hx : x ∈ S) : g x = k ⟨x, hx⟩ := dif_pos hx
  have mono : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y := by
    intro x hx y hy hxy
    rw [hg x hx, hg y hy]
    exact k.strictMono hxy
  let b (y : ℚ) : α := if hy : y ∈ S.image g then
    Classical.choose (Finset.mem_image.mp hy) else Classical.choice ‹Nonempty α›
  have inv (x : α) (hx : x ∈ S) : b (g x) = x := by
    have hm : g x ∈ S.image g := Finset.mem_image_of_mem _ hx
    have hs := Classical.choose_spec (Finset.mem_image.mp hm)
    change (if hy : g x ∈ S.image g then Classical.choose (Finset.mem_image.mp hy)
      else Classical.choice ‹Nonempty α›) = x
    rw [dif_pos hm]
    have hk : k ⟨Classical.choose (Finset.mem_image.mp hm), hs.1⟩ = k ⟨x, hx⟩ :=
      (hg _ hs.1).symm.trans (hs.2.trans (hg x hx))
    exact congrArg Subtype.val (k.injective hk)
  refine ⟨⟨g, b, inv, mono⟩, ?_⟩
  intro x hx
  exact (hg x (hAS hx)).trans (hk x hx)

namespace Str

/-- Equal carrier labels identify the finite mapped structure with the
specified endpoint via the identity, including all carrier relations. -/
theorem IsIso.from_same_labels {P : Str α} {Q : Str β} {f g : α → β}
    (e : IsIso P Q f) (eg : IsIso P (P.map g) g)
    (hfix : ∀ x ∈ P.U, g x = f x) : IsIso (P.map g) Q id := by
  refine ⟨?_, fun _ _ _ _ h => h, ?_⟩
  · change (P.U.image g).image id = Q.U
    rw [Finset.image_id]
    exact (Finset.image_congr hfix).trans e.1
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := eg.preimage hx
    obtain ⟨b, hb, rfl⟩ := eg.preimage hy
    have h := eg.2.2 a ha b hb
    have h' := e.2.2 a ha b hb
    simpa only [hfix a ha, hfix b hb, id_eq] using
      (And.intro (h.1.symm.trans h'.1) (h.2.symm.trans h'.2))


/-- Compatible rational endpoint isomorphisms transport the entire
finite generation proof, including its larger chain witness. -/
theorem Generates.of_rational_isos [Nonempty α] {P Q : Str α} {P' Q' : Str ℚ}
    {h f : α → ℚ} (d : Generates P Q) (e : IsIso P P' h)
    (eplus : IsIso Q Q' f) (hfix : ∀ x ∈ P.U, f x = h x) : Generates P' Q' := by
  obtain ⟨S, hP, hQ, hS⟩ := d.exists_relabeling_support
  obtain ⟨F, hF⟩ := exists_rational_relabeling_extending hQ f eplus.2.1
  have ep : IsIso (P.map F.toFun) P' id :=
    e.from_same_labels (F.isIso hP) (fun x hx => (hF x (d.isSub.1 hx)).trans (hfix x hx))
  have eq : IsIso (Q.map F.toFun) Q' id := eplus.from_same_labels (F.isIso hQ) hF
  exact (hS ℚ F).of_identity_isos ep eq

/-- Compatible endpoint copies induce an isomorphism of their initial spans. -/
theorem IsIso.initialSpan {P Q : Str α} {P' Q' : Str β} {h f : α → β}
    (e : IsIso P P' h) (eplus : IsIso Q Q' f) (hPQ : IsSub P Q)
    (hfix : ∀ x ∈ P.U, f x = h x) :
    IsIso (Q.initialSpan P.U) (Q'.initialSpan P'.U) f := by
  refine ⟨?_, fun x hx y hy => eplus.2.1 x (mem_initialSpan.mp hx).1
    y (mem_initialSpan.mp hy).1, ?_⟩
  · ext z
    constructor
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxQ, p, hp, hxp⟩ := mem_initialSpan.mp hx
      apply mem_initialSpan.mpr
      refine ⟨eplus.mem hxQ, h p, e.mem hp, ?_⟩
      simpa only [hfix p hp] using (eplus.le_iff hxQ (hPQ.1 hp)).mpr hxp
    · intro hz
      obtain ⟨hzQ, p, hp, hzp⟩ := mem_initialSpan.mp hz
      obtain ⟨x, hx, rfl⟩ := eplus.preimage hzQ
      obtain ⟨a, ha, rfl⟩ := e.preimage hp
      have hxa : x ≤ a := (eplus.le_iff hx (hPQ.1 ha)).mp
        (by simpa only [hfix a ha] using hzp)
      exact Finset.mem_image.mpr ⟨x, mem_initialSpan.mpr ⟨hx, a, ha, hxa⟩, rfl⟩
  · intro x hx y hy
    exact eplus.2.2 x (mem_initialSpan.mp hx).1 y (mem_initialSpan.mp hy).1

/-- Exactness survives compatible rational relabeling of both endpoints. -/
theorem Exact.of_rational_isos [Nonempty α] {P Q : Str α} {P' Q' : Str ℚ}
    {h f : α → ℚ} (d : Exact P Q) (e : IsIso P P' h)
    (eplus : IsIso Q Q' f) (hfix : ∀ x ∈ P.U, f x = h x) : Exact P' Q' := by
  have es := e.initialSpan eplus d.isSub hfix
  refine ⟨eplus.isPattern d.pattern, d.generates.of_rational_isos e es hfix, ?_⟩
  apply (initialSpan_correct_iff Q' P'.U).mpr
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := es.preimage hx
  obtain ⟨b, hb, rfl⟩ := eplus.preimage hy
  have hab : Q.r₁ a b := (eplus.2.2 a (mem_initialSpan.mp ha).1 b hb).1.mpr hxy
  exact es.mem ((initialSpan_correct_iff Q P.U).mp d.correct a ha b hb hab)

end Str
end Alexander313.Carlson
