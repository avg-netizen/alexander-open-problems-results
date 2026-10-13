import Alexander313.Carlson.GeneratingRelabeling
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Transport finite generating chains to ordinal endpoints

The isomorphism invariance of a generating rule is implemented by its minimal
lifting constructor, whose source and target use one ambient type. To apply
this invariance across ambient types, first transport the rule's entire finite
support to finite ordinal ranks. Its endpoints can then be moved to their
desired ordinal copies by the existing minimal-lifting rule.

Only the endpoints of a chain need to use the given labels. Auxiliary proof
carriers are transported separately; no extension of the endpoint map to all
hidden labels is assumed. This is the pure-case change of presentation used
in Carlson's Theorem 14.10, via Lemma 13.11(1).
-/

noncomputable section

namespace Alexander313.Carlson

variable {α : Type*} [LinearOrder α] [Nonempty α]

/-- Increasing ordinal ranks for an arbitrary finite ordered frame. -/
def finiteOrdinalRelabeling (S : Finset α) : FiniteRelabeling S Ordinal.{0} := by
  classical
  let index (x : α) (hx : x ∈ S) := (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
  let f (x : α) : Ordinal.{0} := if hx : x ∈ S then (index x hx).val else 0
  have hf (x : α) (hx : x ∈ S) : f x = ((index x hx).val : Ordinal.{0}) := by
    simp only [f, dif_pos hx]
  have mono : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y := by
    intro x hx y hy hxy
    rw [hf x hx, hf y hy]
    have h : (index x hx).val < (index y hy).val :=
      (S.orderIsoOfFin rfl).symm.strictMono
        (show (⟨x, hx⟩ : {x // x ∈ S}) < ⟨y, hy⟩ from hxy)
    exact Nat.cast_lt.mpr h
  have inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x hx y hy heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (mono x hx y hy hlt).ne heq
    · exact (mono y hy x hx hlt).ne heq.symm
  let g (y : Ordinal.{0}) : α :=
    if hy : y ∈ S.image f then Classical.choose (Finset.mem_image.mp hy)
    else Classical.choice inferInstance
  refine ⟨f, g, ?_, mono⟩
  intro x hx
  have hm : f x ∈ S.image f := Finset.mem_image_of_mem f hx
  have hs := Classical.choose_spec (Finset.mem_image.mp hm)
  change g (f x) = x
  simp only [g, dif_pos hm]
  exact inj _ hs.1 x hx hs.2

namespace Str

omit [Nonempty α] in
private theorem inverse_comp_isIso {S : Finset α} (F : FiniteRelabeling S Ordinal.{0})
    {P : Str α} {Q : Str Ordinal.{0}} {h : α → Ordinal.{0}}
    (hP : P.U ⊆ S) (e : IsIso P Q h) :
    IsIso (P.map F.toFun) Q (h ∘ F.invFun) := by
  have b := F.inverse_isIso hP
  refine ⟨?_, ?_, ?_⟩
  · change (P.U.image F.toFun).image (h ∘ F.invFun) = Q.U
    rw [Finset.image_image]
    calc
      P.U.image ((h ∘ F.invFun) ∘ F.toFun) = P.U.image h :=
        Finset.image_congr (fun x hx => by simp only [Function.comp_apply, F.left_inv x (hP hx)])
      _ = Q.U := e.1
  · intro x hx y hy hxy
    exact e.2.1 _ (b.mem hx) _ (b.mem hy) (b.2.1 x hx y hy hxy)
  · intro x hx y hy
    have e₁ := b.2.2 x hx y hy
    have e₂ := e.2.2 _ (b.mem hx) _ (b.mem hy)
    exact ⟨e₁.1.trans e₂.1, e₁.2.trans e₂.2⟩

/-- Compatible ordinal copies of the endpoints preserve a generating rule,
including when its original ambient order differs from the ordinals. -/
theorem GeneratingRule.of_ordinal_isos {P Pplus : Str α} {Q Qplus : Str Ordinal.{0}}
    {h f : α → Ordinal.{0}} (d : GeneratingRule P Pplus)
    (e : IsIso P Q h) (eplus : IsIso Pplus Qplus f)
    (hfix : ∀ x ∈ P.U, f x = h x) : GeneratingRule Q Qplus := by
  obtain ⟨S, hP, hPplus, hS⟩ := d.exists_relabeling_support
  let F := finiteOrdinalRelabeling S
  have d' := hS Ordinal.{0} F
  apply d'.of_isIso (inverse_comp_isIso F hP e) (inverse_comp_isIso F hPplus eplus)
  intro x hx
  exact hfix _ ((F.inverse_isIso hP).mem hx)

/-- An exact chain transports to compatible ordinal endpoint copies. The
intermediate carriers use the final endpoint map on their own finite sets. -/
theorem ExactlyGenerates.of_ordinal_isos {P Pplus : Str α} {Q Qplus : Str Ordinal.{0}}
    {h f : α → Ordinal.{0}} (d : ExactlyGenerates P Pplus)
    (e : IsIso P Q h) (eplus : IsIso Pplus Qplus f)
    (hfix : ∀ x ∈ P.U, f x = h x) : ExactlyGenerates Q Qplus := by
  induction d using ExactlyGenerates.rec (motive_1 := fun _ _ _ => True)
      generalizing Q Qplus h f
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · rename_i P hP
    have d : GeneratingRule P P := .refl hP
    exact (d.of_ordinal_isos e eplus hfix).exactlyGenerates
  · rename_i P M R c r ih _
    have eM : IsIso M (M.map f) f := M.map_isIso f
      (fun x hx y hy hxy => eplus.2.1 x (r.isSub.1 hx) y (r.isSub.1 hy) hxy)
    exact .tail (ih e eM hfix) (r.of_ordinal_isos eM eplus (fun _ _ => rfl))

end Str
end Alexander313.Carlson
