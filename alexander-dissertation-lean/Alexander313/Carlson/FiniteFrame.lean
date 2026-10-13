import Alexander313.Carlson.FiniteRelabeling
import Alexander313.Carlson.FinitePatterns

/-!
# Finite labels for an ordered frame

Every finite frame in a nonempty linear order can be relabeled by a finite
type. The labels below the frame's cardinality enumerate its members in
increasing order; the final label gives the total forward map a value away
from the frame. The inverse uses an arbitrary ambient point at that final
label, so the construction also works when the frame is empty.

Encoding the relabeled structure gives an exact finite Boolean presentation
up to the original carrier-sensitive notion of isomorphism.
-/

noncomputable section

namespace Alexander313.Carlson

variable {α : Type*} [LinearOrder α]

namespace FiniteRelabeling

/-- Relabel a finite frame by its increasing ranks, reserving the last label
for points outside the frame. The ambient type only needs to be nonempty;
the frame itself may be empty. -/
def toFin (S : Finset α) [Nonempty α] : FiniteRelabeling S (Fin (S.card + 1)) where
  toFun x := if hx : x ∈ S then
    ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).castSucc
    else Fin.last S.card
  invFun i := if hi : i.val < S.card then
    S.orderEmbOfFin rfl ⟨i.val, hi⟩
    else Classical.choice inferInstance
  left_inv := by
    intro x hx
    simp only [dif_pos hx, Fin.val_castSucc]
    rw [dif_pos (((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).isLt)]
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
  mono := by
    intro x hx y hy hxy
    simp only [dif_pos hx, dif_pos hy]
    exact Fin.castSucc_lt_castSucc_iff.mpr ((S.orderIsoOfFin rfl).symm.strictMono hxy)

@[simp] theorem toFin_toFun_of_mem (S : Finset α) [Nonempty α] {x : α} (hx : x ∈ S) :
    (toFin S).toFun x = ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).castSucc := by
  simp only [toFin, dif_pos hx]

@[simp] theorem toFin_toFun_of_not_mem (S : Finset α) [Nonempty α] {x : α}
    (hx : x ∉ S) : (toFin S).toFun x = Fin.last S.card := by
  simp only [toFin, dif_neg hx]

/-- Every point of the frame receives a label strictly below the fallback. -/
theorem toFin_toFun_lt_last (S : Finset α) [Nonempty α] {x : α} (hx : x ∈ S) :
    (toFin S).toFun x < Fin.last S.card := by
  rw [toFin_toFun_of_mem S hx]
  exact Fin.castSucc_lt_last _

/-- The inverse enumeration returns a member of the frame at each genuine rank. -/
theorem toFin_invFun_mem (S : Finset α) [Nonempty α] (i : Fin S.card) :
    (toFin S).invFun i.castSucc ∈ S := by
  simp only [toFin, Fin.val_castSucc, dif_pos i.isLt]
  exact S.orderEmbOfFin_mem rfl i

/-- A nonempty frame can use exactly its cardinality as its label bound.
Every finite label is then a genuine increasing rank in the frame. -/
def toFinOfNonempty (S : Finset α) (hne : S.Nonempty) :
    FiniteRelabeling S (Fin S.card) where
  toFun x := if hx : x ∈ S then
    (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
    else ⟨0, Finset.card_pos.mpr hne⟩
  invFun := S.orderEmbOfFin rfl
  left_inv := by
    intro x hx
    simp only [dif_pos hx]
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
  mono := by
    intro x hx y hy hxy
    simp only [dif_pos hx, dif_pos hy]
    exact (S.orderIsoOfFin rfl).symm.strictMono hxy

@[simp] theorem toFinOfNonempty_toFun_of_mem (S : Finset α) (hne : S.Nonempty)
    {x : α} (hx : x ∈ S) :
    (toFinOfNonempty S hne).toFun x = (S.orderIsoOfFin rfl).symm ⟨x, hx⟩ := by
  simp only [toFinOfNonempty, dif_pos hx]

@[simp] theorem toFinOfNonempty_invFun (S : Finset α) (hne : S.Nonempty) :
    (toFinOfNonempty S hne).invFun = S.orderEmbOfFin rfl := rfl

/-- The inverse map of an exact finite relabeling is globally increasing. -/
theorem toFinOfNonempty_invFun_strictMono (S : Finset α) (hne : S.Nonempty) :
    StrictMono (toFinOfNonempty S hne).invFun :=
  (S.orderEmbOfFin rfl).strictMono

@[simp] theorem toFinOfNonempty_invFun_mem (S : Finset α) (hne : S.Nonempty)
    (i : Fin S.card) : (toFinOfNonempty S hne).invFun i ∈ S :=
  S.orderEmbOfFin_mem rfl i

/-- A nonempty frame occupies the entire finite ambient type. -/
theorem toFinOfNonempty_image_univ (S : Finset α) (hne : S.Nonempty) :
    S.image (toFinOfNonempty S hne).toFun = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  refine Finset.mem_image.mpr ⟨S.orderEmbOfFin rfl i, S.orderEmbOfFin_mem rfl i, ?_⟩
  rw [toFinOfNonempty_toFun_of_mem S hne (S.orderEmbOfFin_mem rfl i)]
  exact (S.orderIsoOfFin rfl).symm_apply_apply i

/-- Every finite label is recovered by relabeling its inverse image. -/
@[simp] theorem toFinOfNonempty_right_inv (S : Finset α) (hne : S.Nonempty)
    (i : Fin S.card) :
    (toFinOfNonempty S hne).toFun ((toFinOfNonempty S hne).invFun i) = i := by
  apply (toFinOfNonempty S hne).right_inv
  rw [toFinOfNonempty_image_univ]
  exact Finset.mem_univ i

end FiniteRelabeling

namespace Str

/-- A finite structure admits a Boolean code after relabeling its carrier by
increasing ranks. This includes the empty carrier. -/
theorem exists_finite_code (P : Str α) [Nonempty α] :
    ∃ (n : ℕ) (f : α → Fin n) (C : Finite.PatternCode n), IsIso P C.toStr f := by
  let F := FiniteRelabeling.toFin P.U
  refine ⟨P.U.card + 1, F.toFun, Finite.PatternCode.encode (P.map F.toFun), ?_⟩
  simpa only [Finite.PatternCode.toStr_encode] using F.isIso (Finset.Subset.refl P.U)

end Str
end Alexander313.Carlson
