import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup

/-!
# Primitive-recursive list canonicalization

The existing finite-set encoding sorts a list of element codes and rejects
duplicates. These lemmas certify the list operations needed for that encoding
using mathlib's ordinary `Primcodable (List α)` instance. They do not introduce
a new encoding or assume that an arbitrary decidable comparison is computable.

Insertion sort uses primitive recursion on lists. Its equality with merge
sort transfers the certificate to the sorting operation in the multiset
encoding. Membership, duplicate detection, and duplicate removal provide
the remaining finite-data normalization operations.
-/

namespace Alexander313.Carlson.PrimitiveListData

variable {α : Type*} [Primcodable α]

/-- Inserting an element using a certified comparison is primitive recursive.
No order laws are needed for the insertion operation itself. -/
theorem orderedInsert {r : α → α → Prop} [DecidableRel r]
    (hr : PrimrecRel r) : Primrec₂ (List.orderedInsert r) := by
  have hstep : Primrec₂ fun (p : α × List α) (t : α × List α × List α) =>
      if r p.1 t.1 then p.1 :: t.1 :: t.2.1 else t.1 :: t.2.2 :=
    (Primrec.ite (hr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  exact (Primrec.list_rec Primrec.snd
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) hstep).of_eq fun p => by
      rcases p with ⟨a, l⟩
      dsimp
      induction l with
      | nil => rfl
      | cons b l ih => simp [List.orderedInsert, ih]

/-- Insertion sort is primitive recursive for every primitive-recursive
comparison, whether or not it satisfies order laws. -/
theorem insertionSort {r : α → α → Prop} [DecidableRel r]
    (hr : PrimrecRel r) : Primrec (List.insertionSort r) :=
  Primrec.list_foldr Primrec.id (Primrec.const [])
    ((orderedInsert hr).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

/-- For an order relation, mathlib's merge sort has the same output as
insertion sort and therefore is primitive recursive as well. -/
theorem mergeSort {r : α → α → Prop} [DecidableRel r]
    [IsTrans α r] [Std.Total r] [Std.Antisymm r]
    (hr : PrimrecRel r) :
    Primrec (fun l : List α => l.mergeSort (fun a b => decide (r a b))) :=
  (insertionSort hr).of_eq fun l => (List.mergeSort_eq_insertionSort r l).symm

/-- Membership in a finite list is primitive recursive under its existing
element and list encodings. -/
theorem list_mem : PrimrecRel (fun (a : α) (l : List α) => a ∈ l) :=
  ((Primrec.eq : PrimrecRel (@Eq α)).exists_mem_list.swap).of_eq fun a l => by simp

/-- Rejecting duplicate entries in a decoded list is a primitive-recursive
predicate. -/
theorem list_nodup : PrimrecPred (@List.Nodup α) := by
  letI := Encodable.decidableEqOfEncodable α
  refine ⟨inferInstance, ?_⟩
  have hstep : Primrec₂ fun (_ : List α) (t : α × List α × Bool) =>
      decide (t.1 ∉ t.2.1) && t.2.2 :=
    (Primrec.and.comp
      ((list_mem.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).not.decide)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const true) hstep).of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a l ih =>
        simpa [List.nodup_cons] using congrArg (fun b => decide (a ∉ l) && b) ih

/-- Ordinary list duplicate removal is primitive recursive. -/
theorem list_dedup [DecidableEq α] : Primrec (@List.dedup α _) := by
  have hstep : Primrec₂ fun (_ : List α) (t : α × List α × List α) =>
      if t.1 ∈ t.2.1 then t.2.2 else t.1 :: t.2.2 :=
    (Primrec.ite
      (list_mem.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hstep).of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a l ih =>
        simpa [List.dedup_cons] using
          congrArg (fun xs => if a ∈ l then xs else a :: xs) ih

end Alexander313.Carlson.PrimitiveListData
