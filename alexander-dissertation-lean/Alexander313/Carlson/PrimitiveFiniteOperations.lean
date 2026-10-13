import Alexander313.Carlson.PrimitiveFiniteData
import Alexander313.Carlson.PrimitiveRationalData
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Primitive-recursive operations on the stored finite-set codes

The canonical list view from `PrimitiveFiniteData` exposes the elements of
the existing finite-set encoding. List computations followed by `toFinset`
certify the finite operations used by rational presentations and liftings.
The encoding of every input and result remains unchanged.

Parameterized filtering, image, and bounded quantifiers require a genuine
primitive-recursive proof of their supplied function or predicate. The
concrete rational programs below discharge those hypotheses for membership,
union, and strict initial-segment filtering. Their machine specifications
are on canonical typed inputs; malformed raw inputs are not specified here.
-/

namespace Alexander313.Carlson.PrimitiveFiniteOperations

open Encodable PrimitiveFiniteData

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

/-- Cardinality reads the length of the canonical list. -/
theorem finset_card : Primrec (@Finset.card α) :=
  (Primrec.list_length.comp finsetView_primrec).of_eq length_finsetView

/-- A certified predicate can be filtered over a supplied finite carrier. -/
theorem finset_filter {p : α → β → Prop} [DecidableRel p]
    (hp : PrimrecRel p) :
    Primrec₂ (fun a (s : Finset β) => s.filter (p a)) := by
  letI := Encodable.decidableEqOfEncodable β
  have hflip : PrimrecRel (fun b a => p a b) := hp.comp Primrec.snd Primrec.fst
  refine (list_toFinset.comp
    (hflip.listFilter.comp (finsetView_primrec.comp Primrec.snd) Primrec.fst)).of_eq ?_
  intro q
  ext b
  simp

/-- The image of a supplied finite set under a certified map. -/
theorem finset_image [DecidableEq γ] {f : α → β → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun a (s : Finset β) => s.image (f a)) := by
  refine (list_toFinset.comp
    (Primrec.list_map (finsetView_primrec.comp Primrec.snd)
      (hf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).of_eq ?_
  intro q
  ext b
  simp [mem_finsetView]

/-- Bounded existential quantification over a coded finite set. -/
theorem exists_mem {p : α → β → Prop} (hp : PrimrecRel p) :
    PrimrecRel (fun (s : Finset α) b => ∃ a ∈ s, p a b) := by
  refine (hp.exists_mem_list.comp
    (finsetView_primrec.comp Primrec.fst) Primrec.snd).of_eq ?_
  intro q
  simp [mem_finsetView]

/-- Bounded universal quantification over a coded finite set. -/
theorem forall_mem {p : α → β → Prop} (hp : PrimrecRel p) :
    PrimrecRel (fun (s : Finset α) b => ∀ a ∈ s, p a b) := by
  refine (hp.forall_mem_list.comp
    (finsetView_primrec.comp Primrec.fst) Primrec.snd).of_eq ?_
  intro q
  simp [mem_finsetView]

/-- Inclusion is a finite universal membership test. -/
theorem finset_subset : PrimrecRel ((· ⊆ ·) : Finset α → Finset α → Prop) :=
  forall_mem finset_mem

/-- A finite set is nonempty exactly when its cardinality is nonzero. -/
theorem finset_nonempty : PrimrecPred (fun s : Finset α => s.Nonempty) :=
  (Primrec.nat_lt.comp (Primrec.const 0) finset_card).of_eq
    (fun _ => Finset.card_pos)

/-- Disjointness is a bounded test excluding every element of the other set. -/
theorem finset_disjoint : PrimrecRel (Disjoint : Finset α → Finset α → Prop) :=
  (forall_mem finset_mem.not).of_eq (fun _ _ => Finset.disjoint_left.symm)

/-- Union canonicalizes the concatenation of the two element lists. -/
theorem finset_union [DecidableEq α] :
    Primrec₂ ((· ∪ ·) : Finset α → Finset α → Finset α) := by
  refine (list_toFinset.comp (Primrec.list_append.comp
    (finsetView_primrec.comp Primrec.fst)
    (finsetView_primrec.comp Primrec.snd))).of_eq ?_
  intro q
  ext a
  simp

/-- Intersection is a certified membership filter. -/
theorem finset_inter [DecidableEq α] :
    Primrec₂ ((· ∩ ·) : Finset α → Finset α → Finset α) := by
  have hp : PrimrecRel (fun (s : Finset α) a => a ∈ s) :=
    finset_mem.comp Primrec.snd Primrec.fst
  refine ((finset_filter hp).comp Primrec.snd Primrec.fst).of_eq ?_
  intro q
  ext a
  simp

/-- Set difference is the corresponding nonmembership filter. -/
theorem finset_sdiff [DecidableEq α] :
    Primrec₂ ((· \ ·) : Finset α → Finset α → Finset α) := by
  have hp : PrimrecRel (fun (s : Finset α) a => a ∉ s) :=
    finset_mem.not.comp Primrec.snd Primrec.fst
  refine ((finset_filter hp).comp Primrec.snd Primrec.fst).of_eq ?_
  intro q
  ext a
  simp

/-- Insertion uses duplicate-removing conversion from a list. -/
theorem finset_insert [DecidableEq α] :
    Primrec₂ (fun a (s : Finset α) => insert a s) := by
  refine (list_toFinset.comp (Primrec.list_cons.comp Primrec.fst
    (finsetView_primrec.comp Primrec.snd))).of_eq ?_
  intro q
  ext a
  simp

/-- Erasing an element is a certified inequality filter. -/
theorem finset_erase [DecidableEq α] :
    Primrec₂ (fun a (s : Finset α) => s.erase a) := by
  have hp : PrimrecRel (fun a b : α => b ≠ a) :=
    Primrec.eq.not.comp Primrec.snd Primrec.fst
  refine (finset_filter hp).of_eq ?_
  intro a s
  ext b
  simp [and_comm]

/-- Cartesian products enumerate and canonicalize all pairs. -/
theorem finset_product :
    Primrec₂ (fun (s : Finset α) (t : Finset β) => s ×ˢ t) := by
  letI := Encodable.decidableEqOfEncodable (α × β)
  have hlist : Primrec (fun q : Finset α × Finset β =>
      (finsetView q.1).flatMap (fun a => (finsetView q.2).map (Prod.mk a))) :=
    Primrec.list_flatMap (finsetView_primrec.comp Primrec.fst)
      (Primrec.list_map (finsetView_primrec.comp (Primrec.snd.comp Primrec.fst))
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂
  refine (list_toFinset.comp hlist).of_eq ?_
  intro q
  ext ab
  rcases ab with ⟨a, b⟩
  simp [mem_finsetView]

/-- Initial natural-number intervals retain their existing finite-set codes. -/
theorem finset_range : Primrec Finset.range := by
  refine (list_toFinset.comp Primrec.list_range).of_eq ?_
  intro n
  ext a
  simp

/-- A concrete primitive-recursive operation has an actual machine code
with its supplied input and output encodings. -/
theorem exists_program {f : α → β} (hf : Primrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a,
      c.eval (encode a) = Part.some (encode (f a)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  refine ⟨c, fun a => ?_⟩
  rw [hc]
  simp

/-- Rational finite-set membership returns a Boolean answer in the machine language. -/
theorem rational_membership_program : ∃ c : Nat.Partrec.Code,
    ∀ (x : ℚ) (s : Finset ℚ),
      c.eval (Nat.pair (encode x) (encode s)) = Part.some (encode (decide (x ∈ s))) := by
  obtain ⟨c, hc⟩ := exists_program (finset_mem (α := ℚ)).decide
  exact ⟨c, fun x s => hc (x, s)⟩

/-- Rational finite-set union has an implementation using the existing codes. -/
theorem rational_union_program : ∃ c : Nat.Partrec.Code,
    ∀ s t : Finset ℚ,
      c.eval (Nat.pair (encode s) (encode t)) = Part.some (encode (s ∪ t)) := by
  obtain ⟨c, hc⟩ := exists_program (finset_union (α := ℚ))
  exact ⟨c, fun s t => hc (s, t)⟩

/-- The strict initial part of a finite rational carrier is primitive recursive. -/
theorem rational_below :
    Primrec₂ (fun (a : ℚ) (s : Finset ℚ) => s.filter (fun x => x < a)) :=
  finset_filter (PrimitiveRationalData.rat_lt.comp Primrec.snd Primrec.fst)

/-- Strict rational initial-segment filtering has a concrete machine implementation. -/
theorem rational_below_program : ∃ c : Nat.Partrec.Code,
    ∀ (a : ℚ) (s : Finset ℚ),
      c.eval (Nat.pair (encode a) (encode s)) =
        Part.some (encode (s.filter (fun x => x < a))) := by
  obtain ⟨c, hc⟩ := exists_program rational_below
  exact ⟨c, fun a s => hc (a, s)⟩

end Alexander313.Carlson.PrimitiveFiniteOperations
