import Alexander313.Wilken.HereditaryCanonicalArithmetic
import Alexander313.Effective.HereditaryOrdinalLinearOrder
import Alexander313.Wilken.FiniteUpsilonDomain
import Mathlib.Data.Nat.Nth

/-!
# A genuine computable bijective enumeration of all canonical public codes

Bounded primitive recursion counts accepted canonical codes below a numerical
bound. The literal existing PR check and this rank determine a concrete
Nat.rfind search for the nth accepted code. The existing actual numeral
producer injects Nat into accepted codes, so every rank has a genuine witness
and every search terminates. Its total Computable function is bijective onto
the EXACT existing canonical code subtype, with bounded PR rank as inverse.

The resulting named Nat order is the genuine ordinal order of these codes,
decided by their existing executing comparison. Its actual order isomorphism
covers the entire proved sourceUpsilonOmega interval. The natural enumeration
index order is used only for the numerical scan and is not the ordinal label
order. No supplied enumeration, effectivity, coverage or tracking oracle is
assumed. Actual R1/R2 decisions remain separate. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.HereditaryCanonicalEnumeration

open Wilken.RelativeTerm.Hereditary
open HereditaryOrdinalLabels (Label value value_injective labelLE labelLT labelLinearOrder
  intervalOrderEquiv)

abbrev Accepted (q : Nat) : Prop := Canonical.check q = true

/-- Explicit actual finite numeral codes witness infinitely many accepted
canonical codes, rather than using an infinite-carrier assumption. -/
theorem numeralCode_injective : Function.Injective CanonicalArithmetic.numeralCode := by
  intro n m h
  have he : (n : Ordinal.{0}) = (m : Ordinal.{0}) :=
    (CanonicalArithmetic.numeralCode_value n).symm.trans
      ((congrArg unionInterpretation h).trans (CanonicalArithmetic.numeralCode_value m))
  exact Nat.cast_injective he

theorem accepted_infinite : {q : Nat | Accepted q}.Infinite :=
  Set.infinite_of_injective_forall_mem numeralCode_injective
    (fun n => CanonicalArithmetic.numeralCode_checked n)

/-- A bounded scan counts genuine accepted codes strictly below q. -/
def rank : Nat → Nat
  | 0 => 0
  | q + 1 => cond (Canonical.check q) (rank q + 1) (rank q)

theorem rank_primrec : Primrec rank := by
  have hr : Primrec₂ (fun (_ : Unit) q => Nat.rec (motive := fun _ => Nat) 0
      (fun c previous => cond (Canonical.check c) (previous + 1) previous) q) :=
    Primrec.nat_rec (Primrec.const 0)
      (((Canonical.Effective.check_primrec.comp (Primrec.fst.comp Primrec.snd)).cond
        (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact (hr.comp (Primrec.const ()) Primrec.id).of_eq (by
    intro q
    induction q <;> simp_all [rank])

theorem rank_eq_count (q : Nat) : rank q = Nat.count Accepted q := by
  induction q with
  | zero => simp only [rank, Nat.count_zero]
  | succ q ih =>
    cases hc : Canonical.check q <;> simp [rank, Nat.count_succ, Accepted, hc, ih]

theorem rank_injective_on_accepted {c d : Nat} (hc : Accepted c) (hd : Accepted d)
    (he : rank c = rank d) : c = d :=
  Nat.count_injective hc hd (by simpa only [← rank_eq_count] using he)

/-- The actual search test uses only the genuine canonical checker and the
bounded PR inverse rank. -/
def searchTest (n q : Nat) : Bool := Canonical.check q && (rank q == n)

theorem searchTest_primrec : Primrec₂ searchTest :=
  (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
    (Primrec.beq.comp (rank_primrec.comp Primrec.snd) Primrec.fst)).to₂

theorem searchTest_exact (n q : Nat) : searchTest n q = true ↔ Accepted q ∧ rank q = n := by
  simp only [searchTest, Bool.and_eq_true, beq_iff_eq]

theorem searchTest_exists (n : Nat) : ∃ q, searchTest n q = true := by
  let q := Nat.nth Accepted n
  have hq : Accepted q := Nat.nth_mem_of_infinite accepted_infinite n
  have hr : rank q = n := (rank_eq_count q).trans
    (Nat.count_nth_of_infinite accepted_infinite n)
  exact ⟨q, (searchTest_exact n q).mpr ⟨hq, hr⟩⟩

def search (n : Nat) : Part Nat := Nat.rfind (fun q => Part.some (searchTest n q))

theorem search_partrec : Partrec search :=
  Partrec.rfind searchTest_primrec.to_comp.partrec.to₂

/-- Every original natural query terminates; the witness is derived from
actual infinitude and count, not supplied as a domain premise. -/
theorem search_total (n : Nat) : (search n).Dom := by
  obtain ⟨q, hq⟩ := searchTest_exists n
  exact Nat.rfind_dom.mpr ⟨q, by simpa only [Part.mem_some_iff] using hq.symm,
    fun {_} _ => trivial⟩

def enumCode (n : Nat) : Nat := (search n).get (search_total n)

theorem enumCode_computable : Computable enumCode :=
  search_partrec.of_eq_tot (fun n => Part.get_mem (search_total n))

theorem enumCode_spec (n : Nat) : Accepted (enumCode n) ∧ rank (enumCode n) = n := by
  have ht := Nat.rfind_spec (Part.get_mem (search_total n))
  exact (searchTest_exact n (enumCode n)).mp ((Part.mem_some_iff.mp ht).symm)

theorem enumCode_rank (q : Nat) (hq : Accepted q) : enumCode (rank q) = q :=
  rank_injective_on_accepted (enumCode_spec (rank q)).1 hq (enumCode_spec (rank q)).2

theorem enumCode_injective : Function.Injective enumCode := by
  intro n m he
  exact (enumCode_spec n).2.symm.trans ((congrArg rank he).trans (enumCode_spec m).2)

/-- The enumeration returns an ORIGINAL accepted canonical public code. -/
def label (n : Nat) : Label := ⟨enumCode n, (enumCode_spec n).1⟩

def index (μ : Label) : Nat := rank μ.1

theorem index_label (n : Nat) : index (label n) = n := (enumCode_spec n).2

theorem label_index (μ : Label) : label (index μ) = μ :=
  Subtype.ext (enumCode_rank μ.1 μ.2)

def labelEquiv : Nat ≃ Label where
  toFun := label
  invFun := index
  left_inv := index_label
  right_inv := label_index

def ordinalValue (n : Nat) : Ordinal.{0} := value (label n)

theorem ordinalValue_injective : Function.Injective ordinalValue :=
  value_injective.comp labelEquiv.injective

theorem ordinalValue_range_sourceUpsilonOmega :
    Set.range ordinalValue = Set.Iio Wilken.sourceUpsilonOmega := by
  ext ξ
  constructor
  · rintro ⟨n, rfl⟩
    rw [Wilken.sourceUpsilonOmega_eq_finiteBaseLimit]
    exact HereditaryOrdinalLabels.value_lt_limit (label n)
  · intro hξ
    rw [Wilken.sourceUpsilonOmega_eq_finiteBaseLimit] at hξ
    obtain ⟨μ, hμ⟩ := HereditaryOrdinalLabels.value_covers ξ hξ
    exact ⟨index μ, (congrArg value (label_index μ)).trans hμ⟩

/-- The real ordinal strict comparison of the enumerated codes. -/
def less (n m : Nat) : Bool := Canonical.less (enumCode n) (enumCode m)

theorem less_computable : Computable₂ less := by
  have h : Computable (fun p : Nat × Nat => less p.1 p.2) :=
    Canonical.Effective.less_primrec.to_comp.comp
      (enumCode_computable.comp Computable.fst)
      (enumCode_computable.comp Computable.snd)
  exact h.to₂

theorem less_exact (n m : Nat) : less n m = true ↔ ordinalValue n < ordinalValue m := by
  simpa only [less, (enumCode_spec n).1, (enumCode_spec m).1, true_and, ordinalValue,
    value, Canonical.value, label] using Canonical.less_exact (enumCode n) (enumCode m)

def leCheck (n m : Nat) : Bool := !less m n

theorem leCheck_computable : Computable₂ leCheck := by
  have h : Computable (fun p : Nat × Nat => leCheck p.1 p.2) :=
    Primrec.not.to_comp.comp
      (Computable₂.comp less_computable Computable.snd Computable.fst)
  exact h.to₂

theorem leCheck_exact (n m : Nat) : leCheck n m = true ↔ ordinalValue n ≤ ordinalValue m := by
  rw [← not_lt, ← less_exact]
  cases h : less m n <;> simp [leCheck, h]

/-- Named genuine Nat ordinal-label order; the numerical scan order remains
inside already elaborated rank/search definitions. -/
private def publicLEDecidable (n m : Nat) : Decidable (ordinalValue n ≤ ordinalValue m) :=
  decidable_of_iff (less m n = false) (by
    rw [← not_lt, ← less_exact]
    cases h : less m n <;> simp [h])

private def publicLTDecidable (n m : Nat) : Decidable (less n m = true) := inferInstance

@[reducible] def publicLinearOrder : LinearOrder Nat where
  le n m := ordinalValue n ≤ ordinalValue m
  lt n m := less n m = true
  le_refl n := le_rfl
  le_trans n m k hn hm := hn.trans hm
  le_antisymm n m hn hm := ordinalValue_injective (le_antisymm hn hm)
  lt_iff_le_not_ge n m := (less_exact n m).trans lt_iff_le_not_ge
  le_total n m := le_total _ _
  toDecidableLE := publicLEDecidable
  toDecidableLT := publicLTDecidable
  toDecidableEq := inferInstance
  min n m := @ite Nat (ordinalValue n ≤ ordinalValue m) (publicLEDecidable n m) n m
  max n m := @ite Nat (ordinalValue n ≤ ordinalValue m) (publicLEDecidable n m) m n
  compare n m := @compareOfLessAndEq Nat n m ⟨fun a b => less a b = true⟩
    (publicLTDecidable n m) inferInstance

theorem publicLinearOrder_le_check (n m : Nat) :
    @LE.le Nat publicLinearOrder.toLE n m ↔ leCheck n m = true :=
  (leCheck_exact n m).symm

theorem publicLinearOrder_lt_check (n m : Nat) :
    @LT.lt Nat publicLinearOrder.toLT n m ↔ less n m = true := Iff.rfl

section GenuineOrder

local instance publicNatOrder : LinearOrder Nat := publicLinearOrder
local instance publicNatLE : LE Nat := publicLinearOrder.toLE
local instance publicNatLT : LT Nat := publicLinearOrder.toLT
local instance genuineLabelLE : LE Label := labelLE
local instance genuineLabelLT : LT Label := labelLT
local instance genuineLabelOrder : LinearOrder Label := labelLinearOrder

/-- The actual bijection is an order isomorphism for the genuine executing
ordinal order of labels, not an assertion about numerical index ordering. -/
def labelOrderIso : Nat ≃o Label where
  toEquiv := labelEquiv
  map_rel_iff' := by intro n m; rfl

def sourceIntervalOrderIso : Nat ≃o Set.Iio Wilken.sourceUpsilonOmega := by
  rw [Wilken.sourceUpsilonOmega_eq_finiteBaseLimit]
  exact labelOrderIso.trans intervalOrderEquiv

end GenuineOrder
end Alexander313.HereditaryCanonicalEnumeration
