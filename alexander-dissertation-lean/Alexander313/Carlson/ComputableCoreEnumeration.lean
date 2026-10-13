import Alexander313.Carlson.CanonicalPointedCodes
import Alexander313.Carlson.CoreTallness
import Mathlib.Data.Fintype.EquivFin

/-!
# A computable duplicate-free enumeration of the entire Carlson core

Enumerate the canonical codes in increasing *natural-code* order. Infinitude
of the actual core proves that each next-code search terminates. The label
map is a bijection from all naturals onto the original ordinal initial
segment. Natural-code order is not asserted to be ordinal order: the latter
and both ordinal relations are computed by the existing comparison machine.
-/

namespace Alexander313.Carlson.ComputableCoreEnumeration

open ComputablePointedPresentation CanonicalPointedCodes

/-- Finitely many raw codes cannot exhaust the actual infinite core. -/
theorem canonical_unbounded (b : ℕ) : ∃ k, b ≤ k ∧ Canonical k := by
  classical
  letI := infinite_core
  let f : ℕ → Set.Iio coreBound := fun n => ⟨label n, label_lt_coreBound n⟩
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ((Finset.range b).image f)
  obtain ⟨n, hn⟩ := label_surjective a.val a.property
  refine ⟨representative n, ?_, representative_canonical n⟩
  by_contra h
  apply ha
  refine Finset.mem_image.mpr ⟨representative n,
    Finset.mem_range.mpr (Nat.lt_of_not_ge h), ?_⟩
  exact Subtype.ext ((representative_label n).trans hn)

def checkNext (b k : ℕ) : Bool := decide (b ≤ k) && checkCanonical k

theorem checkNext_eq_true (b k : ℕ) : checkNext b k = true ↔ b ≤ k ∧ Canonical k := by
  simp only [checkNext, Bool.and_eq_true, decide_eq_true_eq, checkCanonical_eq_true]

theorem checkNext_computable : Computable₂ checkNext := by
  have hle : Computable₂ (fun b k : ℕ => decide (b ≤ k)) := Primrec.nat_le.decide.to_comp
  have hand : Computable₂ Bool.and := Primrec.and.to_comp
  exact hand.comp hle (checkCanonical_computable.comp Computable.snd)

theorem exists_next (b : ℕ) : ∃ k, checkNext b k = true := by
  obtain ⟨k, hk⟩ := canonical_unbounded b
  exact ⟨k, (checkNext_eq_true b k).mpr hk⟩

/-- Least canonical code at or above the supplied natural lower bound. -/
def next (b : ℕ) : ℕ := Nat.find (exists_next b)

theorem next_spec (b : ℕ) : b ≤ next b ∧ Canonical (next b) :=
  (checkNext_eq_true b (next b)).mp (Nat.find_spec (exists_next b))

theorem next_le {b k : ℕ} (hb : b ≤ k) (hk : Canonical k) : next b ≤ k :=
  Nat.find_min' (exists_next b) ((checkNext_eq_true b k).mpr ⟨hb, hk⟩)

theorem next_computable : Computable next :=
  find_computable checkNext checkNext_computable exists_next

/-- Every natural index is assigned a distinct canonical code. -/
def enumerate : ℕ → ℕ
  | 0 => 0
  | n + 1 => next (enumerate n + 1)

theorem enumerate_canonical (n : ℕ) : Canonical (enumerate n) := by
  cases n with
  | zero => exact canonical_zero
  | succ n => exact (next_spec (enumerate n + 1)).2

theorem enumerate_lt_succ (n : ℕ) : enumerate n < enumerate (n + 1) :=
  (Nat.lt_succ_self (enumerate n)).trans_le (next_spec (enumerate n + 1)).1

theorem enumerate_strictMono : StrictMono enumerate :=
  strictMono_nat_of_lt_succ enumerate_lt_succ

theorem index_le_enumerate (n : ℕ) : n ≤ enumerate n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := enumerate_lt_succ n
    omega

/-- The next-code searches skip no canonical code. -/
theorem enumerate_surjective (k : ℕ) (hk : Canonical k) : ∃ n, enumerate n = k := by
  have hex : ∃ n, k ≤ enumerate n := ⟨k, index_le_enumerate k⟩
  let n := Nat.find hex
  have hn : k ≤ enumerate n := Nat.find_spec hex
  refine ⟨n, Nat.le_antisymm ?_ hn⟩
  cases he : n with
  | zero => exact Nat.zero_le _
  | succ t =>
    have ht : t < Nat.find hex := by
      change t < n
      rw [he]
      exact Nat.lt_succ_self _
    have hp : ¬ k ≤ enumerate t := Nat.find_min hex ht
    have hb : enumerate t + 1 ≤ k := by omega
    exact next_le hb hk

theorem enumerate_computable : Computable enumerate := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => next (p.2 + 1)) :=
    next_computable.comp (Computable.succ.comp (Computable.snd.comp Computable.snd))
  have hrec := Computable.nat_rec Computable.id (Computable.const 0) hstep
  apply hrec.of_eq
  intro n
  change Nat.rec 0 (fun (_ : ℕ) (r : ℕ) => next (r + 1)) n = enumerate n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun r => next (r + 1)) ih

noncomputable def value (n : ℕ) : Ordinal.{0} := label (enumerate n)

theorem value_lt_coreBound (n : ℕ) : value n < coreBound :=
  label_lt_coreBound (enumerate n)

theorem value_injective : Function.Injective value := by
  intro m n h
  apply enumerate_strictMono.injective
  exact canonical_label_injective (enumerate_canonical m) (enumerate_canonical n) h

theorem value_surjective (a : Ordinal.{0}) (ha : a < coreBound) : ∃ n, value n = a := by
  obtain ⟨k, hk⟩ := label_surjective a ha
  obtain ⟨n, hn⟩ := enumerate_surjective (representative k) (representative_canonical k)
  refine ⟨n, ?_⟩
  change label (enumerate n) = a
  rw [hn, representative_label]
  exact hk

noncomputable def toCore (n : ℕ) : Set.Iio coreBound :=
  ⟨value n, value_lt_coreBound n⟩

theorem toCore_bijective : Function.Bijective toCore := by
  constructor
  · intro m n h
    exact value_injective (congrArg Subtype.val h)
  · intro a
    obtain ⟨n, hn⟩ := value_surjective a.val a.property
    exact ⟨n, Subtype.ext hn⟩

/-- This equivalence uses the explicit enumeration in its forward direction;
choice in the semantic inverse is not part of any executable algorithm. -/
noncomputable def coreEquiv : ℕ ≃ Set.Iio coreBound :=
  Equiv.ofBijective toCore toCore_bijective

def compare (m n : ℕ) : Answers :=
  ComputablePointedPresentation.comparison (enumerate m) (enumerate n)

theorem compare_computable : Computable₂ compare :=
  comparison_computable.comp (enumerate_computable.comp Computable.fst)
    (enumerate_computable.comp Computable.snd)

theorem compare_correct (m n : ℕ) :
    ((compare m n).1 = true ↔ value m = value n) ∧
    ((compare m n).2.1 = true ↔ value m ≤ value n) ∧
    ((compare m n).2.2.1 = true ↔ value m < value n) ∧
    ((compare m n).2.2.2.1 = true ↔ R1 (value m) (value n)) ∧
    ((compare m n).2.2.2.2 = true ↔ R2 (value m) (value n)) :=
  comparison_correct (enumerate m) (enumerate n)

theorem compare_eq_iff (m n : ℕ) : (compare m n).1 = true ↔ m = n :=
  (compare_correct m n).1.trans value_injective.eq_iff

theorem enumeration_program : ∃ machine : Nat.Partrec.Code, ∀ n : ℕ,
    machine.eval n = Part.some (enumerate n) := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp enumerate_computable
  refine ⟨machine, fun n => ?_⟩
  rw [hm]
  simp

/-- All actual relation answers on the all-natural, duplicate-free core
presentation are returned by one total machine. -/
theorem comparison_program : ∃ machine : Nat.Partrec.Code, ∀ m n : ℕ,
    machine.eval (Nat.pair m n) = Part.some (Encodable.encode (compare m n)) := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp compare_computable
  refine ⟨machine, fun m n => ?_⟩
  rw [hm]
  change (Part.bind (Part.ofOption (Encodable.decode (Encodable.encode (m, n))))
    (fun s : ℕ × ℕ => (Part.some (compare s.1 s.2)).map Encodable.encode)) = _
  simp only [Encodable.encodek, Part.ofOption, Part.bind_some, Part.map_some]

end Alexander313.Carlson.ComputableCoreEnumeration
