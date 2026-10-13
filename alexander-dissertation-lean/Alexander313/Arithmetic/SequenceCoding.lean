import Alexander313.Arithmetic.PositiveCertificates
import Mathlib.Logic.Godel.GodelBetaFunction

/-!
# Concrete arithmetic graphs for pairing and finite beta-coded sequences

These formulas use only equality, addition, multiplication, successor,
conjunction, disjunction and existential quantifiers. Their standard-number
meanings and PA certificates are proved. Gödel's beta lemma then supplies
actual natural-number parameters representing any given finite list.

This is finite-sequence infrastructure, not yet the arithmetic formula
asserting that a coded list is a correct universal-program execution trace.
-/

namespace Alexander313

/-- Ports 0,1 represent a strict order comparison; variable 2 is local. -/
def strictOrderGraph (Owner : Type) : Formula Owner :=
  .ex 2 (.equal (.var 1) (.add (.var 0) (.succ (.var 2))))

theorem strictOrderGraph_positive (Owner : Type) :
    (strictOrderGraph Owner).PositiveExistential := by
  simp [strictOrderGraph, Formula.PositiveExistential]

theorem strictOrderGraph_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (strictOrderGraph Owner) s ↔ s 0 < s 1 := by
  simp only [strictOrderGraph, truth, Term.eval]
  simp only [Function.update_self, Function.update_of_ne (by decide : 1 ≠ 2),
    Function.update_of_ne (by decide : 0 ≠ 2)]
  constructor
  · rintro ⟨z, hz⟩
    omega
  · intro h
    exact ⟨s 1 - s 0 - 1, by omega⟩

/-- The graph of mathlib's actual square pairing. Ports 0,1 are the
    components; port 2 is the paired value. Variable 3 is local. -/
def pairGraph (Owner : Type) : Formula Owner :=
  .disj
    (.conj (.ex 3 (.equal (.var 1) (.add (.var 0) (.succ (.var 3)))))
      (.equal (.var 2) (.add (.mul (.var 1) (.var 1)) (.var 0))))
    (.conj (.ex 3 (.equal (.var 0) (.add (.var 1) (.var 3))))
      (.equal (.var 2) (.add (.add (.mul (.var 0) (.var 0)) (.var 0)) (.var 1))))

theorem pairGraph_positive (Owner : Type) : (pairGraph Owner).PositiveExistential := by
  simp [pairGraph, Formula.PositiveExistential]

theorem pairGraph_variables (Owner : Type) : (pairGraph Owner).freeVars = {0, 1, 2} := by
  ext v
  simp [pairGraph, Formula.freeVars, Term.freeVars] <;> omega

theorem pairGraph_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (pairGraph Owner) s ↔ s 2 = Nat.pair (s 0) (s 1) := by
  have hlt : (∃ z, s 1 = s 0 + (z + 1)) ↔ s 0 < s 1 := by
    constructor
    · rintro ⟨z, hz⟩
      omega
    · intro h
      exact ⟨s 1 - s 0 - 1, by omega⟩
  have hle : (∃ z, s 0 = s 1 + z) ↔ s 1 ≤ s 0 := by
    constructor
    · rintro ⟨z, hz⟩
      omega
    · intro h
      exact ⟨s 0 - s 1, by omega⟩
  simp only [pairGraph, truth, Term.eval]
  simp only [Function.update_self, Function.update_of_ne (by decide : 1 ≠ 3),
    Function.update_of_ne (by decide : 0 ≠ 3), hlt, hle]
  by_cases h : s 0 < s 1
  · simp [Nat.pair, h, Nat.not_le_of_gt h]
  · have hle' : s 1 ≤ s 0 := by omega
    simp [Nat.pair, h, hle']

/-- Ports 0,1 are beta parameters a,b; port 2 is the position i;
    port 3 is the entry r. Variables 4,5 are quotient/slack witnesses. -/
def betaGraph (Owner : Type) : Formula Owner :=
  let modulus : Term := .succ (.mul (.succ (.var 2)) (.var 1))
  .ex 4 (.conj
    (.equal (.var 0) (.add (.mul (.var 4) modulus) (.var 3)))
    (.ex 5 (.equal modulus (.add (.var 3) (.succ (.var 5))))))

theorem betaGraph_positive (Owner : Type) : (betaGraph Owner).PositiveExistential := by
  simp [betaGraph, Formula.PositiveExistential]

theorem betaGraph_arithmetic (Owner : Type) : (betaGraph Owner).Arithmetic :=
  Formula.positiveExistential_arithmetic _ (betaGraph_positive Owner)

theorem betaGraph_variables (Owner : Type) : (betaGraph Owner).freeVars = {0, 1, 2, 3} := by
  ext v
  simp [betaGraph, Formula.freeVars, Term.freeVars] <;> omega

theorem remainder_witness_iff (a modulus r : Nat) (hmod : 0 < modulus) :
    (∃ q, a = q * modulus + r ∧ ∃ z, modulus = r + (z + 1)) ↔ a % modulus = r := by
  constructor
  · rintro ⟨q, ha, z, hz⟩
    have hr : r < modulus := by omega
    rw [ha]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro h
    have hr : r < modulus := by simpa only [h] using Nat.mod_lt a hmod
    refine ⟨a / modulus, ?_, modulus - r - 1, by omega⟩
    have hd := Nat.mod_add_div a modulus
    rw [h] at hd
    simpa only [Nat.mul_comm, Nat.add_comm] using hd.symm

theorem betaGraph_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (betaGraph Owner) s ↔
      s 0 % ((s 2 + 1) * s 1 + 1) = s 3 := by
  simp only [betaGraph, truth, Term.eval]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : 0 ≠ 4),
    Function.update_of_ne (by decide : 1 ≠ 4),
    Function.update_of_ne (by decide : 2 ≠ 4),
    Function.update_of_ne (by decide : 3 ≠ 4),
    Function.update_of_ne (by decide : 1 ≠ 5),
    Function.update_of_ne (by decide : 2 ≠ 5),
    Function.update_of_ne (by decide : 3 ≠ 5)]
  exact remainder_witness_iff _ _ _ (by omega)

def betaAssignment (a b i r : Nat) : Assignment :=
  fun v => if v = 0 then a else if v = 1 then b else if v = 2 then i else if v = 3 then r else 0

theorem betaEntry_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b i r : Nat) :
    truth filtered P (betaGraph Owner) (betaAssignment a b i r) ↔
      a % ((i + 1) * b + 1) = r := by
  simpa [betaAssignment] using betaGraph_truth filtered P (betaAssignment a b i r)

/-- The paired version agrees exactly with mathlib's beta convention. -/
theorem betaEntry_beta {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b i r : Nat) :
    truth filtered P (betaGraph Owner) (betaAssignment a b i r) ↔
      Nat.beta (Nat.pair a b) i = r := by
  simpa only [Nat.beta, Nat.unpair_pair] using betaEntry_truth filtered P a b i r

/-- Actual parameters representing every entry of any supplied finite
    list, derived from the proved beta/Chinese-remainder construction. -/
theorem finite_sequence_parameters {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (l : List Nat) :
    ∃ a b, ∀ i : Fin l.length,
      truth filtered P (betaGraph Owner) (betaAssignment a b i l[i]) := by
  refine ⟨(Nat.unbeta l).unpair.1, (Nat.unbeta l).unpair.2, ?_⟩
  intro i
  apply (betaEntry_truth filtered P _ _ _ _).mpr
  exact Nat.beta_unbeta_coe l i

theorem pa_proves_pair_instance (Owner : Type) (a b : Nat) :
    Provable (PAInstance Owner)
      ((pairGraph Owner).close (fun v => if v = 0 then a else if v = 1 then b
        else if v = 2 then Nat.pair a b else 0)) := by
  apply pa_proves_positive_numeral_instance _ (pairGraph_positive Owner)
  apply (pairGraph_truth false (fun _ _ => False) _).mpr
  simp

theorem pa_proves_beta_instance (Owner : Type) (a b i r : Nat)
    (h : a % ((i + 1) * b + 1) = r) :
    Provable (PAInstance Owner) ((betaGraph Owner).close (betaAssignment a b i r)) :=
  pa_proves_positive_numeral_instance _ (betaGraph_positive Owner) _
    ((betaEntry_truth false (fun _ _ => False) a b i r).mpr h)

/-- All entries of a finite beta-coded sequence have genuine finite PA
    certificates; the shared parameters are actual natural numbers. -/
theorem finite_sequence_pa_certificates (Owner : Type) (l : List Nat) :
    ∃ a b, ∀ i : Fin l.length,
      Provable (PAInstance Owner)
        ((betaGraph Owner).close (betaAssignment a b i l[i])) := by
  obtain ⟨a, b, h⟩ := finite_sequence_parameters false (fun (_ : Owner) _ => False) l
  refine ⟨a, b, fun i => ?_⟩
  apply pa_proves_beta_instance Owner a b i l[i]
  exact (betaEntry_truth false (fun (_ : Owner) _ => False) a b i l[i]).mp (h i)

end Alexander313
