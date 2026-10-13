import Alexander313.Effective.LiteralFormation
import Alexander313.Alexander.SourceLabelFormation

/-!
# Effective numeral instances from literal finite assignments

Only the finitely many free variables of a formula matter. A literal list
of numbers gives a total assignment by defaulting to zero. A fold of the
already constructed single-variable numeral substitutions computes exactly
the corresponding closed formula, with binder shadowing inherited from
each substitution. Every arbitrary assignment has such a finite-list
representative for a given formula.
-/

namespace Alexander313
namespace FiniteAssignment

def assignment (L : List Nat) (x : Nat) : Nat := L[x]?.getD 0

theorem assignment_primrec : Primrec₂ assignment :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const 0)).to₂

def replaceList (xs : List Nat) (L : List Nat) (φ : Formula Nat) : Formula Nat :=
  xs.foldr (fun x previous => previous.subst (singleNumeralSubstitution x (assignment L x))) φ

theorem replaceList_primrec : Primrec (fun p : (List Nat × List Nat) × Formula Nat =>
    replaceList p.1.1 p.1.2 p.2) := by
  have hstep : Primrec₂ (fun (p : (List Nat × List Nat) × Formula Nat)
      (s : Nat × Formula Nat) => s.2.subst (singleNumeralSubstitution s.1 (assignment p.1.2 s.1))) := by
    have hx : Primrec (fun p : ((List Nat × List Nat) × Formula Nat) × (Nat × Formula Nat) =>
        p.2.1) := Primrec.fst.comp Primrec.snd
    have hL : Primrec (fun p : ((List Nat × List Nat) × Formula Nat) × (Nat × Formula Nat) =>
        p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hvalue := assignment_primrec.comp hL hx
    exact (Formula.singleNumeralSubst_primrec.comp
      ((hx.pair hvalue).pair (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.list_foldr (Primrec.fst.comp Primrec.fst) Primrec.snd hstep

theorem replaceList_eq_subst (xs L : List Nat) (φ : Formula Nat) :
    replaceList xs L φ = φ.subst (fun x => if x ∈ xs then some (assignment L x) else none) := by
  induction xs with
  | nil => simp [replaceList]
  | cons x xs ih =>
    change (replaceList xs L φ).subst (singleNumeralSubstitution x (assignment L x)) = _
    rw [ih, Formula.subst_compose]
    congr 1
    funext y
    by_cases hyx : y = x
    · subst y
      by_cases hxs : x ∈ xs <;>
        simp [NumericalSubstitution.compose, singleNumeralSubstitution, hxs, List.mem_cons]
    · by_cases hys : y ∈ xs <;>
        simp [NumericalSubstitution.compose, singleNumeralSubstitution, hys, hyx, List.mem_cons]

def close (φ : Formula Nat) (L : List Nat) : Formula Nat :=
  replaceList (φ.freeVars.sort (· ≤ ·)) L φ

theorem close_eq (φ : Formula Nat) (L : List Nat) : close φ L = φ.close (assignment L) := by
  rw [close, replaceList_eq_subst]
  apply Formula.subst_eq_of_agree
  intro x hx
  simp only [Finset.mem_sort, hx, if_true]

theorem close_primrec : Primrec₂ close :=
  (replaceList_primrec.comp
    (((Formula.freeVariables_primrec.comp Primrec.fst).pair Primrec.snd).pair Primrec.fst)).to₂

theorem close_closed (φ : Formula Nat) (L : List Nat) : (close φ L).Closed := by
  rw [close_eq]
  exact φ.close_closed _

theorem assignment_range_map (s : Assignment) (n x : Nat) (hx : x < n) :
    assignment ((List.range n).map s) x = s x := by
  simp [assignment, List.getElem?_range hx]

theorem represents (φ : Formula Nat) (s : Assignment) :
    ∃ L : List Nat, φ.close s = close φ L := by
  refine ⟨(List.range (φ.code id)).map s, ?_⟩
  rw [close_eq]
  apply φ.close_eq_of_agree
  intro x hx
  exact (assignment_range_map s _ x (φ.freeVars_lt_code hx)).symm

theorem instances_iff {φ σ : Formula Nat} :
    (∃ s : Assignment, σ = φ.close s) ↔ ∃ L : List Nat, σ = close φ L := by
  constructor
  · rintro ⟨s, rfl⟩
    exact represents φ s
  · rintro ⟨L, rfl⟩
    exact ⟨assignment L, close_eq φ L⟩

end FiniteAssignment
end Alexander313
