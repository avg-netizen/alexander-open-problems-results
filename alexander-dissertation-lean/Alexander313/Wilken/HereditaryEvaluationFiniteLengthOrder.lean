import Alexander313.Wilken.HereditaryEvaluationCompleteLengthBound
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.List.Lex
import Mathlib.Order.WellFoundedSet

/-!
# The actual evaluation lengths inhabit a finite lexical order

The genuinely computed original height bounds every actual positive length
and the number of components. Lifting these bounded numerals to Fin gives a
finite set of possible length words. Its ordinary strict lexical relation
is well founded. The output of the real component program lies in that set,
without a supplied length word or bound. The separate recursive evaluation
clauses still have to prove that each actual recursive call decreases this
lexical relation and remains within a common height. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFiniteLengthOrder

open EvaluationComponents.Support
open Hereditary.FinePredecessor (stripLast)

def lengthDomain (h : Nat) : Set (List Nat) :=
  {ns | ns.length ≤ h ∧ ∀ n ∈ ns, 0 < n ∧ n ≤ h}

private theorem bounded_lift (h : Nat) (ns : List Nat)
    (hb : ∀ n ∈ ns, n ≤ h) :
    ∃ xs : List (Fin (h + 1)), xs.map Fin.val = ns := by
  revert hb
  induction ns with
  | nil => intro hb; exact ⟨[], rfl⟩
  | cons n ns ih =>
    intro hb
    obtain ⟨xs, hx⟩ := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    have hn : n < h + 1 := by
      have hl := hb n List.mem_cons_self
      omega
    exact ⟨⟨n, hn⟩ :: xs, by simp only [List.map_cons, hx]⟩

/-- Finiteness is constructed from a genuine bounded numeral alphabet,
not assumed for a set of already generated evaluation traces. -/
theorem lengthDomain_finite (h : Nat) : (lengthDomain h).Finite := by
  have hf : {xs : List (Fin (h + 1)) | xs.length ≤ h}.Finite :=
    List.finite_length_le (Fin (h + 1)) h
  apply (hf.image (fun xs => xs.map Fin.val)).subset
  intro ns hn
  obtain ⟨xs, hx⟩ := bounded_lift h ns (fun n hm => (hn.2 n hm).2)
  refine ⟨xs, ?_, hx⟩
  have hl : xs.length = ns.length := by
    simpa only [List.length_map] using congrArg List.length hx
  change xs.length ≤ h
  rw [hl]
  exact hn.1

theorem lengthDomain_wellFounded (h : Nat) :
    (lengthDomain h).WellFoundedOn (List.Lex (· < ·)) :=
  (lengthDomain_finite h).wellFoundedOn

/-- This version is a relation on ordinary numerical lists, retaining
both domain guards explicitly for a later recursive program. -/
theorem guarded_lex_wellFounded (h : Nat) :
    WellFounded (fun xs ys : List Nat =>
      List.Lex (· < ·) xs ys ∧ xs ∈ lengthDomain h ∧ ys ∈ lengthDomain h) :=
  Set.wellFoundedOn_iff.mp (lengthDomain_wellFounded h)

/-- Genuine execution gives membership at its computed original height;
the only exception is precisely the printed literal fixed endpoint chain. -/
theorem executeLengths_mem (codes ns : List Nat)
    (ho : ns ∈ EvaluationComponents.executeLengths codes)
    (hf : properTail codes = [] →
      codes ≠ GlobalAdditiveTracking.Source.baseWord (segmentIndex (stripLast codes) + 1)) :
    ns ∈ lengthDomain (EvaluationCompleteLengthBound.originalHeight codes + 1) :=
  EvaluationCompleteLengthBound.executeLengths_bounded codes ns ho hf

/-- A strict change at the first affected component dominates every
later component, as required by the chronological source length order. -/
theorem lex_first_changed (prefix left right : List Nat) (small large : Nat)
    (hsmall : small < large) :
    List.Lex (· < ·) (prefix ++ small :: left) (prefix ++ large :: right) :=
  List.Lex.append_left (· < ·) (List.Lex.rel hsmall) prefix

theorem lex_proper_prefix (prefix tail : List Nat) (n : Nat) :
    List.Lex (· < ·) prefix (prefix ++ n :: tail) := by
  simpa only [List.append_nil] using
    List.Lex.append_left (· < ·) (List.Lex.nil : List.Lex (· < ·) ([] : List Nat) (n :: tail)) prefix

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFiniteLengthOrder
