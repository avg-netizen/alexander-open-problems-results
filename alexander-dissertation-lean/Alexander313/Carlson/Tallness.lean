import Alexander313.Carlson.ClosureSemantics
import Alexander313.Carlson.Patterns
import Mathlib.Data.List.OfFn

/-!
# Unconditional chains and coveredness for pure Carlson patterns

The countable closure construction supplies an increasing sequence of actual
ordinals below `ω₁` with all forward `R2` links. Every finite pure pattern
embeds into a finite part of this sequence, giving Carlson's Lemma 15.11 in
the pure language without a set-theoretic reflection principle.

This is classical existence. It does not give a program presenting the core,
or show tallness inside the realization of any one fixed finite seed.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal

def nextReflectionPoint (a : Ordinal.{0}) (ha : a < ω₁) : Ordinal.{0} :=
  Classical.choose (exists_reflectionPoint_above ha)

theorem nextReflectionPoint_spec (a : Ordinal.{0}) (ha : a < ω₁) :
    a < nextReflectionPoint a ha ∧ ReflectionPoint (nextReflectionPoint a ha) :=
  Classical.choose_spec (exists_reflectionPoint_above ha)

abbrev ReflectionOrdinal := {a : Ordinal.{0} // ReflectionPoint a}

def firstReflectionOrdinal : ReflectionOrdinal :=
  ⟨nextReflectionPoint 0 (Cardinal.isSuccLimit_omega 1).pos,
    (nextReflectionPoint_spec 0 (Cardinal.isSuccLimit_omega 1).pos).2⟩

def advanceReflectionOrdinal (a : ReflectionOrdinal) : ReflectionOrdinal :=
  ⟨nextReflectionPoint a a.2.below, (nextReflectionPoint_spec a a.2.below).2⟩

theorem lt_advanceReflectionOrdinal (a : ReflectionOrdinal) :
    a.1 < (advanceReflectionOrdinal a).1 :=
  (nextReflectionPoint_spec a a.2.below).1

/-- A classical sequence of genuinely second-related countable ordinals. -/
def reflectionSequence (n : ℕ) : Ordinal.{0} :=
  (advanceReflectionOrdinal^[n] firstReflectionOrdinal).1

theorem reflectionSequence_point (n : ℕ) : ReflectionPoint (reflectionSequence n) :=
  (advanceReflectionOrdinal^[n] firstReflectionOrdinal).2

theorem reflectionSequence_strictMono : StrictMono reflectionSequence := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (advanceReflectionOrdinal^[n] firstReflectionOrdinal).1 <
    (advanceReflectionOrdinal^[n + 1] firstReflectionOrdinal).1
  rw [Function.iterate_succ_apply']
  exact lt_advanceReflectionOrdinal (advanceReflectionOrdinal^[n] firstReflectionOrdinal)

theorem reflectionSequence_second {i j : ℕ} (hij : i ≤ j) :
    R2 (reflectionSequence i) (reflectionSequence j) :=
  (reflectionSequence_point i).second (reflectionSequence_point j)
    (reflectionSequence_strictMono.monotone hij)

/-- Arbitrarily long finite strict `R2` chains, with no ordinal-package input. -/
theorem exists_finite_second_chain (n : ℕ) :
    ∃ xs : List Ordinal.{0}, xs.length = n ∧ xs.Pairwise (· < ·) ∧ xs.Pairwise R2 := by
  refine ⟨List.ofFn (fun i : Fin n => reflectionSequence i), List.length_ofFn, ?_, ?_⟩
  · exact List.pairwise_ofFn.mpr fun _ _ h => reflectionSequence_strictMono h
  · exact List.pairwise_ofFn.mpr fun _ _ h => reflectionSequence_second h.le

/-- The exact list shape used by ordinal-package finite guards. -/
theorem exists_ordinal_guard (k : ℕ) :
    ∃ top : Ordinal.{0}, ∃ tail : List Ordinal.{0}, tail.length = k ∧
      (top :: tail).Pairwise (· < ·) ∧ (top :: tail).Pairwise R2 := by
  let tail := List.ofFn (fun i : Fin k => reflectionSequence (i.val + 1))
  have hlist : reflectionSequence 0 :: tail =
      List.ofFn (fun i : Fin (k + 1) => reflectionSequence i.val) := by
    rw [List.ofFn_succ]
    rfl
  refine ⟨reflectionSequence 0, tail, List.length_ofFn, ?_, ?_⟩
  · rw [hlist]
    exact List.pairwise_ofFn.mpr fun _ _ h => reflectionSequence_strictMono h
  · rw [hlist]
    exact List.pairwise_ofFn.mpr fun _ _ h => reflectionSequence_second h.le

/-- Every finite pure pattern has a covering whose labels are countable
ordinals. The map need only carry relations forward, as Carlson requires. -/
theorem exists_covering_below_omega_one {α : Type*} [LinearOrder α]
    (P : Str α) (hP : P.IsPattern) :
    ∃ h : α → Ordinal.{0}, P.CoveringR h ∧ ∀ x ∈ P.U, h x < ω₁ := by
  classical
  let index (x : α) (hx : x ∈ P.U) := (P.U.orderIsoOfFin rfl).symm ⟨x, hx⟩
  let h (x : α) := if hx : x ∈ P.U then reflectionSequence (index x hx).val
    else reflectionSequence 0
  have hh (x : α) (hx : x ∈ P.U) : h x = reflectionSequence (index x hx).val := by
    simp only [h, hx, ↓reduceDIte]
  have hindex {x y : α} (hx : x ∈ P.U) (hy : y ∈ P.U) (hxy : x ≤ y) :
      index x hx ≤ index y hy := (P.U.orderIsoOfFin rfl).symm.monotone hxy
  refine ⟨h, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    rw [hh x hx, hh y hy]
    exact reflectionSequence_strictMono ((P.U.orderIsoOfFin rfl).symm.strictMono hxy)
  · intro x hx y hy hxy
    rw [hh x hx, hh y hy]
    exact R2_R1 (reflectionSequence_second (hindex hx hy (hP.le₁ x hx y hy hxy)))
  · intro x hx y hy hxy
    rw [hh x hx, hh y hy]
    exact reflectionSequence_second
      (hindex hx hy (hP.le₁ x hx y hy (hP.sub₂ x hx y hy hxy)))
  · intro x hx
    rw [hh x hx]
    exact (reflectionSequence_point _).below

/-- Carlson Lemma 15.11, for the pure language `{≤, ≤₁, ≤₂}`. -/
theorem every_pattern_covered {α : Type*} [LinearOrder α] (P : Str α)
    (hP : P.IsPattern) : P.Covered := by
  obtain ⟨h, hh, _⟩ := exists_covering_below_omega_one P hP
  exact ⟨h, hh⟩

end Alexander313.Carlson
