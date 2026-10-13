import Alexander313.CanonicalOrdinalPackage
import Alexander313.Thesis313FromPackage

/-!
# The remaining ordinal inputs as plain semantic and effective statements

`CanonicalOrdinalPackage.assemble` needs two recognizing Programs and guards
of every finite rank on the canonical labels. This file restates both inputs
without labels or guards:

* tallness follows from the finite part of Wilken's maximal second chain,
  `υ₂ <₂ υ₃ <₂ ⋯` (Theorem 1.8(1) of *Pure Σ₂-elementarity beyond the core*),
  stated here as `UpsilonSecondChain` on the source sequence
  `sourceUpsilonFinite`;
* a recognizing Program exists as soon as the relation is decided by a
  computable Boolean function on the canonical codes.

`challenge313_of_inputs` then gives 3-1-3 from two such decisions and the
chain. Nothing here proves those inputs. Whether `sourceUpsilonFinite r` is
Wilken's `υ_r` is the source-alignment question recorded in
`Wilken/FiniteUpsilonDomain.lean`; `UpsilonSecondChain` is about the Lean
sequence, whatever that alignment turns out to be.
-/

noncomputable section

namespace Alexander313.CanonicalOrdinalPackage

open HereditaryCanonicalEnumeration
open Wilken.PureRelations
open Wilken (sourceUpsilonFinite sourceUpsilonOmega sourceUpsilonFinite_strictMono
  sourceUpsilonFinite_lt_omega)

theorem lt_iff_value (n m : Label) : n < m ↔ ordinalValue n < ordinalValue m :=
  less_exact n m

/-- Every ordinal of the source interval is the value of a canonical label. -/
theorem exists_label (ξ : Ordinal.{0}) (hξ : ξ < sourceUpsilonOmega) :
    ∃ n : Label, ordinalValue n = ξ := by
  have h : ξ ∈ Set.range ordinalValue := by
    rw [ordinalValue_range_sourceUpsilonOmega]
    exact hξ
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩

/-- A label with a prescribed value inside the interval; arbitrary outside. -/
def labelOf (ξ : Ordinal.{0}) : Label :=
  if h : ξ < sourceUpsilonOmega then Classical.choose (exists_label ξ h) else (0 : Nat)

theorem value_labelOf {ξ : Ordinal.{0}} (hξ : ξ < sourceUpsilonOmega) :
    ordinalValue (labelOf ξ) = ξ := by
  unfold labelOf
  rw [dif_pos hξ]
  exact Classical.choose_spec (exists_label ξ hξ)

/-- Finite tallness from increasing, pairwise second-related ordinal lists of
every length inside the interval. -/
theorem tall_of_ordinal_guards
    (h : ∀ k, ∃ ν : Ordinal.{0}, ∃ tail : List Ordinal.{0}, tail.length = k ∧
      (ν :: tail).Pairwise (· < ·) ∧ (ν :: tail).Pairwise R2 ∧
      ∀ x ∈ ν :: tail, x < sourceUpsilonOmega) :
    ∀ k, ∃ top : Label, GuardHead second k top := by
  intro k
  obtain ⟨ν, tail, hlen, hlt, hR, hbelow⟩ := h k
  refine ⟨labelOf ν, tail.map labelOf, by rw [List.length_map, hlen], ?_, ?_⟩
  · have hmap : ((ν :: tail).map labelOf).Pairwise (· < ·) := by
      rw [List.pairwise_map]
      exact hlt.imp_of_mem fun hx hy hxy => by
        rw [lt_iff_value, value_labelOf (hbelow _ hx), value_labelOf (hbelow _ hy)]
        exact hxy
    simpa only [List.map_cons] using hmap
  · have hmap : ((ν :: tail).map labelOf).Pairwise second := by
      rw [List.pairwise_map]
      exact hR.imp_of_mem fun hx hy hxy => by
        change R2 (ordinalValue (labelOf _)) (ordinalValue (labelOf _))
        rw [value_labelOf (hbelow _ hx), value_labelOf (hbelow _ hy)]
        exact hxy
    simpa only [List.map_cons] using hmap

/-- The finite part of the maximal second chain of Wilken's Theorem 1.8(1):
`υᵢ <₂ υⱼ` whenever `2 ≤ i < j < ω`, on the source sequence. -/
def UpsilonSecondChain : Prop :=
  ∀ i j : Nat, 2 ≤ i → i < j → R2 (sourceUpsilonFinite i) (sourceUpsilonFinite j)

theorem upsilon_tail_pairwise (k : Nat) (S : Ordinal.{0} → Ordinal.{0} → Prop)
    (hS : ∀ i j : Nat, i < j → S (sourceUpsilonFinite (i + 3)) (sourceUpsilonFinite (j + 3))) :
    ((List.range k).map fun i => sourceUpsilonFinite (i + 3)).Pairwise S := by
  rw [List.pairwise_map]
  exact (List.pairwise_lt_range (n := k)).imp fun hij => hS _ _ hij

theorem mem_upsilon_tail {k : Nat} {x : Ordinal.{0}}
    (hx : x ∈ (List.range k).map fun i => sourceUpsilonFinite (i + 3)) :
    ∃ i, x = sourceUpsilonFinite (i + 3) := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact ⟨i, rfl⟩

/-- The guard of rank `k` is `υ₂, υ₃, …, υ_{k+2}`. -/
theorem tall_of_upsilonSecondChain (h : UpsilonSecondChain) :
    ∀ k, ∃ top : Label, GuardHead second k top := by
  apply tall_of_ordinal_guards
  intro k
  refine ⟨sourceUpsilonFinite 2, (List.range k).map fun i => sourceUpsilonFinite (i + 3),
    by simp, ?_, ?_, ?_⟩
  · refine List.pairwise_cons.mpr ⟨fun x hx => ?_, upsilon_tail_pairwise k _ fun i j hij =>
      sourceUpsilonFinite_strictMono (by omega)⟩
    obtain ⟨i, rfl⟩ := mem_upsilon_tail hx
    exact sourceUpsilonFinite_strictMono (by omega)
  · refine List.pairwise_cons.mpr ⟨fun x hx => ?_, upsilon_tail_pairwise k _ fun i j hij =>
      h (i + 3) (j + 3) (by omega) (by omega)⟩
    obtain ⟨i, rfl⟩ := mem_upsilon_tail hx
    exact h 2 (i + 3) le_rfl (by omega)
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sourceUpsilonFinite_lt_omega 2
    · obtain ⟨i, rfl⟩ := mem_upsilon_tail hx
      exact sourceUpsilonFinite_lt_omega (i + 3)

/-- A computable Boolean decision of a binary relation on codes yields a
Program whose domain on paired codes is exactly that relation. -/
theorem program_of_decision (d : Nat → Nat → Bool) (hd : Computable₂ d)
    (R : Nat → Nat → Prop) (hR : ∀ n m, d n m = true ↔ R n m) :
    ∃ p : Program, ∀ n m, p.domain (Nat.pair n m) ↔ R n m := by
  let evaluation : Nat → Part Nat := fun query =>
    cond (d query.unpair.1 query.unpair.2) (Part.some 0) Part.none
  have hpart : Partrec evaluation :=
    Partrec.cond
      (hd.comp (Primrec.fst.comp Primrec.unpair).to_comp
        (Primrec.snd.comp Primrec.unpair).to_comp)
      (Computable.const 0).partrec Partrec.none
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpart)
  refine ⟨p, fun n m => ?_⟩
  rw [Program.domain, hp]
  change (evaluation (Nat.pair n m)).Dom ↔ R n m
  simp only [evaluation, Nat.unpair_pair]
  rw [← hR n m]
  cases h : d n m <;> simp

/-- 3-1-3 from computable decisions of the actual first and second relations
on the canonical codes and the finite maximal second chain. -/
theorem challenge313_of_inputs (decideFirst decideSecond : Nat → Nat → Bool)
    (hfirst : Computable₂ decideFirst) (hsecond : Computable₂ decideSecond)
    (first_exact : ∀ n m, decideFirst n m = true ↔ R1 (ordinalValue n) (ordinalValue m))
    (second_exact : ∀ n m, decideSecond n m = true ↔ R2 (ordinalValue n) (ordinalValue m))
    (chain : UpsilonSecondChain) : Comparator.challenge313 := by
  obtain ⟨p₁, hp₁⟩ := program_of_decision decideFirst hfirst _ first_exact
  obtain ⟨p₂, hp₂⟩ := program_of_decision decideSecond hsecond _ second_exact
  exact challenge313_of_package (assemble p₁ p₂ (fun n m => hp₁ n m) (fun n m => hp₂ n m)
    (tall_of_upsilonSecondChain chain))

theorem challenge312_of_inputs (decideFirst decideSecond : Nat → Nat → Bool)
    (hfirst : Computable₂ decideFirst) (hsecond : Computable₂ decideSecond)
    (first_exact : ∀ n m, decideFirst n m = true ↔ R1 (ordinalValue n) (ordinalValue m))
    (second_exact : ∀ n m, decideSecond n m = true ↔ R2 (ordinalValue n) (ordinalValue m))
    (chain : UpsilonSecondChain) : Comparator.challenge312 := by
  intro R hR wf
  obtain ⟨S⟩ := challenge313_of_inputs decideFirst decideSecond hfirst hsecond
    first_exact second_exact chain R hR wf
  exact ⟨S.toSolution312⟩

end Alexander313.CanonicalOrdinalPackage
