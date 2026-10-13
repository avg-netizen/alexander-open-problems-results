import Alexander313.OrdinalPackageFromSmallLabels
import Alexander313.Wilken.PureRelationsCanonicalLabels
import Alexander313.Effective.HereditaryCanonicalEnumerationPrograms

/-!
# The remaining ordinal inputs on the actual canonical enumeration

The natural-number presentation, its order isomorphism to the whole source
finite/omega interval, and its strict-order recognizing Program are constructed
here from the compiled hereditary canonical enumeration. The package constructor
therefore needs only Programs recognizing the actual first and second pure
relations on these same labels, and guards of every finite rank in this same
interval. These remaining inputs are explicit; this file does not assert them.
-/

noncomputable section

namespace Alexander313.CanonicalOrdinalPackage

open HereditaryCanonicalEnumeration
open Wilken.PureRelations
open Wilken.RelativeTerm.Hereditary (finiteBaseLimit)

/-- Every natural number is a label in the genuine executing ordinal order.
The type synonym prevents the numerical order on indices from being used. -/
abbrev Label := CodedLabel publicLinearOrder

def smallOrderIso : Label ≃o SmallLabels.Labels finiteBaseLimit where
  toEquiv := labelEquiv.trans CanonicalLabels.smallOrderEquiv.toEquiv
  map_rel_iff' := by
    intro n m
    change CanonicalLabels.smallOrderEquiv (label n) ≤
      CanonicalLabels.smallOrderEquiv (label m) ↔ ordinalValue n ≤ ordinalValue m
    rw [← SmallLabels.SeparatedCopies.value_le_iff,
      CanonicalLabels.small_value, CanonicalLabels.small_value]
    rfl

theorem small_value (n : Label) :
    SmallLabels.value finiteBaseLimit (smallOrderIso n) = ordinalValue n :=
  CanonicalLabels.small_value (label n)

theorem small_lt_iff (n m : Label) : smallOrderIso n < smallOrderIso m ↔ n < m := by
  calc
    smallOrderIso n < smallOrderIso m ↔
        SmallLabels.value finiteBaseLimit (smallOrderIso n) <
          SmallLabels.value finiteBaseLimit (smallOrderIso m) :=
      (SmallLabels.value_lt_iff finiteBaseLimit _ _).symm
    _ ↔ ordinalValue n < ordinalValue m := by rw [small_value, small_value]
    _ ↔ n < m := (less_exact n m).symm

/-- The full semantic relations, not a chosen subrelation or an oracle. -/
def first (n m : Label) : Prop := R1 (ordinalValue n) (ordinalValue m)

def second (n m : Label) : Prop := R2 (ordinalValue n) (ordinalValue m)

theorem first_small_iff (n m : Label) :
    SmallLabels.first finiteBaseLimit (smallOrderIso n) (smallOrderIso m) ↔ first n m := by
  change R1 (SmallLabels.value finiteBaseLimit (smallOrderIso n))
    (SmallLabels.value finiteBaseLimit (smallOrderIso m)) ↔ R1 (ordinalValue n) (ordinalValue m)
  rw [small_value, small_value]

theorem second_small_iff (n m : Label) :
    SmallLabels.second finiteBaseLimit (smallOrderIso n) (smallOrderIso m) ↔ second n m := by
  change R2 (SmallLabels.value finiteBaseLimit (smallOrderIso n))
    (SmallLabels.value finiteBaseLimit (smallOrderIso m)) ↔ R2 (ordinalValue n) (ordinalValue m)
  rw [small_value, small_value]

/-- A partial recognizer is needed: the existing total comparison Program
halts on false answers too, so its domain alone would not recognize `<`. -/
def ltEvaluation (query : Nat) : Part Nat :=
  cond (less query.unpair.1 query.unpair.2) (Part.some 0) Part.none

theorem ltEvaluation_partrec : Partrec ltEvaluation :=
  Partrec.cond
    (less_computable.comp (Primrec.fst.comp Primrec.unpair).to_comp
      (Primrec.snd.comp Primrec.unpair).to_comp)
    (Computable.const 0).partrec Partrec.none

theorem ltProgram_exists : ∃ p : Program, ∀ query, p.eval query = ltEvaluation query := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp ltEvaluation_partrec)
  exact ⟨p, fun query => congrFun hp query⟩

def ltProgram : Program := Classical.choose ltProgram_exists

theorem ltProgram_domain (n m : Label) : ltProgram.domain (Nat.pair n m) ↔ n < m := by
  rw [Program.domain, ltProgram, Classical.choose_spec ltProgram_exists]
  change (ltEvaluation (Nat.pair n m)).Dom ↔ less n m = true
  simp only [ltEvaluation, Nat.unpair_pair]
  cases h : less n m <;> simp [h]

/-- A precise sufficient input on the already constructed canonical carrier.
All other ordinal-package fields, including full finite reflection and room,
are theorems of the actual pure ordinal relations. -/
def assemble (firstProgram secondProgram : Program)
    (hfirst : ∀ n m : Label, firstProgram.domain (Nat.pair n m) ↔ first n m)
    (hsecond : ∀ n m : Label, secondProgram.domain (Nat.pair n m) ↔ second n m)
    (htall : ∀ k, ∃ top : Label, GuardHead second k top) : OrdinalPackage :=
  OrdinalPackage.ofEffectiveSmallLabels publicLinearOrder finiteBaseLimit smallOrderIso
    ltProgram firstProgram secondProgram
    (fun n m => (ltProgram_domain n m).trans (small_lt_iff n m).symm)
    (fun n m => (hfirst n m).trans (first_small_iff n m).symm)
    (fun n m => (hsecond n m).trans (second_small_iff n m).symm)
    (fun k => by
      obtain ⟨top, ht⟩ := htall k
      exact ⟨smallOrderIso top,
        ht.mapOrderIso smallOrderIso second (SmallLabels.second finiteBaseLimit)
          (fun n m h => (second_small_iff n m).mpr h)⟩)

end Alexander313.CanonicalOrdinalPackage
