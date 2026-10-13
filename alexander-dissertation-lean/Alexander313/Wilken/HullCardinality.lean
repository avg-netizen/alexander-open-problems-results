import Alexander313.Wilken.Hulls
import Alexander313.Wilken.OmegaSequence
import Mathlib.Data.W.Cardinal

/-!
# Cardinality of the actual inductive hull

Wilken Lemma 2.2(d) is proved by finite algebraic witnesses. Every hull
derivation is represented by a finite W-tree whose leaves are below the
base or parameter, and whose operations are addition or one of countably
many collapsing symbols. No cardinality bound for the supplied family
itself is assumed.
-/

namespace Alexander313.Wilken

universe u

abbrev HullSeeds (base parameter : Ordinal.{u}) :=
  Set.Iio base ⊕ Set.Iio parameter

abbrev HullAlphabet (base parameter : Ordinal.{u}) := HullSeeds base parameter ⊕ Nat

def HullArity (base parameter : Ordinal.{u}) : HullAlphabet base parameter → Type
  | .inl _ => Empty
  | .inr 0 => Bool
  | .inr (_ + 1) => Unit

instance hullArity_finite (base parameter : Ordinal.{u})
    (a : HullAlphabet base parameter) : Finite (HullArity base parameter a) := by
  rcases a with a | k
  · exact inferInstanceAs (Finite Empty)
  · cases k with
    | zero => exact inferInstanceAs (Finite Bool)
    | succ k => exact inferInstanceAs (Finite Unit)

def hullTreeOperation (theta : Nat → Ordinal.{u} → Ordinal.{u})
    (base parameter : Ordinal.{u}) :
    (Σ a, HullArity base parameter a → Ordinal.{u}) → Ordinal.{u}
  | ⟨.inl (.inl ξ), _⟩ => ξ.val
  | ⟨.inl (.inr ξ), _⟩ => ξ.val
  | ⟨.inr 0, f⟩ => f false + f true
  | ⟨.inr (k + 1), f⟩ => theta k (f ())

def hullTreeEval (theta : Nat → Ordinal.{u} → Ordinal.{u})
    (base parameter : Ordinal.{u}) : WType (HullArity base parameter) → Ordinal.{u} :=
  WType.elim _ (hullTreeOperation theta base parameter)

theorem hull_has_finite_tree {omega : Nat → Ordinal.{u}}
    {theta : Nat → Ordinal.{u} → Ordinal.{u}} {n m : Nat} {α β ξ : Ordinal.{u}}
    (h : Hull omega theta n m α β ξ) :
    ∃ t, hullTreeEval theta (omega m) β t = ξ := by
  induction h with
  | below_base h => exact ⟨WType.mk (.inl (.inl ⟨_, h⟩)) Empty.rec, rfl⟩
  | below_parameter h => exact ⟨WType.mk (.inl (.inr ⟨_, h⟩)) Empty.rec, rfl⟩
  | add _ _ ihξ ihη =>
    obtain ⟨t, ht⟩ := ihξ
    obtain ⟨s, hs⟩ := ihη
    exact ⟨WType.mk (.inr 0) (Bool.rec t s), by
      change hullTreeEval theta (omega m) β t + hullTreeEval theta (omega m) β s = _
      rw [ht, hs]⟩
  | higher hmk hkn hsort _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨WType.mk (.inr (_ + 1)) (fun _ => t), by
      change theta _ (hullTreeEval theta (omega m) β t) = _
      rw [ht]⟩
  | «local» hξ _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨WType.mk (.inr (m + 1)) (fun _ => t), by
      change theta m (hullTreeEval theta (omega m) β t) = _
      rw [ht]⟩

/-- The finite tree witness bound, before instantiating the source cardinal. -/
theorem hull_cardinality_lt {omega : Nat → Ordinal.{u}}
    {theta : Nat → Ordinal.{u} → Ordinal.{u}} (n m : Nat) (α β : Ordinal.{u})
    (c : Cardinal.{u + 1}) (hcount : Cardinal.aleph0 < c)
    (hbase : Cardinal.mk (Set.Iio (omega m)) < c)
    (hparameter : Cardinal.mk (Set.Iio β) < c) :
    Cardinal.mk {ξ | Hull omega theta n m α β ξ} < c := by
  have subset : {ξ | Hull omega theta n m α β ξ} ⊆
      Set.range (hullTreeEval theta (omega m) β) := by
    intro ξ hξ
    exact hull_has_finite_tree hξ
  have halphabet : Cardinal.mk (HullAlphabet (omega m) β) < c := by
    have h := Cardinal.add_lt_of_lt hcount.le
      (Cardinal.add_lt_of_lt hcount.le hbase hparameter) hcount
    simpa only [HullAlphabet, HullSeeds, Cardinal.mk_sum, Cardinal.lift_id,
      Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0] using h
  calc
    Cardinal.mk {ξ | Hull omega theta n m α β ξ} ≤
        Cardinal.mk (Set.range (hullTreeEval theta (omega m) β)) :=
      Cardinal.mk_le_mk_of_subset subset
    _ ≤ Cardinal.mk (WType (HullArity (omega m) β)) := Cardinal.mk_range_le
    _ ≤ max (Cardinal.mk (HullAlphabet (omega m) β)) Cardinal.aleph0 := by
      simpa only [Cardinal.lift_uzero] using
        (WType.cardinalMk_le_max_aleph0_of_finite'
          (β := HullArity (omega m) β))
    _ < c := max_lt halphabet hcount

/-- Wilken Lemma 2.2(d) for the concrete Ω-sequence.
The lift only records that a set of ordinals inhabits one higher universe. -/
theorem source_hull_cardinality_lt (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α β : Ordinal.{u})
    (hβ : β < omegaSequence τ (m + 1)) :
    Cardinal.mk {ξ | Hull (omegaSequence τ) theta n m α β ξ} <
      Cardinal.lift.{u + 1} (levelCardinal τ (m + 1)) := by
  apply hull_cardinality_lt
  · have hcount : (Cardinal.aleph0 : Cardinal.{u}) < levelCardinal τ (m + 1) :=
      (levelCardinal_infinite τ m).trans_lt (Order.lt_succ _)
    simpa only [Cardinal.lift_aleph0] using
      (Cardinal.lift_lt.mpr hcount : Cardinal.lift.{u + 1} Cardinal.aleph0 <
        Cardinal.lift.{u + 1} (levelCardinal τ (m + 1)))
  · rw [Cardinal.mk_Iio_ordinal]
    apply Cardinal.lift_lt.mpr
    cases m with
    | zero => exact (le_max_right _ _).trans_lt (Order.lt_succ _)
    | succ m =>
      simpa only [omegaSequence, Cardinal.card_ord] using levelCardinal_step τ (m + 1)
  · rw [Cardinal.mk_Iio_ordinal]
    apply Cardinal.lift_lt.mpr
    exact Cardinal.lt_ord.mp hβ

end Alexander313.Wilken
