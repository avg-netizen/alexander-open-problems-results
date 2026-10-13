import Alexander313.Wilken.FiniteCollapse
import Alexander313.Wilken.HullCardinality

/-!
# Proper collapse on the source-admissible domain

Wilken Lemma 2.7 is proved from the constructed tower and hull cardinality.
First extract a parameter bound from the source domain Cⁿₘ(0,Ωₘ₊₁).
Iterate a bound on all small elements of Cⁿₘ(α,β), and take the countable
supremum. Regularity keeps that supremum below Ωₘ₊₁; finite hull witnesses
show it is closed. It is therefore a genuine candidate for the already
constructed minimum. No proper-collapse bound is assumed as an input.
-/

namespace Alexander313.Wilken

universe u

def smallHull (τ : Ordinal.{u}) (theta : Nat → Ordinal.{u} → Ordinal.{u})
    (n m : Nat) (α β : Ordinal.{u}) : Set Ordinal.{u} :=
  {ξ | Hull (omegaSequence τ) theta n m α β ξ ∧ ξ < omegaSequence τ (m + 1)}

noncomputable def hullClosureBound (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat)
    (α β : Ordinal.{u}) : Ordinal.{u} :=
  sSup ((fun ξ => ξ + 1) '' smallHull τ theta n m α β)

theorem hullClosureBound_lt (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α β : Ordinal.{u})
    (hβ : β < omegaSequence τ (m + 1)) :
    hullClosureBound τ theta n m α β < omegaSequence τ (m + 1) := by
  have hcard : Cardinal.mk (smallHull τ theta n m α β) <
      Cardinal.lift.{u + 1} (levelCardinal τ (m + 1)) :=
    (Cardinal.mk_le_mk_of_subset (fun _ h => h.1)).trans_lt
      (source_hull_cardinality_lt τ theta n m α β hβ)
  have hcof : (Ordinal.lift.{u + 1} (omegaSequence τ (m + 1))).cof =
      Cardinal.lift.{u + 1} (levelCardinal τ (m + 1)) := by
    rw [← Ordinal.lift_cof, omegaSequence, (omegaSequence_regular τ m).cof_ord]
  apply Ordinal.sSup_add_one_lt_of_lt_cof
  · simpa only [hcof] using hcard
  · intro ξ hξ
    exact hξ.2

theorem hullClosureBound_contains (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α β ξ : Ordinal.{u})
    (hξ : Hull (omegaSequence τ) theta n m α β ξ)
    (hsort : ξ < omegaSequence τ (m + 1)) :
    ξ + 1 ≤ hullClosureBound τ theta n m α β := by
  have hlimit : Order.IsSuccLimit (omegaSequence τ (m + 1)) :=
    Cardinal.isSuccLimit_ord (levelCardinal_infinite τ (m + 1))
  have bdd : BddAbove ((fun ξ : Ordinal.{u} => ξ + 1) '' smallHull τ theta n m α β) := by
    refine ⟨omegaSequence τ (m + 1), ?_⟩
    rintro _ ⟨η, hη, rfl⟩
    exact (hlimit.add_one_lt hη.2).le
  exact le_csSup bdd ⟨ξ, ⟨hξ, hsort⟩, rfl⟩

noncomputable def hullClosureSequence (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat)
    (α seed : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => seed
  | k + 1 => max (hullClosureSequence τ theta n m α seed k)
      (hullClosureBound τ theta n m α (hullClosureSequence τ theta n m α seed k))

theorem hullClosureSequence_mono (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α seed : Ordinal.{u}) :
    Monotone (hullClosureSequence τ theta n m α seed) := by
  apply monotone_nat_of_le_succ
  intro k
  exact le_max_left _ _

theorem hullClosureSequence_lt (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α seed : Ordinal.{u})
    (hseed : seed < omegaSequence τ (m + 1)) (k : Nat) :
    hullClosureSequence τ theta n m α seed k < omegaSequence τ (m + 1) := by
  induction k with
  | zero => exact hseed
  | succ k ih =>
    exact max_lt ih (hullClosureBound_lt τ theta n m α _ ih)

noncomputable def hullClosureLimit (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat)
    (α seed : Ordinal.{u}) : Ordinal.{u} :=
  ⨆ k, hullClosureSequence τ theta n m α seed k

theorem hullClosureLimit_lt (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α seed : Ordinal.{u})
    (hseed : seed < omegaSequence τ (m + 1)) :
    hullClosureLimit τ theta n m α seed < omegaSequence τ (m + 1) := by
  apply Ordinal.lift_iSup_lt_of_lt_cof
  · simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0, Ordinal.lift_id', omegaSequence,
      (omegaSequence_regular τ m).cof_ord] using
        (levelCardinal_infinite τ m).trans_lt (levelCardinal_step τ m)
  · exact hullClosureSequence_lt τ theta n m α seed hseed

theorem hullClosureLimit_closed (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α seed ξ : Ordinal.{u})
    (hξ : Hull (omegaSequence τ) theta n m α (hullClosureLimit τ theta n m α seed) ξ)
    (hsort : ξ < omegaSequence τ (m + 1)) :
    ξ < hullClosureLimit τ theta n m α seed := by
  obtain ⟨k, hk⟩ := (hull_nat_sup_parameter
    (hullClosureSequence τ theta n m α seed)
    (hullClosureSequence_mono τ theta n m α seed)).mp hξ
  have hbound := hullClosureBound_contains τ theta n m α _ ξ hk hsort
  have hstep : hullClosureBound τ theta n m α
      (hullClosureSequence τ theta n m α seed k) ≤
      hullClosureSequence τ theta n m α seed (k + 1) := le_max_right _ _
  exact (lt_add_one ξ).trans_le
    (hbound.trans (hstep.trans (Ordinal.le_iSup
      (hullClosureSequence τ theta n m α seed) (k + 1))))

/-- A genuine source candidate is constructed from source hull membership. -/
theorem source_collapse_candidate_exists (τ : Ordinal.{u})
    (theta : Nat → Ordinal.{u} → Ordinal.{u}) (n m : Nat) (α : Ordinal.{u})
    (hα : Hull (omegaSequence τ) theta n m 0 (omegaSequence τ (m + 1)) α) :
    ∃ β, CollapseCandidate (omegaSequence τ) theta n m α β := by
  have hlimit : Order.IsSuccLimit (omegaSequence τ (m + 1)) :=
    Cardinal.isSuccLimit_ord (levelCardinal_infinite τ (m + 1))
  obtain ⟨seed, hseed, hαseed⟩ := (hull_limit_parameter hlimit).mp hα
  refine ⟨hullClosureLimit τ theta n m α seed,
    hullClosureLimit_lt τ theta n m α seed hseed,
    fun ξ hξ hsort => hullClosureLimit_closed τ theta n m α seed ξ hξ hsort, ?_⟩
  apply hull_mono ((zero_le : 0 ≤ α)) _ hαseed
  exact Ordinal.le_iSup (hullClosureSequence τ theta n m α seed) 0

/-- Wilken Lemma 2.7: no fallback on Cⁿₘ(0,Ωₘ₊₁)∩Ωₘ₊₂. -/
theorem sourceFiniteCollapse_proper (τ : Ordinal.{u}) (n m : Nat)
    (hm : m < n) (α : Ordinal.{u}) (_hsort : α < omegaSequence τ (m + 2))
    (hα : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m 0
      (omegaSequence τ (m + 1)) α) :
    sourceFiniteCollapse τ n m α < omegaSequence τ (m + 1) := by
  obtain ⟨β, hβ⟩ := source_collapse_candidate_exists τ (sourceFiniteCollapse τ n) n m α hα
  exact (finiteCollapse_minimal hm hβ).trans_lt hβ.1

theorem sourceFiniteCollapse_nonmembership (τ : Ordinal.{u}) (n m : Nat)
    (hm : m < n) (α : Ordinal.{u}) (hsort : α < omegaSequence τ (m + 2))
    (hα : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m 0
      (omegaSequence τ (m + 1)) α) :
    ¬ Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α
      (sourceFiniteCollapse τ n m α) (sourceFiniteCollapse τ n m α) :=
  finiteCollapse_not_mem_of_lt hm α (sourceFiniteCollapse_proper τ n m hm α hsort hα)

end Alexander313.Wilken
