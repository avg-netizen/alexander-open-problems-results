import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Data.Finset.Max

/-!
# Semantic finite frontiers for arbitrary well-founded R

The ranks and maximal-frontier selection in this file are deliberately
noncomputable metatheoretic objects. No enumerator tests negative
reachability, and no computable rank is an input to a thesis statement.
-/

namespace Alexander313

inductive StrictBelow (R : Nat → Nat → Prop) : Nat → Nat → Prop where
  | edge {j i} : R j i → StrictBelow R j i
  | trans {j k i} : StrictBelow R j k → StrictBelow R k i → StrictBelow R j i

noncomputable def nodeRank {R : Nat → Nat → Prop} (wf : WellFounded R) (i : Nat) :
    Ordinal := (wf.apply i).rank

theorem nodeRank_edge {R : Nat → Nat → Prop} (wf : WellFounded R)
    {j i : Nat} (h : R j i) : nodeRank wf j < nodeRank wf i :=
  Acc.rank_lt_of_rel (wf.apply i) h

theorem nodeRank_below {R : Nat → Nat → Prop} (wf : WellFounded R)
    {j i : Nat} (h : StrictBelow R j i) : nodeRank wf j < nodeRank wf i := by
  induction h with
  | edge h => exact nodeRank_edge wf h
  | trans _ _ ih₁ ih₂ => exact lt_trans ih₁ ih₂

noncomputable def frontierRank {R : Nat → Nat → Prop} (wf : WellFounded R)
    (J : Finset Nat) : Ordinal := J.sup (nodeRank wf)

def DownIdeal (R : Nat → Nat → Prop) (J : Finset Nat) (i : Nat) : Prop :=
  ∃ j ∈ J, i = j ∨ StrictBelow R i j

def FrontierAntichain (R : Nat → Nat → Prop) (J : Finset Nat) : Prop :=
  ∀ i ∈ J, ∀ j ∈ J, ¬ StrictBelow R i j

/-- The strict outer decrease of note 26 equation (6). Nonemptiness of A
    is essential and the empty case is delegated to core genericity. -/
theorem frontierRank_strict {R : Nat → Nat → Prop} (wf : WellFounded R)
    (A J : Finset Nat) (hA : A.Nonempty)
    (below : ∀ a ∈ A, ∃ j ∈ J, StrictBelow R a j) :
    frontierRank wf A < frontierRank wf J := by
  classical
  have each : ∀ a ∈ A, nodeRank wf a < frontierRank wf J := by
    intro a ha
    obtain ⟨j, hj, hbelow⟩ := below a ha
    exact lt_of_lt_of_le (nodeRank_below wf hbelow)
      (Finset.le_sup (f := nodeRank wf) hj)
  have positive : (⊥ : Ordinal) < frontierRank wf J := by
    obtain ⟨a, ha⟩ := hA
    exact lt_of_le_of_lt bot_le (each a ha)
  exact (Finset.sup_lt_iff positive).mpr each

noncomputable def maximalFrontier (R : Nat → Nat → Prop) (F : Finset Nat) : Finset Nat := by
  classical
  exact F.filter (fun i => ∀ j ∈ F, ¬ StrictBelow R i j)

theorem maximalFrontier_antichain (R : Nat → Nat → Prop) (F : Finset Nat) :
    FrontierAntichain R (maximalFrontier R F) := by
  classical
  intro i hi j hj
  exact (Finset.mem_filter.mp hi).2 j (Finset.mem_filter.mp hj).1

theorem finite_frontier_covers {R : Nat → Nat → Prop} (wf : WellFounded R)
    (F : Finset Nat) (i : Nat) (hi : i ∈ F) : DownIdeal R (maximalFrontier R F) i := by
  classical
  let reachable := F.filter (fun j => i = j ∨ StrictBelow R i j)
  have hiReach : i ∈ reachable := by simp [reachable, hi]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image reachable (nodeRank wf) ⟨i, hiReach⟩
  have hjF : j ∈ F := (Finset.mem_filter.mp hj).1
  have hij : i = j ∨ StrictBelow R i j := (Finset.mem_filter.mp hj).2
  refine ⟨j, Finset.mem_filter.mpr ⟨hjF, ?_⟩, hij⟩
  intro k hk hjk
  have hik : i = k ∨ StrictBelow R i k := by
    rcases hij with rfl | hij
    · exact Or.inr hjk
    · exact Or.inr (.trans hij hjk)
  have hkReach : k ∈ reachable := Finset.mem_filter.mpr ⟨hk, hik⟩
  exact (not_lt_of_ge (hmax k hkReach)) (nodeRank_below wf hjk)

theorem maximalFrontier_nonempty {R : Nat → Nat → Prop} (wf : WellFounded R)
    (F : Finset Nat) (hF : F.Nonempty) : (maximalFrontier R F).Nonempty := by
  obtain ⟨i, hi⟩ := hF
  obtain ⟨j, hj, _⟩ := finite_frontier_covers wf F i hi
  exact ⟨j, hj⟩

end Alexander313
