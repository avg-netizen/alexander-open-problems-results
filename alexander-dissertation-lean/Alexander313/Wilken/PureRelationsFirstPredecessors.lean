import Alexander313.Wilken.PureRelationsSeparatedCopies

/-!
# Actual strict first-predecessor chains below a strict second endpoint

The genuine separated-copy theorem is applied to the singleton upper point
alpha. Its actual R1 connection to beta supplies, above EVERY lower cutoff,
a strict first predecessor of alpha. The full predecessor set is an infinite
R1 chain with least upper bound alpha, as in source Lemma3.1. A countable
increasing subchain is also constructed, without asserting it is cofinal in
an arbitrary uncountable alpha. No predecessor, room or chain oracle is used.
These proof candidates remain uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

def FirstPredecessors (α : Ordinal.{0}) : Set Ordinal.{0} :=
  {δ | δ < α ∧ R1 δ α}

/-- Every strict actual R2 pair supplies genuine R1 predecessors cofinally
below its lower endpoint, including above any displayed ordinal cutoff. -/
theorem firstPredecessors_cofinal (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β)
    (c : Ordinal.{0}) (hc : c < α) :
    ∃ δ : Ordinal.{0}, c < δ ∧ δ ∈ FirstPredecessors α := by
  obtain ⟨f, _, _, range, _, links⟩ :=
    SeparatedCopies.finite_separated_copy α β hR hαβ ∅ {α}
      (fun _ h => by simp at h)
      (fun y hy => by
        have he : y = α := Finset.mem_singleton.mp hy
        simpa only [he] using And.intro le_rfl hαβ) c hc
  have hm : α ∈ ({α} : Finset Ordinal.{0}) := Finset.mem_singleton_self _
  exact ⟨f α, (range α hm).1, (range α hm).2, links α hm (R2_R1 hR)⟩

/-- The actual full first-predecessor set is an R1 chain in the ordinary
ordinal order: interval connectedness supplies each forward relation. -/
theorem firstPredecessors_chain (α : Ordinal.{0}) {δ ε : Ordinal.{0}}
    (hδ : δ ∈ FirstPredecessors α) (hε : ε ∈ FirstPredecessors α) (hδε : δ < ε) :
    R1 δ ε :=
  R1_between hδ.2 hδε.le hε.1.le

/-- The strict actual R2 lower endpoint is the least upper bound of its
ENTIRE actual first-predecessor chain, without a countable-cofinality premise. -/
theorem firstPredecessors_isLUB (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β) :
    IsLUB (FirstPredecessors α) α := by
  refine ⟨fun δ hδ => hδ.1.le, ?_⟩
  intro γ hγ
  by_contra hbad
  obtain ⟨δ, hγδ, hδ⟩ := firstPredecessors_cofinal α β hR hαβ γ (lt_of_not_ge hbad)
  exact (not_le_of_gt hγδ) (hγ hδ)

/-- The actual predecessor order has no largest point, by genuine
cofinal separated copies. This is a derived instance, not input data. -/
theorem firstPredecessors_noMaxOrder (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β) :
    NoMaxOrder (FirstPredecessors α) := by
  refine ⟨?_⟩
  intro δ
  obtain ⟨ε, hδε, hε⟩ := firstPredecessors_cofinal α β hR hαβ δ.val δ.property.1
  exact ⟨⟨ε, hε⟩, hδε⟩

/-- A genuine infinite increasing R1 chain is constructed below alpha.
Its members all have an actual R1 link to alpha; no claim of countable
cofinality of the entire arbitrary ordinal alpha is made. -/
theorem firstPredecessors_increasing_sequence (α β : Ordinal.{0})
    (hR : R2 α β) (hαβ : α < β) :
    ∃ f : Nat → Ordinal.{0}, StrictMono f ∧ (∀ n, f n ∈ FirstPredecessors α) ∧
      ∀ m n : Nat, m < n → R1 (f m) (f n) := by
  letI : NoMaxOrder (FirstPredecessors α) := firstPredecessors_noMaxOrder α β hR hαβ
  have hp := (SeparatedCopies.lower_isSuccLimit α β (R2_R1 hR) hαβ).pos
  obtain ⟨δ, _, hδ⟩ := firstPredecessors_cofinal α β hR hαβ 0 hp
  obtain ⟨g, hg, _⟩ := Nat.exists_strictMono' (⟨δ, hδ⟩ : FirstPredecessors α)
  let f : Nat → Ordinal.{0} := fun n => (g n).val
  have hf : StrictMono f := fun _ _ hmn => hg hmn
  have hm : ∀ n, f n ∈ FirstPredecessors α := fun n => (g n).property
  exact ⟨f, hf, hm, fun m n hmn => firstPredecessors_chain α (hm m) (hm n) (hf hmn)⟩

/-- Source Lemma3.1: the full genuine strict R1 predecessor chain whose
supremum is alpha is infinite. Both properties are derived from actual R2. -/
theorem firstPredecessors_infinite (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β) :
    (FirstPredecessors α).Infinite := by
  obtain ⟨f, hf, hm, _⟩ := firstPredecessors_increasing_sequence α β hR hαβ
  exact Set.infinite_of_injective_forall_mem hf.injective hm

end Alexander313.Wilken.PureRelations
