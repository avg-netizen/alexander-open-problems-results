import Alexander313.Wilken.PureRelationsFiniteReflection
import Alexander313.Wilken.PureRelationsSeparatedCopies

/-!
# Genuine second-successor cofinality under a strict first extension

Full actual R1 reflection fixes the lower predecessor and an arbitrary cutoff
while copying the upper point alpha. Its actual R2 predecessor link survives
in the complete finite pattern. Thus every strict R2 predecessor of alpha has
R2 successors cofinally below alpha whenever alpha has a strict R1 extension.
This proves the FORWARD half of source Lemma3.2(2), with an actual supremum
statement. The converse, public decision algorithms and a cofinal strict R2
chain of endpoints are separate constructions. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

def SecondSuccessorsBelow (α δ : Ordinal.{0}) : Set Ordinal.{0} :=
  {γ | γ < α ∧ R2 δ γ}

/-- The actual full finite diagram constructs an R2 successor above EVERY
lower cutoff, preserving its original lower predecessor as a fixed label. -/
theorem secondSuccessorsBelow_cofinal (α β δ : Ordinal.{0})
    (hR : R1 α β) (hαβ : α < β) (hδα : δ < α) (hδR : R2 δ α)
    (c : Ordinal.{0}) (hc : c < α) :
    ∃ γ : Ordinal.{0}, c < γ ∧ δ < γ ∧ γ ∈ SecondSuccessorsBelow α δ := by
  let F : Finset Ordinal.{0} := {δ, c, α}
  have hF : ∀ x ∈ F, x < β := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hδα.trans hαβ
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc.trans hαβ
      · have he : x = α := Finset.mem_singleton.mp hx
        simpa only [he] using hαβ
  obtain ⟨f, below, fixed, pattern⟩ := finiteLabelReflection α β hR F hF
  have hd : δ ∈ F := Finset.mem_insert_self _ _
  have hcm : c ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have ha : α ∈ F := Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hcg := (pattern.2.1 c hcm α ha).mpr hc
  have hdg := (pattern.2.1 δ hd α ha).mpr hδα
  have hgR := (pattern.2.2.2 δ hd α ha).mpr hδR
  rw [fixed c hcm hc] at hcg
  rw [fixed δ hd hδα] at hdg hgR
  exact ⟨f α, hcg, hdg, below α ha, hgR⟩

/-- The full actual R2 successor class of each strict predecessor has
supremum alpha under a genuine strict actual first extension of alpha. -/
theorem secondSuccessorsBelow_isLUB (α β δ : Ordinal.{0})
    (hR : R1 α β) (hαβ : α < β) (hδα : δ < α) (hδR : R2 δ α) :
    IsLUB (SecondSuccessorsBelow α δ) α := by
  refine ⟨fun γ hγ => hγ.1.le, ?_⟩
  intro ξ hξ
  by_contra hbad
  obtain ⟨γ, hξγ, _, hγ⟩ := secondSuccessorsBelow_cofinal α β δ hR hαβ hδα hδR
    ξ (lt_of_not_ge hbad)
  exact (not_le_of_gt hξγ) (hξ hγ)

/-- The FORWARD implication of printed source Lemma3.2(2): actual
alpha R1 alpha+1 forces a proper limit and the displayed supremum property
for EVERY strict second predecessor. No converse is claimed here. -/
theorem source_lemma_3_2_forward (α : Ordinal.{0}) (hR : R1 α (α + 1)) :
    Order.IsSuccLimit α ∧ ∀ δ : Ordinal.{0}, δ < α → R2 δ α →
      IsLUB (SecondSuccessorsBelow α δ) α :=
  ⟨SeparatedCopies.lower_isSuccLimit α (α + 1) hR (lt_add_one α),
    fun δ hδα hδR => secondSuccessorsBelow_isLUB α (α + 1) δ hR
      (lt_add_one α) hδα hδR⟩

end Alexander313.Wilken.PureRelations
