import Alexander313.Carlson.GeneratingRules
import Alexander313.Carlson.ReflectionRelabeling
import Alexander313.Carlson.LiftingRelabeling

/-!
# Finite support of generating derivations

Every rule, exact chain and generation witness admits a single finite ordered
frame on which relabeling transports the whole derivation. The frame includes
recursive witnesses, rather than only the endpoint carriers: an upward rule
uses its earlier lower copy, and a lifting uses its earlier source rule.

The target ambient order is arbitrary. Thus the result applies both to finite
normalization and to interpreting finite certificates in an infinite order.
-/

noncomputable section

universe u v

namespace Alexander313.Carlson.Str

variable {α : Type u} [LinearOrder α]

/-- A generating derivation uses only finitely many ordered labels. -/
theorem GeneratingRule.exists_relabeling_support {P Q : Str α}
    (d : GeneratingRule P Q) :
    ∃ S : Finset α, P.U ⊆ S ∧ Q.U ⊆ S ∧
      ∀ (β : Type v) [LinearOrder β] (F : FiniteRelabeling S β),
        GeneratingRule (P.map F.toFun) (Q.map F.toFun) := by
  induction d using GeneratingRule.rec
    (motive_2 := fun P Q _ => ∃ S : Finset α, P.U ⊆ S ∧ Q.U ⊆ S ∧
      ∀ (β : Type v) [LinearOrder β] (F : FiniteRelabeling S β),
        ExactlyGenerates (P.map F.toFun) (Q.map F.toFun))
  · rename_i P Q hP hsub hU
    refine ⟨Q.U, hsub.1, Finset.Subset.refl _, ?_⟩
    intro β _ F
    exact .arithmetic ((F.isIso hsub.1).isPattern hP)
      (F.isSub hsub.1 (Finset.Subset.refl _) hsub)
      (congrArg (fun U => U.image F.toFun) hU)
  · rename_i P k a b X N g D
    refine ⟨P.U ∪ N, Finset.subset_union_left, Finset.Subset.refl _, ?_⟩
    intro β _ F
    have hP : P.U ⊆ P.U ∪ N := Finset.subset_union_left
    have hN : N ⊆ P.U ∪ N := Finset.subset_union_right
    exact (GeneratingRule.downward (F.downwardData hP hN D)).of_isIso
      (IsIso.refl _) ((F.downward_isIso hP hN D).id_of_same_map
        (F.isIso (Finset.Subset.refl _))) (fun _ _ => rfl)
  · rename_i P Q a b N g d D ih
    obtain ⟨S, hPS, hQS, hS⟩ := ih
    have hP : P.U ⊆ S ∪ N := hPS.trans Finset.subset_union_left
    have hQ : Q.U ⊆ S ∪ N := hQS.trans Finset.subset_union_left
    have hN : N ⊆ S ∪ N := Finset.subset_union_right
    have hU : (P.upward Q a b N g).U ⊆ S ∪ N := Finset.union_subset hP hN
    refine ⟨S ∪ N, hP, hU, ?_⟩
    intro β _ F
    have d' := hS β (F.restrict Finset.subset_union_left)
    exact (GeneratingRule.upward d' (F.upwardData hP hQ hN D)).of_isIso
      (IsIso.refl _) ((F.upward_isIso hP hQ hN D).id_of_same_map
        (F.isIso hU)) (fun _ _ => rfl)
  · rename_i P Q R a c hsub hAt ih
    obtain ⟨S, hP, hR, hS⟩ := ih
    have hQ : Q.U ⊆ S := hsub.1.trans hR
    refine ⟨S, hP, hQ, ?_⟩
    intro β _ F
    exact .finiteRestriction (hS β F) (F.isSub hQ hR hsub) (F.extensionAt hP hQ hAt)
  · rename_i P Pplus Q Qplus h f d he L hM ih
    obtain ⟨S, hPS, hPplusS, hS⟩ := ih
    have hP : P.U ⊆ S ∪ Qplus.U := hPS.trans Finset.subset_union_left
    have hPplus : Pplus.U ⊆ S ∪ Qplus.U := hPplusS.trans Finset.subset_union_left
    have hQplus : Qplus.U ⊆ S ∪ Qplus.U := Finset.subset_union_right
    have hQ : Q.U ⊆ S ∪ Qplus.U := L.target_sub.1.trans hQplus
    refine ⟨S ∪ Qplus.U, hQ, hQplus, ?_⟩
    intro β _ F
    exact .lifting (hS β (F.restrict Finset.subset_union_left))
      (F.continuousEmbedding hP hQ he) (F.patternLifting hPplus hQplus L)
      (F.isMinimal hPplus hQplus L hM)
  · rename_i P hP
    refine ⟨P.U, Finset.Subset.refl _, Finset.Subset.refl _, ?_⟩
    intro β _ F
    exact .refl ((F.isIso (Finset.Subset.refl _)).isPattern hP)
  · rename_i P Q R c d hc hd
    obtain ⟨S, hP, _, hS⟩ := hc
    obtain ⟨T, _, hR, hT⟩ := hd
    refine ⟨S ∪ T, hP.trans Finset.subset_union_left,
      hR.trans Finset.subset_union_right, ?_⟩
    intro β _ F
    exact .tail (hS β (F.restrict Finset.subset_union_left))
      (hT β (F.restrict Finset.subset_union_right))

/-- A single finite frame supports an entire exact chain, including all
recursive rule witnesses appearing in that chain. -/
theorem ExactlyGenerates.exists_relabeling_support {P Q : Str α}
    (d : ExactlyGenerates P Q) :
    ∃ S : Finset α, P.U ⊆ S ∧ Q.U ⊆ S ∧
      ∀ (β : Type v) [LinearOrder β] (F : FiniteRelabeling S β),
        ExactlyGenerates (P.map F.toFun) (Q.map F.toFun) := by
  induction d using ExactlyGenerates.rec (motive_1 := fun _ _ _ => True)
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · rename_i P hP
    refine ⟨P.U, Finset.Subset.refl _, Finset.Subset.refl _, ?_⟩
    intro β _ F
    exact .refl ((F.isIso (Finset.Subset.refl _)).isPattern hP)
  · rename_i P Q R c d hc _
    obtain ⟨S, hP, _, hS⟩ := hc
    obtain ⟨T, _, hR, hT⟩ := d.exists_relabeling_support
    refine ⟨S ∪ T, hP.trans Finset.subset_union_left,
      hR.trans Finset.subset_union_right, ?_⟩
    intro β _ F
    exact .tail (hS β (F.restrict Finset.subset_union_left))
      (hT β (F.restrict Finset.subset_union_right))

/-- The frame for generation also contains its larger exact-chain witness. -/
theorem Generates.exists_relabeling_support {P Q : Str α} (d : Generates P Q) :
    ∃ S : Finset α, P.U ⊆ S ∧ Q.U ⊆ S ∧
      ∀ (β : Type v) [LinearOrder β] (F : FiniteRelabeling S β),
        Generates (P.map F.toFun) (Q.map F.toFun) := by
  obtain ⟨R, c, hQR, hPQ⟩ := d
  obtain ⟨S, hP, hR, hS⟩ := c.exists_relabeling_support
  have hQ := hQR.1.trans hR
  refine ⟨S, hP, hQ, ?_⟩
  intro β _ F
  exact ⟨R.map F.toFun, hS β F, F.isSub hQ hR hQR,
    Finset.image_subset_image hPQ⟩

/-- A globally increasing change of ambient labels transports a rule. -/
theorem GeneratingRule.map_of_strictMono [Nonempty α] {β : Type v} [LinearOrder β]
    {P Q : Str α} (d : GeneratingRule P Q) {f : α → β} (hf : StrictMono f) :
    GeneratingRule (P.map f) (Q.map f) := by
  obtain ⟨S, _, _, hS⟩ := d.exists_relabeling_support
  exact hS β (FiniteRelabeling.ofStrictMono S f hf)

/-- Global increasing relabelings transport exact chains, including their witnesses. -/
theorem ExactlyGenerates.map_of_strictMono [Nonempty α] {β : Type v} [LinearOrder β]
    {P Q : Str α} (d : ExactlyGenerates P Q) {f : α → β} (hf : StrictMono f) :
    ExactlyGenerates (P.map f) (Q.map f) := by
  obtain ⟨S, _, _, hS⟩ := d.exists_relabeling_support
  exact hS β (FiniteRelabeling.ofStrictMono S f hf)

/-- Global increasing relabelings transport generation by restriction. -/
theorem Generates.map_of_strictMono [Nonempty α] {β : Type v} [LinearOrder β]
    {P Q : Str α} (d : Generates P Q) {f : α → β} (hf : StrictMono f) :
    Generates (P.map f) (Q.map f) := by
  obtain ⟨S, _, _, hS⟩ := d.exists_relabeling_support
  exact hS β (FiniteRelabeling.ofStrictMono S f hf)

/-- Changes to relations away from the carrier do not affect exact generation. -/
theorem ExactlyGenerates.of_identity_isos {P Q P' Q' : Str α}
    (d : ExactlyGenerates P Q) (eP : IsIso P P' id) (eQ : IsIso Q Q' id) :
    ExactlyGenerates P' Q' := by
  have first : GeneratingRule P' P := .arithmetic
    (eP.isPattern d.source_pattern) eP.symm_id.isSub_of_id eP.universe_eq_of_id
  have last : GeneratingRule Q Q' := .arithmetic d.target_pattern
    eQ.isSub_of_id eQ.universe_eq_of_id.symm
  exact (first.exactlyGenerates.trans d).tail last

/-- Identity isomorphisms of endpoints preserve generation by restriction. -/
theorem Generates.of_identity_isos {P Q P' Q' : Str α}
    (d : Generates P Q) (eP : IsIso P P' id) (eQ : IsIso Q Q' id) :
    Generates P' Q' := by
  obtain ⟨R, c, hQR, hPQ⟩ := d
  have c' := c.of_identity_isos eP (IsIso.refl R)
  refine ⟨R, c', eQ.symm_id.isSub_of_id.trans hQR, ?_⟩
  rwa [← eP.universe_eq_of_id, ← eQ.universe_eq_of_id]

end Alexander313.Carlson.Str
