import Alexander313.Carlson.Exactness
import Alexander313.Carlson.CoreIsominimal

/-!
# Isominimality survives 1-correct initial cuts

Carlson's Lemma 15.7, pure case. First, the existing least-copy theorem
shows that every isominimal induced ordinal pattern is pointwise least
among all ordinal coverings. For a downward closed 1-correct cut, splice
any downward-moving isomorphism of the cut with the identity on its tail.
Correctness excludes first-relation edges across the cut, and hence
second-relation edges too. The splice is a covering of the whole pattern.
Its pointwise least property forces the cut map to be the identity.

The arguments include empty carriers and cutoffs outside the carrier.
-/

noncomputable section

namespace Alexander313.Carlson

/-- An induced finite ordinal structure has an exact pointwise least
copy, and that copy lies in the common core. -/
theorem exists_least_ordinal_copy (U : Finset Ordinal.{0}) :
    ∃ f : Ordinal.{0} → Ordinal.{0},
      Str.IsIso (Str.ofOrdinals U) (Str.ofOrdinals (U.image f)) f ∧
      (∀ z ∈ U, f z < coreBound) ∧
      ∀ g : Ordinal.{0} → Ordinal.{0}, (Str.ofOrdinals U).CoveringR g →
        ∀ z ∈ U, f z ≤ g z := by
  let F := ordinalRationalRelabeling U
  let P := Str.ofOrdinals U
  let Q := P.map F.toFun
  have e : Str.IsIso P Q F.toFun := F.isIso (Finset.Subset.refl U)
  have eb : Str.IsIso Q P F.invFun := F.inverse_isIso (Finset.Subset.refl U)
  obtain ⟨h, eh, hcore, hleast⟩ := exists_minimal_copy_in_core Q
    (e.isPattern (Str.ofOrdinals_isPattern U))
  let f := h ∘ F.toFun
  have ef : Str.IsIso P (Str.ofOrdinals (U.image f)) f := by
    refine ⟨rfl, ?_, ?_⟩
    · intro x hx y hy hxy
      exact eh.2.1 _ (e.mem hx) _ (e.mem hy) (e.2.1 x hx y hy hxy)
    · intro x hx y hy
      have e₁ := e.2.2 x hx y hy
      have e₂ := eh.2.2 _ (e.mem hx) _ (e.mem hy)
      exact ⟨e₁.1.trans e₂.1, e₁.2.trans e₂.2⟩
  refine ⟨f, ef, fun z hz => hcore _ (e.mem hz), ?_⟩
  intro g hg z hz
  have hb : Q.CoveringR (g ∘ F.invFun) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hg.1 _ (eb.mem hx) _ (eb.mem hy) (eb.2.1 x hx y hy hxy)
    · intro x hx y hy hxy
      exact hg.2.1 _ (eb.mem hx) _ (eb.mem hy) ((eb.2.2 x hx y hy).1.mp hxy)
    · intro x hx y hy hxy
      exact hg.2.2 _ (eb.mem hx) _ (eb.mem hy) ((eb.2.2 x hx y hy).2.mp hxy)
  have hm := hleast (g ∘ F.invFun) hb (F.toFun z) (e.mem hz)
  simpa only [f, Function.comp_apply, F.left_inv z hz] using hm

namespace IsominimalOrdinalSet

variable {U V : Finset Ordinal.{0}}

/-- An isominimal ordinal pattern is pointwise least even among
coverings which need not reflect relations. -/
theorem le_covering (hU : IsominimalOrdinalSet U)
    {g : Ordinal.{0} → Ordinal.{0}} (hg : (Str.ofOrdinals U).CoveringR g)
    {z : Ordinal.{0}} (hz : z ∈ U) : z ≤ g z := by
  obtain ⟨f, ef, _, hleast⟩ := exists_least_ordinal_copy U
  have hid : (Str.ofOrdinals U).CoveringR id :=
    ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩
  have hle : ∀ x ∈ U, f x ≤ x := hleast id hid
  have himage : U.image f = U := hU _ f ef hle
  have hfix := eqOn_of_strictMonoOn_image_eq ef.2.1
    (fun _ _ _ _ h => h) (himage.trans (Finset.image_id.symm))
  simpa only [hfix z hz] using hleast g hg z hz

/-- Pointwise leastness of coverings is equivalent to isominimality. -/
theorem iff_le_covering : IsominimalOrdinalSet U ↔
    ∀ g : Ordinal.{0} → Ordinal.{0}, (Str.ofOrdinals U).CoveringR g →
      ∀ z ∈ U, z ≤ g z := by
  constructor
  · intro hU g hg z hz
    exact hU.le_covering hg hz
  · intro h T f ef hle
    have hc : (Str.ofOrdinals U).CoveringR f :=
      ⟨ef.2.1, fun x hx y hy => (ef.2.2 x hx y hy).1.mp,
        fun x hx y hy => (ef.2.2 x hx y hy).2.mp⟩
    have hfix : ∀ z ∈ U, f z = z := fun z hz => (hle z hz).antisymm (h f hc z hz)
    calc
      T = U.image f := ef.1.symm
      _ = U.image id := Finset.image_congr hfix
      _ = U := Finset.image_id

/-- Finite unions of isominimal induced ordinal patterns are isominimal. -/
theorem union (hU : IsominimalOrdinalSet U) (hV : IsominimalOrdinalSet V) :
    IsominimalOrdinalSet (U ∪ V) := by
  apply iff_le_covering.mpr
  intro g hg z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact hU.le_covering (hg.mono (Str.restrict_isSub (Str.ofOrdinals (U ∪ V))
      Finset.subset_union_left)) hz
  · exact hV.le_covering (hg.mono (Str.restrict_isSub (Str.ofOrdinals (U ∪ V))
      Finset.subset_union_right)) hz

/-- Lemma 15.7 in its carrier form: every downward closed, 1-correct
induced subpattern of an isominimal ordinal pattern is isominimal. -/
theorem of_initial_correct (hU : IsominimalOrdinalSet U) (hVU : V ⊆ U)
    (hlower : ∀ x ∈ U, ∀ y ∈ V, x ≤ y → x ∈ V)
    (hc : Str.KCorrect (Str.ofOrdinals V) (Str.ofOrdinals U) .one) :
    IsominimalOrdinalSet V := by
  have hclosed : ∀ x ∈ V, ∀ y ∈ U, R1 x y → y ∈ V :=
    (Str.kCorrect_one_iff_no_crossing hVU hlower).mp hc
  intro T f ef hle
  let g : Ordinal.{0} → Ordinal.{0} := fun x => if x ∈ V then f x else x
  have hg : (Str.ofOrdinals U).CoveringR g := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      by_cases hxV : x ∈ V <;> by_cases hyV : y ∈ V
      · simpa only [g, if_pos hxV, if_pos hyV] using ef.2.1 x hxV y hyV hxy
      · simpa only [g, if_pos hxV, if_neg hyV] using (hle x hxV).trans_lt hxy
      · exact (hxV (hlower x hx y hyV hxy.le)).elim
      · simpa only [g, if_neg hxV, if_neg hyV] using hxy
    · intro x hx y hy hxy
      by_cases hxV : x ∈ V <;> by_cases hyV : y ∈ V
      · simpa only [g, if_pos hxV, if_pos hyV, Str.ofOrdinals] using
          (ef.2.2 x hxV y hyV).1.mp hxy
      · exact (hyV (hclosed x hxV y hy hxy)).elim
      · exact (hxV (hlower x hx y hyV (R1_le hxy))).elim
      · simpa only [g, if_neg hxV, if_neg hyV, Str.ofOrdinals] using hxy
    · intro x hx y hy hxy
      by_cases hxV : x ∈ V <;> by_cases hyV : y ∈ V
      · simpa only [g, if_pos hxV, if_pos hyV, Str.ofOrdinals] using
          (ef.2.2 x hxV y hyV).2.mp hxy
      · exact (hyV (hclosed x hxV y hy (R2_R1 hxy))).elim
      · exact (hxV (hlower x hx y hyV (R1_le (R2_R1 hxy)))).elim
      · simpa only [g, if_neg hxV, if_neg hyV, Str.ofOrdinals] using hxy
  have hfix : ∀ z ∈ V, f z = z := by
    intro z hz
    have hzle : z ≤ f z := by
      simpa only [g, if_pos hz] using hU.le_covering hg (hVU hz)
    exact (hle z hz).antisymm hzle
  calc
    T = V.image f := ef.1.symm
    _ = V.image id := Finset.image_congr hfix
    _ = V := Finset.image_id

/-- Carlson's Lemma 15.7, including cutoffs outside the carrier. -/
theorem initialCut (hU : IsominimalOrdinalSet U) (a : Ordinal.{0})
    (hc : Str.KCorrect ((Str.ofOrdinals U).initialCut a) (Str.ofOrdinals U) .one) :
    IsominimalOrdinalSet (U.filter (fun x => x ≤ a)) :=
  hU.of_initial_correct (Finset.filter_subset _ _)
    (fun _x hx _y hy hxy => Finset.mem_filter.mpr
      ⟨hx, hxy.trans (Finset.mem_filter.mp hy).2⟩) hc

end IsominimalOrdinalSet

end Alexander313.Carlson
