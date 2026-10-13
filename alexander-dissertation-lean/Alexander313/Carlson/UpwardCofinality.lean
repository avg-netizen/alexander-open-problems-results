import Alexander313.Carlson.Upward
import Alexander313.Carlson.CofinalCopies
import Alexander313.Carlson.CoveringExtension

/-!
# Cofinal validity of upward reflection

Carlson, *Patterns of resemblance of order 2*, Lemma 10.3, pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 43–44 of the author's October 16, 2008 manuscript.

A cofinally valid extension at `a` supplies cofinal copies of its lower
block below the image of `a`. The second resemblance relation transfers
these copies below the image of `b`. Choose a copy above every old point
below `b` and the prescribed cutoff. Its increasing covering fixes the
old lower block, so it extends the original covering after the new points
are matched with their originals. The first relation across the old and
new blocks follows from `R1_between`; the second is copied from the source.
-/

noncomputable section

namespace Alexander313.Carlson

namespace Str

variable {α : Type*} [LinearOrder α]

namespace UpData

variable {P Q : Str α} {a b : α} {N : Finset α} {g : α → α}

/-- Lemma 10.3: upward reflection preserves cofinal validity.
Continuity of the reflected extension is `UpData.continuous`. -/
theorem cofinallyValid (D : UpData P Q a b N g) (hcv : CofinallyValid P Q) :
    CofinallyValid P (P.upward Q a b N g) := by
  classical
  refine ⟨D.isSub, fun h hh cut hcut => ?_⟩
  let L : Finset α := P.U.filter (· < a)
  let A : Str α := Q.restrict (L ∪ (Q.U \ P.U))
  have hR2 : R2 (h a) (h b) := hh.2.2 a D.ha b D.hb D.hrel
  have hab : h a < h b := hh.1 a D.ha b D.hb D.hab
  have hpos : 0 < h b := lt_of_le_of_lt zero_le hab
  have hL : ∀ x ∈ L.image h, x < h a := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hzP, hza⟩ := Finset.mem_filter.mp hz
    exact hh.1 z hzP a D.ha hza
  have sourceCopies : CofinalCopies R1 R2 (L.image h)
      A.indexedFirst A.indexedSecond (h a) := hcv.cofinalCopies_at D.ext hh
  have targetCopies : CofinalCopies R1 R2 (L.image h)
      A.indexedFirst A.indexedSecond (h b) :=
    R2_cofinal hR2 (L.image h) hL A.indexedFirst A.indexedSecond sourceCopies
  let F : Finset Ordinal.{0} := insert (cut b) ((P.U.filter (· < b)).image h)
  have hFne : F.Nonempty := ⟨cut b, Finset.mem_insert_self _ _⟩
  have hF : ∀ x ∈ F, x < h b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hcut b D.hb hpos
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hzP, hzb⟩ := Finset.mem_filter.mp hz
      exact hh.1 z hzP b D.hb hzb
  have old_bound {x : α} (hx : x ∈ P.U) (hxb : x < b) : h x ≤ F.max' hFne :=
    F.le_max' (h x) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem h (Finset.mem_filter.mpr ⟨hx, hxb⟩)))
  have cut_bound : cut b ≤ F.max' hFne :=
    F.le_max' (cut b) (Finset.mem_insert_self _ _)
  obtain ⟨Y, hY, cover⟩ := targetCopies (F.max' hFne) (hF _ (F.max'_mem hFne))
  have hLA : L ⊆ A.U := fun _ hx => Finset.mem_union_left _ hx
  have source_separated : ∀ x ∈ L, ∀ z ∈ A.U, z ∉ L → x < z := by
    intro x hx z hz hzL
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hzL hz).elim
    · obtain ⟨hzQ, hzP⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hxP, hxa⟩ := Finset.mem_filter.mp hx
      exact (D.ext.2.2.2 z hzQ hzP).2.2 x hxP hxa
  have target_separated : ∀ x ∈ L, ∀ y ∈ Y, h x < y := by
    intro x hx y hy
    obtain ⟨hxP, hxa⟩ := Finset.mem_filter.mp hx
    exact (old_bound hxP (hxa.trans D.hab)).trans_lt (hY y hy).1
  obtain ⟨f, fcov, ffix, fnew⟩ :=
    exists_covering_extension_of_coversStructure (A := A) (X := L) (Y := Y) (h := h)
      hLA source_separated
      (fun x hx y hy hxy => hh.1 x (Finset.mem_filter.mp hx).1
        y (Finset.mem_filter.mp hy).1 hxy) target_separated cover
  have g_mem_A {n : α} (hn : n ∈ N) : g n ∈ A.U :=
    Finset.mem_union_right L (Finset.mem_sdiff.mpr (D.g_mem hn))
  have g_mem_Y {n : α} (hn : n ∈ N) : f (g n) ∈ Y :=
    fnew (g n) (g_mem_A hn) (fun hL => (D.g_mem hn).2 (Finset.mem_filter.mp hL).1)
  have new_bounds {n : α} (hn : n ∈ N) : F.max' hFne < f (g n) ∧ f (g n) < h b :=
    hY _ (g_mem_Y hn)
  have old_lt_new {x n : α} (hx : x ∈ P.U) (hxb : x < b) (hn : n ∈ N) :
      h x < f (g n) := (old_bound hx hxb).trans_lt (new_bounds hn).1
  let h' : α → Ordinal.{0} := fun z => if z ∈ N then f (g z) else h z
  have h'_old {z : α} (hz : z ∈ P.U) : h' z = h z := by
    simp only [h', if_neg (fun hN => D.hNP z hN hz)]
  have h'_new {z : α} (hz : z ∈ N) : h' z = f (g z) := by
    simp only [h', if_pos hz]
  refine ⟨h', ⟨?_, ?_, ?_⟩, fun z hz => h'_old hz, ?_⟩
  · -- The chosen copy lies between all old points below `b` and `b`.
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu <;>
      rcases Finset.mem_union.mp hv with hv | hv
    · rw [h'_old hu, h'_old hv]
      exact hh.1 u hu v hv huv
    · rw [h'_old hu, h'_new hv]
      exact old_lt_new hu (huv.trans (D.hNb v hv)) hv
    · rw [h'_new hu, h'_old hv]
      have hbv : b ≤ v := by
        by_contra hnot
        exact absurd huv (not_lt.mpr (D.hNL u hu v hv (not_le.mp hnot)).le)
      exact (new_bounds hu).2.trans_le (IsCovering.le_of_le hh D.hb hv hbv)
    · rw [h'_new hu, h'_new hv]
      exact fcov.1 (g u) (g_mem_A hu) (g v) (g_mem_A hv) (D.hmono u hu v hv huv)
  · -- Every old-to-new first edge is inherited from an old edge to `b`.
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu <;>
      rcases Finset.mem_union.mp hv with hv | hv
    · rw [h'_old hu, h'_old hv]
      exact hh.2.1 u hu v hv ((D.r₁_PP hu hv).mp huv)
    · obtain ⟨hub, hur⟩ := (D.r₁_PN hu hv).mp huv
      rw [h'_old hu, h'_new hv]
      exact R1_between (hh.2.1 u hu b D.hb hur)
        (old_lt_new hu hub hv).le (new_bounds hv).2.le
    · exact absurd huv (D.not_r₁_NP hu hv)
    · rw [h'_new hu, h'_new hv]
      exact fcov.2.1 (g u) (g_mem_A hu) (g v) (g_mem_A hv) ((D.r₁_NN hu hv).mp huv)
  · -- The copied second edges use the covering's agreement on the old prefix.
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu <;>
      rcases Finset.mem_union.mp hv with hv | hv
    · rw [h'_old hu, h'_old hv]
      exact hh.2.2 u hu v hv ((D.r₂_PP hu hv).mp huv)
    · obtain ⟨hua, hur⟩ := (D.r₂_PN hu hv).mp huv
      have huL : u ∈ L := Finset.mem_filter.mpr ⟨hu, hua⟩
      rw [h'_old hu, h'_new hv, ← ffix u huL]
      exact fcov.2.2 u (hLA huL) (g v) (g_mem_A hv) hur
    · exact absurd huv (D.not_r₂_NP hu hv)
    · rw [h'_new hu, h'_new hv]
      exact fcov.2.2 (g u) (g_mem_A hu) (g v) (g_mem_A hv) ((D.r₂_NN hu hv).mp huv)
  · intro b' c hc hjb
    have hcN : c ∈ N := by
      rcases Finset.mem_union.mp hc with hcP | hcN
      · exact (hjb.not_mem hcP).elim
      · exact hcN
    have hb' : b' = b := hjb.unique ⟨D.hb, D.hNb c hcN, D.hNL c hcN⟩
    rw [hb', h'_new hcN]
    exact cut_bound.trans_lt (new_bounds hcN).1

end UpData

end Str

end Alexander313.Carlson
