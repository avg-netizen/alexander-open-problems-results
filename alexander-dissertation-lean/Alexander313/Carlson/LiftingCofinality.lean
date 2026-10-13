import Alexander313.Carlson.PatternLifting
import Alexander313.Carlson.PatternOperations

/-!
# Cofinal validity of minimal pattern liftings

Carlson, *Patterns of resemblance of order 2*, the cofinal-validity argument
of Lemma 13.8, in the pure case.
Source: https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
§13 of the author's October 16, 2008 manuscript.

Once a minimal pattern lifting is given, cofinal validity of the source
rule implies cofinal validity of the lifted rule. The bounded arithmetic
lifting hypotheses place every new target point in the image of a source
block. We first enlarge each cutoff to dominate the images of all old
target points below its anchor, then combine a covering of the old target
with a suitable covering of the extended source. Minimality makes this
increasing combined map preserve both relations: intersect the lifted
pattern with the pullback of the ordinal relations under the combined map.

Continuity is not assumed in this implication. In Lemma 13.8 it supplies
the existence and continuity of a minimal lifting through Lemma 12.6;
those are separate assertions from the cofinal conclusion proved here.
-/

noncomputable section

namespace Alexander313.Carlson

namespace PatternLifting

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
variable {P Pplus : Str α} {Q Qplus : Str β} {h f : α → β}

/-- The cofinal-validity part of Lemma 13.8. A given minimal pattern lifting
transfers cofinal validity from the source rule to the target rule. -/
theorem cofinallyValid (D : PatternLifting P Pplus Q Qplus h f)
    (hmin : IsMinimal P Pplus Q Qplus h) (hcv : Str.CofinallyValid P Pplus) :
    Str.CofinallyValid Q Qplus := by
  classical
  refine ⟨D.target_sub, fun t tcov cut hcut => ?_⟩
  let F : β → Finset Ordinal.{0} := fun b =>
    insert (cut b) ((Q.U.filter (· < b)).image t)
  have Fne : ∀ b, (F b).Nonempty := fun b => ⟨cut b, Finset.mem_insert_self _ _⟩
  let boost : β → Ordinal.{0} := fun b => (F b).max' (Fne b)
  have cut_bound (b : β) : cut b ≤ boost b :=
    (F b).le_max' (cut b) (Finset.mem_insert_self _ _)
  have old_bound {y b : β} (hy : y ∈ Q.U) (hyb : y < b) : t y ≤ boost b :=
    (F b).le_max' (t y) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem t (Finset.mem_filter.mpr ⟨hy, hyb⟩)))
  have boost_lt {b : β} (hb : b ∈ Q.U) (hpos : 0 < t b) : boost b < t b := by
    have hF : ∀ z ∈ F b, z < t b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hcut b hb hpos
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hyQ, hyb⟩ := Finset.mem_filter.mp hy
        exact tcov.1 y hyQ b hb hyb
    exact hF _ ((F b).max'_mem (Fne b))
  have source_cov : Str.CoveringR P (t ∘ h) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact tcov.1 (h x) (D.arithmetic.base_mem x hx)
        (h y) (D.arithmetic.base_mem y hy) (D.arithmetic.base_mono x hx y hy hxy)
    · intro x hx y hy hxy
      exact tcov.2.1 (h x) (D.arithmetic.base_mem x hx)
        (h y) (D.arithmetic.base_mem y hy) ((D.base_relations hx hy).1.mp hxy)
    · intro x hx y hy hxy
      exact tcov.2.2 (h x) (D.arithmetic.base_mem x hx)
        (h y) (D.arithmetic.base_mem y hy) ((D.base_relations hx hy).2.mp hxy)
  have source_cut : ∀ a ∈ P.U, 0 < (t ∘ h) a → (boost ∘ h) a < (t ∘ h) a := by
    intro a ha hpos
    exact boost_lt (D.arithmetic.base_mem a ha) hpos
  obtain ⟨g, gcov, gfix, gcut⟩ := hcv.2 (t ∘ h) source_cov (boost ∘ h) source_cut
  have new_bounds {x : α} (hx : x ∈ Pplus.U) (hxP : x ∉ P.U) :
      boost (h (Str.up P.U x)) < g x ∧ g x < t (h (Str.up P.U x)) := by
    have hj := D.arithmetic.source_justBelow hx hxP
    refine ⟨gcut _ x hx hj, ?_⟩
    have hlt := gcov.1 x hx (Str.up P.U x) (D.source_sub.1 hj.1) hj.2.1
    rw [gfix _ hj.1] at hlt
    exact hlt
  have pre : ∀ y, y ∈ Qplus.U \ Q.U → ∃ x ∈ Pplus.U, x ∉ P.U ∧ f x = y := by
    intro y hy
    exact D.arithmetic.exists_new_preimage
      (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  let t' : β → Ordinal.{0} := fun y =>
    if hy : y ∈ Qplus.U \ Q.U then g (Classical.choose (pre y hy)) else t y
  have t'_old {y : β} (hy : y ∈ Q.U) : t' y = t y := by
    simp only [t', dif_neg (fun hy' => (Finset.mem_sdiff.mp hy').2 hy)]
  have t'_image {x : α} (hx : x ∈ Pplus.U) : t' (f x) = g x := by
    by_cases hxP : x ∈ P.U
    · rw [D.arithmetic.agrees x hxP, t'_old (D.arithmetic.base_mem x hxP)]
      exact (gfix x hxP).symm
    · have hfx : f x ∈ Qplus.U \ Q.U :=
        Finset.mem_sdiff.mpr ⟨D.arithmetic.mem x hx, D.arithmetic.new_not_mem hx hxP⟩
      have hs := Classical.choose_spec (pre (f x) hfx)
      have heq : Classical.choose (pre (f x) hfx) = x :=
        D.arithmetic.injective hs.1 hx hs.2.2
      simp only [t', dif_pos hfx, heq]
  have t'_mono : ∀ u ∈ Qplus.U, ∀ v ∈ Qplus.U, u < v → t' u < t' v := by
    intro u hu v hv huv
    by_cases huQ : u ∈ Q.U
    · by_cases hvQ : v ∈ Q.U
      · rw [t'_old huQ, t'_old hvQ]
        exact tcov.1 u huQ v hvQ huv
      · obtain ⟨y, hy, hyP, rfl⟩ := D.arithmetic.exists_new_preimage hv hvQ
        rw [t'_old huQ, t'_image hy]
        have hua : u < h (Str.up P.U y) :=
          (D.arithmetic.old_lt_image_iff hy hyP huQ).mp huv
        exact (old_bound huQ hua).trans_lt (new_bounds hy hyP).1
    · obtain ⟨x, hx, hxP, rfl⟩ := D.arithmetic.exists_new_preimage hu huQ
      by_cases hvQ : v ∈ Q.U
      · rw [t'_image hx, t'_old hvQ]
        have hav : h (Str.up P.U x) ≤ v :=
          (D.arithmetic.image_lt_old_iff hx hxP hvQ).mp huv
        have ha : Str.up P.U x ∈ P.U := (D.arithmetic.source_justBelow hx hxP).1
        exact (new_bounds hx hxP).2.trans_le
          (Str.IsCovering.le_of_le tcov (D.arithmetic.base_mem _ ha) hvQ hav)
      · obtain ⟨y, hy, hyP, rfl⟩ := D.arithmetic.exists_new_preimage hv hvQ
        rw [t'_image hx, t'_image hy]
        have hxy : x < y := by
          by_contra hnot
          exact absurd huv (not_lt.mpr (D.arithmetic.le_of_le hy hx (not_lt.mp hnot)))
        exact gcov.1 x hx y hy hxy
  let S : Str β := Str.interPullback Qplus t'
  have DS : PatternLifting P Pplus Q S h f :=
    { source_pattern := D.source_pattern
      target_pattern := Str.interPullback_isPattern D.target_pattern t'_mono
      source_sub := D.source_sub
      target_sub := by
        refine ⟨D.target_sub.1, ?_⟩
        intro x hx y hy
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro hxy
          refine ⟨(D.target_sub.2 x hx y hy).1.mp hxy, ?_⟩
          rw [t'_old hx, t'_old hy]
          exact tcov.2.1 x hx y hy hxy
        · intro hxy
          exact (D.target_sub.2 x hx y hy).1.mpr hxy.1
        · intro hxy
          refine ⟨(D.target_sub.2 x hx y hy).2.mp hxy, ?_⟩
          rw [t'_old hx, t'_old hy]
          exact tcov.2.2 x hx y hy hxy
        · intro hxy
          exact (D.target_sub.2 x hx y hy).2.mpr hxy.1
      arithmetic := D.arithmetic
      relations := by
        intro x hx y hy
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro hxy
          refine ⟨(D.relations x hx y hy).1.mp hxy, ?_⟩
          rw [t'_image hx, t'_image hy]
          exact gcov.2.1 x hx y hy hxy
        · intro hxy
          exact (D.relations x hx y hy).1.mpr hxy.1
        · intro hxy
          refine ⟨(D.relations x hx y hy).2.mp hxy, ?_⟩
          rw [t'_image hx, t'_image hy]
          exact gcov.2.2 x hx y hy hxy
        · intro hxy
          exact (D.relations x hx y hy).2.mpr hxy.1 }
  have hcover := hmin S f rfl DS
  have t'_cov : Str.CoveringR Qplus t' :=
    ⟨t'_mono, fun x hx y hy hxy => (hcover.2.2.1 x hx y hy hxy).2,
      fun x hx y hy hxy => (hcover.2.2.2 x hx y hy hxy).2⟩
  refine ⟨t', t'_cov, fun x hx => t'_old hx, ?_⟩
  intro b y hy hj
  obtain ⟨x, hx, hxP, rfl⟩ := D.arithmetic.exists_new_preimage hy hj.not_mem
  have hanchor : b = h (Str.up P.U x) :=
    hj.unique (D.arithmetic.mapped_justBelow hx hxP)
  rw [hanchor, t'_image hx]
  exact (cut_bound _).trans_lt (new_bounds hx hxP).1

/-- A given pattern lifting has a minimal choice of relations whose target
rule is cofinally valid whenever the source rule is cofinally valid. -/
theorem exists_minimal_cofinallyValid (D : PatternLifting P Pplus Q Qplus h f)
    (hcv : Str.CofinallyValid P Pplus) :
    ∃ R : Str β, R.U = Qplus.U ∧ PatternLifting P Pplus Q R h f ∧
      IsMinimal P Pplus Q R h ∧ Str.CofinallyValid Q R := by
  obtain ⟨R, hU, DR, hmin⟩ := D.exists_minimal
  exact ⟨R, hU, DR, hmin, DR.cofinallyValid hmin hcv⟩

end PatternLifting

end Alexander313.Carlson
