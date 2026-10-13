import Alexander313.Carlson.FairSequence

/-!
# Downward copies in fair generating-sequence limits

Carlson, *Patterns of resemblance of order 2*, Lemma 14.8(7), the first
relation and the first clause of the second relation, pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 61--62 of the author's October 16, 2008 manuscript.

A finite part of the union below `b` is captured in one stage together
with the endpoints of an existing relation `a ≤ₖ b`. Downward reflection
copies its part at or above `a` into a new block below `a`. Fairness embeds
this generating extension into the union while fixing the original stage.
The resulting copy preserves both relations; at level two it also carries
first-relation links to `b` into links to `a`.

The final statements use the existing `FirstCondition` and
`LinkedCondition` on the limit subtype itself. Empty copied blocks use
the identity map, so neither nonempty finite sets nor strict endpoints
are additional assumptions. Coveredness is not needed in this direction.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {S : GeneratingSequence ℚ}

/-- Downward saturation on the ambient rational labels. The image of
the finite source remains in the union. At level two, links to the upper
endpoint are carried into links to the lower endpoint. -/
theorem Fair.exists_downward_copy (hS : S.Fair) {k : Lvl} {a b : ℚ}
    (hrel : S.rel k a b) (F : Finset ℚ)
    (hF : ∀ z ∈ F, z ∈ S.carrier) (hbelow : ∀ z ∈ F, z < b) :
    ∃ f : ℚ → ℚ,
      (∀ z ∈ F, f z ∈ S.carrier) ∧
      CoveringCopy (S.rel .one) (S.rel .two) F f a ∧
      (k = .two → ∀ z ∈ F, a ≤ z → S.rel .one z b → S.rel .one (f z) a) := by
  classical
  let Y := F.filter (a ≤ ·)
  by_cases hY : Y.Nonempty
  · obtain ⟨m, ham, hbm, hrelm⟩ := hrel
    obtain ⟨j, hFj⟩ := S.finite_capture F hF
    let n := max m j
    let P := S.stage n
    have hm : m ≤ n := Nat.le_max_left m j
    have hj : j ≤ n := Nat.le_max_right m j
    have ha : a ∈ P.U := S.mem_mono hm ham
    have hb : b ∈ P.U := S.mem_mono hm hbm
    have hFP : F ⊆ P.U := hFj.trans (S.isSub hj).1
    have hrelP : P.rel k a b := ((S.isSub hm).rel_iff ham hbm k).mp hrelm
    have hYP : ∀ z ∈ Y, z ∈ P.U ∧ a ≤ z ∧ z < b := by
      intro z hz
      obtain ⟨hzF, haz⟩ := Finset.mem_filter.mp hz
      exact ⟨hFP hzF, haz, hbelow z hzF⟩
    have hab : a < b := by
      obtain ⟨z, hz⟩ := hY
      exact (hYP z hz).2.1.trans_lt (hYP z hz).2.2
    obtain ⟨N, g, D⟩ := Str.DownData.exists_rat (S.pattern n) ha hb hab hrelP hYP hY
    have preimage (z : ℚ) (hz : z ∈ Y) : ∃ w ∈ N, g w = z := by
      apply Finset.mem_image.mp
      rwa [D.himage]
    let c : ℚ → ℚ := fun z =>
      if hz : z ∈ Y then Classical.choose (preimage z hz) else z
    have hcN (z : ℚ) (hz : z ∈ Y) : c z ∈ N := by
      simp only [c, dif_pos hz]
      exact (Classical.choose_spec (preimage z hz)).1
    have hcg (z : ℚ) (hz : z ∈ Y) : g (c z) = z := by
      simp only [c, dif_pos hz]
      exact (Classical.choose_spec (preimage z hz)).2
    have hcfix (z : ℚ) (hza : z < a) : c z = z := by
      have hzY : z ∉ Y := fun hz =>
        (not_le.mpr hza) (Finset.mem_filter.mp hz).2
      simp only [c, dif_neg hzY]
    have hclow (z : ℚ) (hz : z ∈ F) : Str.InLow N P a (c z) := by
      by_cases hza : z < a
      · rw [hcfix z hza]
        exact Or.inr ⟨hFP hz, hza⟩
      · exact Or.inl (hcN z (Finset.mem_filter.mpr ⟨hz, not_lt.mp hza⟩))
    have hcback (z : ℚ) (hz : z ∈ F) : Str.back N g (c z) = z := by
      by_cases hzY : z ∈ Y
      · rw [Str.back_of_mem (hcN z hzY), hcg z hzY]
      · simp only [c, dif_neg hzY]
        exact D.back_L (hFP hz)
    have hcmem (z : ℚ) (hz : z ∈ F) : c z ∈ (P.downward k a b N g).U := by
      rcases hclow z hz with hc | ⟨hc, _⟩
      · exact Finset.mem_union_right P.U hc
      · exact Finset.mem_union_left N hc
    have hclt (z : ℚ) (hz : z ∈ F) : c z < a := by
      rcases hclow z hz with hc | ⟨_, hc⟩
      · exact D.hNa _ hc
      · exact hc
    have hcmono (z : ℚ) (hz : z ∈ F) (w : ℚ) (hw : w ∈ F)
        (hzw : z < w) : c z < c w := by
      by_contra hnot
      have hback := D.low_back_le (hclow w hw) (hclow z hz) (not_lt.mp hnot)
      rw [hcback w hw, hcback z hz] at hback
      exact (not_le.mpr hzw) hback
    obtain ⟨t, htmem, htfix, htmono, htrel⟩ :=
      hS.realizes n (P.downward k a b N g) (.downward D)
    have haQ : a ∈ (P.downward k a b N g).U := D.isSub.1 ha
    refine ⟨t ∘ c, fun z hz => htmem (c z) (hcmem z hz), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      change t (c z) < a
      simpa only [htfix a ha] using htmono (c z) (hcmem z hz) a haQ (hclt z hz)
    · intro z hz hza
      change t (c z) = z
      rw [hcfix z hza, htfix z (hFP hz)]
    · intro z hz w hw hzw
      exact htmono (c z) (hcmem z hz) (c w) (hcmem w hw) (hcmono z hz w hw hzw)
    · intro z hz w hw hzw
      have hrP := (S.rel_iff n (hFP hz) (hFP hw) .one).mp hzw
      have hrQ := (D.r₁_low (hclow z hz) (hclow w hw)).mpr (by
        rw [hcback z hz, hcback w hw]
        exact hrP)
      exact (htrel (c z) (hcmem z hz) (c w) (hcmem w hw)).1.mp hrQ
    · intro z hz w hw hzw
      have hrP := (S.rel_iff n (hFP hz) (hFP hw) .two).mp hzw
      have hrQ := (D.r₂_low (hclow z hz) (hclow w hw)).mpr (by
        rw [hcback z hz, hcback w hw]
        exact hrP)
      exact (htrel (c z) (hcmem z hz) (c w) (hcmem w hw)).2.mp hrQ
    · intro hk z hz haz hzb
      have hzY : z ∈ Y := Finset.mem_filter.mpr ⟨hz, haz⟩
      have hzbP := (S.rel_iff n (hFP hz) hb .one).mp hzb
      have hlink := (D.r₁_NH (hcN z hzY) ha le_rfl).mpr
        ⟨hk, by rw [hcg z hzY]; exact hzbP, D.pat.refl₁ a ha⟩
      have htlink := (htrel (c z) (hcmem z hz) a haQ).1.mp hlink
      change S.rel .one (t (c z)) a
      simpa only [htfix a ha] using htlink
  · have hlow : ∀ z ∈ F, z < a := by
      intro z hz
      by_contra hnot
      exact hY ⟨z, Finset.mem_filter.mpr ⟨hz, not_lt.mp hnot⟩⟩
    refine ⟨id, hF, identity_copy (S.rel .one) (S.rel .two) a F hlow, ?_⟩
    intro _ z hz haz _
    exact ((not_le.mpr (hlow z hz)) haz).elim

/-- The downward copy, now on the actual limit carrier. Outside the
finite set being copied the map is extended by the identity. -/
theorem Fair.exists_limit_copy (hS : S.Fair) {k : Lvl} {a b : S.Limit}
    (hrel : S.limitRel k a b) (F : Finset S.Limit)
    (hbelow : ∀ z ∈ F, z < b) :
    ∃ f : S.Limit → S.Limit,
      CoveringCopy (S.limitRel .one) (S.limitRel .two) F f a ∧
      (k = .two → ∀ z ∈ F, a ≤ z →
        S.limitRel .one z b → S.limitRel .one (f z) a) := by
  classical
  let G : Finset ℚ := F.image Subtype.val
  have hG : ∀ z ∈ G, z ∈ S.carrier := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact x.property
  have hGb : ∀ z ∈ G, z < b.val := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hbelow x hx
  have hmem (x : S.Limit) (hx : x ∈ F) : x.val ∈ G :=
    Finset.mem_image_of_mem Subtype.val hx
  obtain ⟨g, hgmem, hgcopy, hglink⟩ := hS.exists_downward_copy hrel G hG hGb
  let f : S.Limit → S.Limit := fun x =>
    if hx : x ∈ F then ⟨g x.val, hgmem x.val (hmem x hx)⟩ else x
  have hfval (x : S.Limit) (hx : x ∈ F) : (f x).val = g x.val := by
    simp only [f, dif_pos hx]
  refine ⟨f, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    change (f z).val < a.val
    rw [hfval z hz]
    exact hgcopy.1 z.val (hmem z hz)
  · intro z hz hza
    apply Subtype.ext
    rw [hfval z hz]
    exact hgcopy.2.1 z.val (hmem z hz) hza
  · intro z hz w hw hzw
    change (f z).val < (f w).val
    rw [hfval z hz, hfval w hw]
    exact hgcopy.2.2.1 z.val (hmem z hz) w.val (hmem w hw) hzw
  · intro z hz w hw hzw
    change S.rel .one (f z).val (f w).val
    rw [hfval z hz, hfval w hw]
    exact hgcopy.2.2.2.1 z.val (hmem z hz) w.val (hmem w hw) hzw
  · intro z hz w hw hzw
    change S.rel .two (f z).val (f w).val
    rw [hfval z hz, hfval w hw]
    exact hgcopy.2.2.2.2 z.val (hmem z hz) w.val (hmem w hw) hzw
  · intro hk z hz haz hzb
    change S.rel .one (f z).val a.val
    rw [hfval z hz]
    exact hglink hk z.val (hmem z hz) haz hzb

/-- Lemma 14.8(7), first relation: an edge in a fair union satisfies
Carlson's semantic first reflection condition in that union. -/
theorem Fair.firstCondition (hS : S.Fair) {a b : S.Limit}
    (hrel : S.limitRel .one a b) :
    FirstCondition (S.limitRel .one) (S.limitRel .two) a b := by
  intro F hF
  obtain ⟨f, hcopy, _⟩ := hS.exists_limit_copy hrel F hF
  exact ⟨f, hcopy⟩

/-- Lemma 14.8(7), first clause of the second relation: the downward
copy also preserves first-relation links to the endpoints. -/
theorem Fair.linkedCondition (hS : S.Fair) {a b : S.Limit}
    (hrel : S.limitRel .two a b) :
    LinkedCondition (S.limitRel .one) (S.limitRel .two)
      (fun z => S.limitRel .one z b) (fun z => S.limitRel .one z a) a b := by
  intro F hF
  obtain ⟨f, hcopy, hlink⟩ := hS.exists_limit_copy hrel F hF
  exact ⟨f, hcopy, hlink rfl⟩

end GeneratingSequence
end Alexander313.Carlson
