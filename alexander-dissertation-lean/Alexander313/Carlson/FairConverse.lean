import Alexander313.Carlson.GeneratingSequenceCovering

/-!
# The first semantic converse for generating-sequence limits

Carlson, *Patterns of resemblance of order 2*, Lemma 14.8(8),
level-one converse, pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 63--64 of the author's October 16, 2008 manuscript.

The first finite-copy condition cannot add any new first-relation edges
to a generating-sequence limit with a covered initial stage. A hypothetical
new edge gives a covering of a finite stage which moves an old point
downward, contradicting generating-sequence rigidity. Well-founded
induction on the upper endpoint provides the minimal-counterexample
argument. Fairness is unnecessary for this converse direction.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {α : Type*} [LinearOrder α] (S : GeneratingSequence α)

/-- The limit-subtype form of finite-stage covering rigidity. The map
need only preserve strict order and the two relations on this stage. -/
theorem le_of_stage_limitCovering {n : ℕ} (hP : Str.Covered (S.stage n))
    {f : S.Limit → S.Limit}
    (hmono : ∀ x : S.Limit, x.val ∈ (S.stage n).U →
      ∀ y : S.Limit, y.val ∈ (S.stage n).U → x < y → f x < f y)
    (hrel : ∀ k, ∀ x : S.Limit, x.val ∈ (S.stage n).U →
      ∀ y : S.Limit, y.val ∈ (S.stage n).U →
        S.limitRel k x y → S.limitRel k (f x) (f y))
    {x : S.Limit} (hx : x.val ∈ (S.stage n).U) : x ≤ f x := by
  classical
  let g : α → α := fun z => if hz : z ∈ S.carrier then (f ⟨z, hz⟩).val else z
  have hg (z : S.Limit) : g z.val = (f z).val := by simp only [g, dif_pos z.property]
  have hcover : S.CoversIntoLimit (S.stage n) g := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [hg ⟨z, S.mem_carrier n hz⟩]
      exact (f ⟨z, S.mem_carrier n hz⟩).property
    · intro z hz w hw hzw
      rw [hg ⟨z, S.mem_carrier n hz⟩, hg ⟨w, S.mem_carrier n hw⟩]
      exact hmono ⟨z, S.mem_carrier n hz⟩ hz ⟨w, S.mem_carrier n hw⟩ hw hzw
    · intro z hz w hw hzw
      rw [hg ⟨z, S.mem_carrier n hz⟩, hg ⟨w, S.mem_carrier n hw⟩]
      exact hrel .one ⟨z, S.mem_carrier n hz⟩ hz ⟨w, S.mem_carrier n hw⟩ hw
        ((S.rel_iff n hz hw .one).mpr hzw)
    · intro z hz w hw hzw
      rw [hg ⟨z, S.mem_carrier n hz⟩, hg ⟨w, S.mem_carrier n hw⟩]
      exact hrel .two ⟨z, S.mem_carrier n hz⟩ hz ⟨w, S.mem_carrier n hw⟩ hw
        ((S.rel_iff n hz hw .two).mpr hzw)
  have h := S.le_of_coversIntoLimit hP hcover hx
  rw [hg x] at h
  exact h

/-- The level-one converse in Lemma 14.8(8). A covered starting stage
suffices; fairness is needed for the forward implication, not here. -/
theorem firstCondition_rel_one (hP : Str.Covered (S.stage 0))
    {a b : S.Limit} (hab : a ≤ b)
    (hcopy : FirstCondition (S.limitRel .one) (S.limitRel .two) a b) :
    S.limitRel .one a b := by
  classical
  suffices h : ∀ b a : S.Limit, a ≤ b →
      FirstCondition (S.limitRel .one) (S.limitRel .two) a b → S.limitRel .one a b
    from h b a hab hcopy
  clear a b hab hcopy
  intro b
  refine (S.wellFounded hP).induction b
    (C := fun b => ∀ a : S.Limit, a ≤ b →
      FirstCondition (S.limitRel .one) (S.limitRel .two) a b → S.limitRel .one a b) ?_
  intro b ih a hab hcopy
  by_contra hnot
  have hab' : a < b := lt_of_le_of_ne hab (by
    intro heq
    subst b
    exact hnot (S.rel_refl .one a.property))
  have hbetween : ∀ x : S.Limit, a ≤ x → x < b → S.limitRel .one a x := by
    intro x hax hxb
    exact ih x hxb a hax (fun F hF => hcopy F (fun z hz => (hF z hz).trans hxb))
  have hcross : ∀ k, ∀ x y : S.Limit, a ≤ x → x < b → b ≤ y →
      ¬ S.limitRel k x y := by
    intro k x y hax hxb hby hxy
    have hxy₁ : S.rel .one x.val y.val := by
      cases k with
      | one => exact hxy
      | two => exact S.rel_two_one hxy
    exact hnot (S.rel_trans (hbetween x hax hxb)
      (S.rel_convex_one b.property hxb.le hby hxy₁))
  obtain ⟨na, ha⟩ := a.property
  obtain ⟨nb, hb⟩ := b.property
  let n := max na nb
  have ha' : a.val ∈ (S.stage n).U := S.mem_mono (Nat.le_max_left na nb) ha
  have hPn : Str.Covered (S.stage n) :=
    (S.exactlyGenerates (Nat.zero_le n)).valid.covered hP
  let E : Finset S.Limit := (S.stage n).U.subtype (fun z => z ∈ S.carrier)
  let F := E.filter (· < b)
  have hmem (z : S.Limit) : z ∈ F ↔ z.val ∈ (S.stage n).U ∧ z < b := by
    simp only [F, E, Finset.mem_filter, Finset.mem_subtype]
  obtain ⟨c, hc⟩ := hcopy F (fun z hz => ((hmem z).mp hz).2)
  let f : S.Limit → S.Limit := fun z => if z < b then c z else z
  have hf_low {z : S.Limit} (hz : z < b) : f z = c z := if_pos hz
  have hf_high {z : S.Limit} (hz : ¬ z < b) : f z = z := if_neg hz
  have hmono : ∀ x : S.Limit, x.val ∈ (S.stage n).U →
      ∀ y : S.Limit, y.val ∈ (S.stage n).U → x < y → f x < f y := by
    intro x hx y hy hxy
    by_cases hyb : y < b
    · have hxb := hxy.trans hyb
      rw [hf_low hxb, hf_low hyb]
      exact hc.2.2.1 x ((hmem x).mpr ⟨hx, hxb⟩) y ((hmem y).mpr ⟨hy, hyb⟩) hxy
    · rw [hf_high hyb]
      by_cases hxb : x < b
      · rw [hf_low hxb]
        exact (hc.1 x ((hmem x).mpr ⟨hx, hxb⟩)).trans_le
          (hab.trans (le_of_not_gt hyb))
      · rw [hf_high hxb]
        exact hxy
  have hrel : ∀ k, ∀ x : S.Limit, x.val ∈ (S.stage n).U →
      ∀ y : S.Limit, y.val ∈ (S.stage n).U →
        S.limitRel k x y → S.limitRel k (f x) (f y) := by
    intro k x hx y hy hxy
    by_cases hyb : y < b
    · have hxb : x < b := (S.rel_le hxy).trans_lt hyb
      rw [hf_low hxb, hf_low hyb]
      have hxF := (hmem x).mpr ⟨hx, hxb⟩
      have hyF := (hmem y).mpr ⟨hy, hyb⟩
      cases k with
      | one => exact hc.2.2.2.1 x hxF y hyF hxy
      | two => exact hc.2.2.2.2 x hxF y hyF hxy
    · rw [hf_high hyb]
      by_cases hxb : x < b
      · by_cases hxa : x < a
        · rw [hf_low hxb, hc.2.1 x ((hmem x).mpr ⟨hx, hxb⟩) hxa]
          exact hxy
        · exact (hcross k x y (le_of_not_gt hxa) hxb (le_of_not_gt hyb) hxy).elim
      · rw [hf_high hxb]
        exact hxy
  have hrigid := S.le_of_stage_limitCovering hPn hmono hrel ha'
  have hfa : f a < a := by
    rw [hf_low hab']
    exact hc.1 a ((hmem a).mpr ⟨ha', hab'⟩)
  exact (not_le_of_gt hfa) hrigid

end GeneratingSequence
end Alexander313.Carlson
