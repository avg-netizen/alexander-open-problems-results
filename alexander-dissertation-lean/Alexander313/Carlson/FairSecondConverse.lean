import Alexander313.Carlson.FairConverse
import Alexander313.Carlson.FairDownward
import Alexander313.Carlson.ReflectionConditions
import Alexander313.Carlson.CoveringExtension

/-!
# The second semantic converse for fair generating-sequence limits

Carlson, *Patterns of resemblance of order 2*, Lemma 14.8(8),
level-two converse, pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 64--66 of the author's October 16, 2008 manuscript.

Well-founded induction on the upper endpoint supplies the minimal
counterexample argument. The linked-copy and cofinal-copy clauses then
give, in the two cases of Carlson's proof, a covering of a finite stage
that moves an old point downward. Finite-stage rigidity excludes both
possibilities.

Fairness is used through the already proved first finite-copy property
of each first-relation edge. Coveredness supplies well-foundedness and
the rigidity of finite stages.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {S : GeneratingSequence ℚ}

/-- Lemma 14.8(8), second relation: both intrinsic reflection clauses
produce an actual second-relation edge in a fair covered limit. -/
theorem Fair.secondCondition_rel_two (hS : S.Fair)
    (hP : Str.Covered (S.stage 0)) {a b : S.Limit}
    (hsem : SecondCondition (S.limitRel .one) (S.limitRel .two) a b) :
    S.limitRel .two a b := by
  classical
  suffices h : ∀ b a : S.Limit,
      SecondCondition (S.limitRel .one) (S.limitRel .two) a b →
        S.limitRel .two a b from h b a hsem
  clear a b hsem
  intro b
  refine (S.wellFounded hP).induction b
    (C := fun b => ∀ a : S.Limit,
      SecondCondition (S.limitRel .one) (S.limitRel .two) a b →
        S.limitRel .two a b) ?_
  intro b ih a hsem
  by_contra hnot
  have hab : a < b := lt_of_le_of_ne hsem.1 (by
    intro heq
    subst b
    exact hnot (S.rel_refl .two a.property))
  have hab₁ : S.limitRel .one a b :=
    S.firstCondition_rel_one hP hsem.1 hsem.firstCondition
  have hclaim (x : S.Limit) (hax : a ≤ x) (hxb : x < b)
      (hxb₁ : S.limitRel .one x b) :
      S.limitRel .two a x ∧ ¬ S.limitRel .two x b := by
    have haxsem := hsem.respects_first
      (fun hxy hyz => S.rel_trans hxy hyz) hax hxb.le hxb₁ (hS.firstCondition hxb₁)
    have hax₂ := ih x hxb a haxsem
    exact ⟨hax₂, fun hxb₂ => hnot (S.rel_trans hax₂ hxb₂)⟩
  obtain ⟨na, ha⟩ := a.property
  obtain ⟨nb, hb⟩ := b.property
  let n := max na nb
  have ha' : a.val ∈ (S.stage n).U := S.mem_mono (Nat.le_max_left na nb) ha
  have hb' : b.val ∈ (S.stage n).U := S.mem_mono (Nat.le_max_right na nb) hb
  have hPn : Str.Covered (S.stage n) :=
    (S.exactlyGenerates (Nat.zero_le n)).valid.covered hP
  let E : Finset S.Limit := (S.stage n).U.subtype (fun z => z ∈ S.carrier)
  have hE (z : S.Limit) : z ∈ E ↔ z.val ∈ (S.stage n).U := by
    simp only [E, Finset.mem_subtype]
  by_cases hcase : ∀ d : S.Limit, d ∈ E → b ≤ d →
      S.limitRel .one a d → S.limitRel .one b d
  · -- Case 2.1: the linked downward copy extends by the identity above `b`.
    let F := E.filter (· < b)
    have hF (z : S.Limit) : z ∈ F ↔ z ∈ E ∧ z < b := Finset.mem_filter
    obtain ⟨c, hc, hlinks⟩ := hsem.2.1 F (fun z hz => ((hF z).mp hz).2)
    let f : S.Limit → S.Limit := fun z => if z < b then c z else z
    have hf_low {z : S.Limit} (hz : z < b) : f z = c z := if_pos hz
    have hf_high {z : S.Limit} (hz : ¬ z < b) : f z = z := if_neg hz
    have hmono : ∀ x : S.Limit, x.val ∈ (S.stage n).U →
        ∀ y : S.Limit, y.val ∈ (S.stage n).U → x < y → f x < f y := by
      intro x hx y hy hxy
      by_cases hyb : y < b
      · have hxb := hxy.trans hyb
        rw [hf_low hxb, hf_low hyb]
        exact hc.2.2.1 x ((hF x).mpr ⟨(hE x).mpr hx, hxb⟩)
          y ((hF y).mpr ⟨(hE y).mpr hy, hyb⟩) hxy
      · rw [hf_high hyb]
        by_cases hxb : x < b
        · rw [hf_low hxb]
          exact (hc.1 x ((hF x).mpr ⟨(hE x).mpr hx, hxb⟩)).trans_le
            (hab.le.trans (le_of_not_gt hyb))
        · rw [hf_high hxb]
          exact hxy
    have hrel : ∀ k, ∀ x : S.Limit, x.val ∈ (S.stage n).U →
        ∀ y : S.Limit, y.val ∈ (S.stage n).U →
          S.limitRel k x y → S.limitRel k (f x) (f y) := by
      intro k x hx y hy hxy
      by_cases hyb : y < b
      · have hxb : x < b := (S.rel_le hxy).trans_lt hyb
        rw [hf_low hxb, hf_low hyb]
        have hxF := (hF x).mpr ⟨(hE x).mpr hx, hxb⟩
        have hyF := (hF y).mpr ⟨(hE y).mpr hy, hyb⟩
        cases k with
        | one => exact hc.2.2.2.1 x hxF y hyF hxy
        | two => exact hc.2.2.2.2 x hxF y hyF hxy
      · rw [hf_high hyb]
        by_cases hxb : x < b
        · rw [hf_low hxb]
          have hxF := (hF x).mpr ⟨(hE x).mpr hx, hxb⟩
          by_cases hxa : x < a
          · rw [hc.2.1 x hxF hxa]
            exact hxy
          · have hax : a ≤ x := le_of_not_gt hxa
            have hby : b ≤ y := le_of_not_gt hyb
            have hax₁ : S.limitRel .one a x :=
              S.rel_convex_one x.property hax hxb.le hab₁
            have hxy₁ : S.limitRel .one x y := by
              cases k with
              | one => exact hxy
              | two => exact S.rel_two_one hxy
            have hxb₁ : S.limitRel .one x b :=
              S.rel_convex_one b.property hxb.le hby hxy₁
            have hay₁ : S.limitRel .one a y := S.rel_trans hax₁ hxy₁
            cases k with
            | one => exact S.rel_trans (hlinks x hxF hax hxb₁) hay₁
            | two =>
                have hby₁ := hcase y ((hE y).mpr hy) hby hay₁
                exact ((hclaim x hax hxb hxb₁).2
                  (S.rel_respect_two hxb.le hby hxy hby₁)).elim
        · rw [hf_high hxb]
          exact hxy
    have hrigid := S.le_of_stage_limitCovering hPn hmono hrel ha'
    have hfa : f a < a := by
      rw [hf_low hab]
      exact hc.1 a ((hF a).mpr ⟨(hE a).mpr ha', hab⟩)
    exact (not_le_of_gt hfa) hrigid
  · -- Case 2.2: cofinal copies compress the finite first-relation interval at `b`.
    push Not at hcase
    obtain ⟨d, hdE, hbd, had₁, hbdnot⟩ := hcase
    let B := E.filter (S.limitRel .one b)
    have hbB : b ∈ B := Finset.mem_filter.mpr
      ⟨(hE b).mpr hb', S.rel_refl .one b.property⟩
    have hB : B.Nonempty := ⟨b, hbB⟩
    let c := B.max' hB
    have hcB : c ∈ B := B.max'_mem hB
    have hcE : c ∈ E := (Finset.mem_filter.mp hcB).1
    have hbc₁ : S.limitRel .one b c := (Finset.mem_filter.mp hcB).2
    have hbc : b ≤ c := S.rel_le hbc₁
    have hcd : c < d := by
      by_contra hnotcd
      exact hbdnot (S.rel_convex_one d.property hbd (le_of_not_gt hnotcd) hbc₁)
    have hmax (z : S.Limit) (hz : z ∈ E) (hbz : S.limitRel .one b z) : z ≤ c :=
      B.le_max' z (Finset.mem_filter.mpr ⟨hz, hbz⟩)
    have hinterval (z : S.Limit) (hbz : b ≤ z) (hzc : z ≤ c) :
        S.limitRel .one b z := S.rel_convex_one z.property hbz hzc hbc₁
    let F := E.filter (· ≤ c)
    let X := F.filter (· < a)
    let A : Str S.Limit := ⟨F, S.limitRel .one, S.limitRel .two⟩
    have hF (z : S.Limit) : z ∈ F ↔ z ∈ E ∧ z ≤ c := Finset.mem_filter
    have hX (z : S.Limit) : z ∈ X ↔ z ∈ F ∧ z < a := Finset.mem_filter
    have hXbelow : ∀ z ∈ X, z < a := fun z hz => ((hX z).mp hz).2
    have hcopies : CofinalCopies (S.limitRel .one) (S.limitRel .two) X
        A.indexedFirst A.indexedSecond a :=
      (hS.firstCondition had₁).cofinalCopies (S.rel_le had₁) F
        (fun z hz => ((hF z).mp hz).2.trans_lt hcd)
    have hcopies' := hsem.2.2 X hXbelow A.U.card A.indexedFirst A.indexedSecond hcopies
    let L := E.filter (· < b)
    have haL : a ∈ L := Finset.mem_filter.mpr ⟨(hE a).mpr ha', hab⟩
    have hL : L.Nonempty := ⟨a, haL⟩
    have hLbelow : L.max' hL < b := (Finset.mem_filter.mp (L.max'_mem hL)).2
    have hbound (z : S.Limit) (hz : z ∈ E) (hzb : z < b) : z ≤ L.max' hL :=
      L.le_max' z (Finset.mem_filter.mpr ⟨hz, hzb⟩)
    obtain ⟨Y, hY, hcover⟩ := hcopies' (L.max' hL) hLbelow
    have hsource : ∀ x ∈ X, ∀ z ∈ A.U, z ∉ X → x < z := by
      intro x hx z hz hzX
      have haz : a ≤ z := le_of_not_gt (fun hza => hzX ((hX z).mpr ⟨hz, hza⟩))
      exact (hXbelow x hx).trans_le haz
    have htarget : ∀ x ∈ X, ∀ y ∈ Y, id x < y := by
      intro x hx y hy
      have hxE := ((hF x).mp ((hX x).mp hx).1).1
      exact (hbound x hxE ((hXbelow x hx).trans hab)).trans_lt (hY y hy).1
    have hcover' : CoversStructure (S.limitRel .one) (S.limitRel .two)
        (X.image id ∪ Y) A.indexedFirst A.indexedSecond := by
      rw [Finset.image_id]
      exact hcover
    letI : Nonempty S.Limit := ⟨a⟩
    obtain ⟨g, hg, hgfix, hgnew⟩ :=
      Str.exists_covering_extension_of_coversStructure
        (A := A) (X := X) (Y := Y) (h := id)
        (fun z hz => ((hX z).mp hz).1) hsource
        (fun _ _ _ _ hxy => hxy) htarget hcover'
    have hgbounds (z : S.Limit) (hz : z ∈ F) (haz : a ≤ z) :
        L.max' hL < g z ∧ g z < b :=
      hY (g z) (hgnew z hz (fun hzX => (not_lt_of_ge haz) (hXbelow z hzX)))
    let f : S.Limit → S.Limit := fun z => if b ≤ z ∧ z ≤ c then g z else z
    have hf_in {z : S.Limit} (hz : b ≤ z ∧ z ≤ c) : f z = g z := if_pos hz
    have hf_out {z : S.Limit} (hz : ¬ (b ≤ z ∧ z ≤ c)) : f z = z := if_neg hz
    have hfin (z : S.Limit) (hz : z ∈ E) (hbz : b ≤ z ∧ z ≤ c) :
        z ∈ F := (hF z).mpr ⟨hz, hbz.2⟩
    have hfle (z : S.Limit) (hz : z ∈ E) : f z ≤ z := by
      by_cases hzin : b ≤ z ∧ z ≤ c
      · rw [hf_in hzin]
        exact ((hgbounds z (hfin z hz hzin) (hab.le.trans hzin.1)).2.trans_le hzin.1).le
      · rw [hf_out hzin]
    have hmono : ∀ x : S.Limit, x.val ∈ (S.stage n).U →
        ∀ y : S.Limit, y.val ∈ (S.stage n).U → x < y → f x < f y := by
      intro x hx y hy hxy
      have hxE := (hE x).mpr hx
      have hyE := (hE y).mpr hy
      by_cases hxin : b ≤ x ∧ x ≤ c
      · rw [hf_in hxin]
        by_cases hyin : b ≤ y ∧ y ≤ c
        · rw [hf_in hyin]
          exact hg.1 x (hfin x hxE hxin) y (hfin y hyE hyin) hxy
        · rw [hf_out hyin]
          exact ((hgbounds x (hfin x hxE hxin) (hab.le.trans hxin.1)).2.trans_le
            hxin.1).trans hxy
      · rw [hf_out hxin]
        by_cases hyin : b ≤ y ∧ y ≤ c
        · rw [hf_in hyin]
          have hxb : x < b := lt_of_not_ge (fun hbx => hxin ⟨hbx, hxy.le.trans hyin.2⟩)
          exact (hbound x hxE hxb).trans_lt
            (hgbounds y (hfin y hyE hyin) (hab.le.trans hyin.1)).1
        · rw [hf_out hyin]
          exact hxy
    have hmono_le (x : S.Limit) (hx : x.val ∈ (S.stage n).U)
        (y : S.Limit) (hy : y.val ∈ (S.stage n).U) (hxy : x ≤ y) : f x ≤ f y := by
      rcases hxy.lt_or_eq with hxy | rfl
      · exact (hmono x hx y hy hxy).le
      · exact le_rfl
    have hrel : ∀ k, ∀ x : S.Limit, x.val ∈ (S.stage n).U →
        ∀ y : S.Limit, y.val ∈ (S.stage n).U →
          S.limitRel k x y → S.limitRel k (f x) (f y) := by
      intro k x hx y hy hxy
      have hxE := (hE x).mpr hx
      have hyE := (hE y).mpr hy
      have hxyord : x ≤ y := S.rel_le hxy
      by_cases hxin : b ≤ x ∧ x ≤ c
      · have hxy₁ : S.limitRel .one x y := by
          cases k with
          | one => exact hxy
          | two => exact S.rel_two_one hxy
        have hby₁ : S.limitRel .one b y :=
          S.rel_trans (hinterval x hxin.1 hxin.2) hxy₁
        have hyin : b ≤ y ∧ y ≤ c := ⟨hxin.1.trans hxyord, hmax y hyE hby₁⟩
        rw [hf_in hxin, hf_in hyin]
        cases k with
        | one => exact hg.2.1 x (hfin x hxE hxin) y (hfin y hyE hyin) hxy
        | two => exact hg.2.2 x (hfin x hxE hxin) y (hfin y hyE hyin) hxy
      · rw [hf_out hxin]
        cases k with
        | one =>
            have hxfy : x ≤ f y := by
              simpa only [hf_out hxin] using hmono_le x hx y hy hxyord
            exact S.rel_convex_one (f y).property hxfy (hfle y hyE) hxy
        | two =>
            by_cases hyin : b ≤ y ∧ y ≤ c
            · rw [hf_in hyin]
              have hxc : x ≤ c := hxyord.trans hyin.2
              have hxb : x < b := lt_of_not_ge (fun hbx => hxin ⟨hbx, hxc⟩)
              have hxa : x < a := by
                by_contra hnotxa
                have hax : a ≤ x := le_of_not_gt hnotxa
                have hxb₁ : S.limitRel .one x b :=
                  S.rel_convex_one b.property hxb.le hyin.1 (S.rel_two_one hxy)
                exact (hclaim x hax hxb hxb₁).2
                  (S.rel_respect_two hxb.le hyin.1 hxy (hinterval y hyin.1 hyin.2))
              have hxF : x ∈ F := (hF x).mpr ⟨hxE, hxc⟩
              have hfix : g x = x := hgfix x ((hX x).mpr ⟨hxF, hxa⟩)
              rw [← hfix]
              exact hg.2.2 x hxF y (hfin y hyE hyin) hxy
            · rw [hf_out hyin]
              exact hxy
    have hrigid := S.le_of_stage_limitCovering hPn hmono hrel hb'
    have hfb : f b < b := by
      rw [hf_in ⟨le_rfl, hbc⟩]
      exact (hgbounds b ((hF b).mpr ⟨(hE b).mpr hb', hbc⟩) hab.le).2
    exact (not_le_of_gt hfb) hrigid

end GeneratingSequence
end Alexander313.Carlson
