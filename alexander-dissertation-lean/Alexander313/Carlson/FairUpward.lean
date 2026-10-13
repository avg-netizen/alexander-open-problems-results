import Alexander313.Carlson.FairDownward
import Alexander313.Carlson.SemanticTransport

/-!
# Cofinal saturation of fair generating sequences

Carlson, *Patterns of resemblance of order 2*, Lemma 14.8(7), the
cofinal-copy clause of the second relation, in the pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 62--63 of the October 16, 2008 manuscript.

A finite copy occurring sufficiently high below a stage point gives an
extension at that point. Finite restriction makes this extension a generating
rule. Upward reflection followed by fairness realizes a copy above any
prescribed lower bound at the larger endpoint. All cofinal quantifiers range
over the limit carrier, including when that carrier has a least point.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {S : GeneratingSequence ℚ}

/-- A copy just below `a` over one finite stage can be moved above any old
point below `b`, using upward reflection of its finite generating rule. -/
theorem Fair.transfer_copy (hS : S.Fair) (m : ℕ) {a b c : ℚ}
    (ha : a ∈ (S.stage m).U) (hb : b ∈ (S.stage m).U)
    (hc : c ∈ (S.stage m).U) (hab : a < b) (hcb : c < b)
    (hrel : (S.stage m).r₂ a b) (X Y : Finset ℚ)
    (hX : ∀ x ∈ X, x ∈ (S.stage m).U ∧ x < a)
    (hY : ∀ y ∈ Y, y ∈ S.carrier ∧ Str.JustBelow (S.stage m).U a y)
    (hne : Y.Nonempty) {n : ℕ} {P₁ P₂ : Fin n → Fin n → Prop}
    (hcopy : CoversStructure (S.rel .one) (S.rel .two) (X ∪ Y) P₁ P₂) :
    ∃ Z : Finset ℚ, (∀ z ∈ Z, z ∈ S.carrier ∧ c < z ∧ z < b) ∧
      CoversStructure (S.rel .one) (S.rel .two) (X ∪ Z) P₁ P₂ := by
  classical
  let P := S.stage m
  let Q := S.restrict (P.U ∪ Y)
  have hYP : ∀ y ∈ Y, y ∉ P.U := fun y hy => (hY y hy).2.not_mem
  have hQU : ∀ x ∈ P.U ∪ Y, x ∈ S.carrier := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact S.mem_carrier m hx
    · exact (hY x hx).1
  have hsub : Str.IsSub P Q := S.stage_isSub_restrict Finset.subset_union_left
  have hext : Str.ExtensionAt P Q a := by
    refine ⟨hsub, ha, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := hne
      exact ⟨y, Finset.mem_union_right _ hy, hYP y hy⟩
    · intro y hyQ hyP
      exact (hY y ((Finset.mem_union.mp hyQ).resolve_left hyP)).2
  obtain ⟨i, hi⟩ := S.finite_capture (P.U ∪ Y) hQU
  have hcap : Q.U ⊆ (S.stage (max m i)).U :=
    hi.trans (S.isSub (Nat.le_max_right m i)).1
  have hgen : Str.GeneratingRule P Q :=
    .finiteRestriction (S.exactlyGenerates (Nat.le_max_left m i))
      (S.restrict_isSub hcap) hext
  obtain ⟨N, g, D⟩ := Str.UpData.exists_rat hgen.target_pattern
    hgen.continuous hext hb hab hrel
  let R := P.upward Q a b N g
  let L := P.U.filter (· < a)
  have hdiff : Q.U \ P.U = Y := by
    ext y
    simp only [Q, restrict, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hy | hy, hn⟩
      · exact (hn hy).elim
      · exact hy
    · intro hy
      exact ⟨Or.inr hy, hYP y hy⟩
  have e : Str.IsIso (R.restrict (L ∪ N)) (Q.restrict (L ∪ Y))
      (fun z => if z ∈ N then g z else z) := by
    simpa only [hdiff] using D.copiedBlock_isIso
  obtain ⟨f, ef, hleft, hright⟩ := e.exists_inverse
  have hXL : X ⊆ L := fun x hx => Finset.mem_filter.mpr (hX x hx)
  have hsource : X ∪ Y ⊆ L ∪ Y := Finset.union_subset_union_left hXL
  have f_old (x : ℚ) (hx : x ∈ L) : f x = x := by
    have hxP : x ∈ P.U := (Finset.mem_filter.mp hx).1
    have hxN : x ∉ N := fun hn => D.hNP x hn hxP
    simpa only [if_neg hxN] using hleft x (Finset.mem_union_left N hx)
  have f_new (y : ℚ) (hy : y ∈ Y) : f y ∈ N := by
    have hfmem := ef.mem (Finset.mem_union_right L hy)
    rcases Finset.mem_union.mp hfmem with hfL | hfN
    · have hfP := (Finset.mem_filter.mp hfL).1
      have hfN : f y ∉ N := fun hn => D.hNP (f y) hn hfP
      have heq : f y = y := by
        simpa only [if_neg hfN] using hright y (Finset.mem_union_right L hy)
      exact (hYP y hy (heq ▸ hfP)).elim
    · exact hfN
  obtain ⟨t, htmem, htfix, htmono, htrel⟩ :=
    hS.realizes m R (Str.GeneratingRule.upward hgen D)
  have hfR (x : ℚ) (hx : x ∈ X ∪ Y) : f x ∈ R.U := by
    have hf := ef.mem (hsource hx)
    rcases Finset.mem_union.mp hf with hf | hf
    · exact Finset.mem_union_left N (Finset.mem_filter.mp hf).1
    · exact Finset.mem_union_right P.U hf
  let u : ℚ → ℚ := fun x => t (f x)
  have u_old (x : ℚ) (hx : x ∈ X) : u x = x := by
    dsimp only [u]
    rw [f_old x (hXL hx), htfix x (hX x hx).1]
  have huimage : (X ∪ Y).image u = X ∪ Y.image u := by
    rw [Finset.image_union]
    congr 1
    calc
      X.image u = X.image id := Finset.image_congr (fun x hx => u_old x hx)
      _ = X := Finset.image_id
  refine ⟨Y.image u, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hfy := f_new y hy
    have hfyR : f y ∈ R.U := Finset.mem_union_right P.U hfy
    have hcR : c ∈ R.U := Finset.mem_union_left N hc
    have hbR : b ∈ R.U := Finset.mem_union_left N hb
    refine ⟨htmem (f y) hfyR, ?_, ?_⟩
    · have hlt := htmono c hcR (f y) hfyR (D.hNL (f y) hfy c hc hcb)
      simpa only [htfix c hc, u] using hlt
    · have hlt := htmono (f y) hfyR b hbR (D.hNb (f y) hfy)
      simpa only [htfix b hb, u] using hlt
  · rw [← huimage]
    apply hcopy.image u
    · intro x hx y hy hxy
      exact htmono (f x) (hfR x hx) (f y) (hfR y hy)
        (ef.2.1 x (hsource hx) y (hsource hy) hxy)
    · intro x hx y hy hxy
      exact (htrel (f x) (hfR x hx) (f y) (hfR y hy)).1.mp
        ((ef.2.2 x (hsource hx) y (hsource hy)).1.mp hxy)
    · intro x hx y hy hxy
      exact (htrel (f x) (hfR x hx) (f y) (hfR y hy)).2.mp
        ((ef.2.2 x (hsource hx) y (hsource hy)).2.mp hxy)

/-- Lemma 14.8(7), the cofinal clause of the second relation. The finite
structures being copied are arbitrary indexed relations, as in `CofinalCondition`.
No coveredness or well-foundedness assumption is needed for this direction. -/
theorem Fair.cofinalCondition (hS : S.Fair) {a b : S.Limit}
    (hrel : S.limitRel .two a b) :
    CofinalCondition (S.limitRel .one) (S.limitRel .two) a b := by
  classical
  intro X hXa n P₁ P₂ hcof
  by_cases heq : a = b
  · subst b
    exact hcof
  have hab : a < b := lt_of_le_of_ne (S.rel_le hrel) heq
  intro c hcb
  let E : Finset S.Limit := insert a (insert b (insert c X))
  obtain ⟨m, hm⟩ := S.finite_capture (E.image Subtype.val) (by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    exact z.property)
  have hcap (x : S.Limit) (hx : x ∈ E) : x.val ∈ (S.stage m).U :=
    hm (Finset.mem_image_of_mem Subtype.val hx)
  have ha : a.val ∈ (S.stage m).U := hcap a (by simp only [E, Finset.mem_insert_self])
  have hb : b.val ∈ (S.stage m).U := hcap b (by simp [E])
  have hc : c.val ∈ (S.stage m).U := hcap c (by simp [E])
  let X₀ : Finset ℚ := X.image Subtype.val
  have hX₀ (x : ℚ) (hx : x ∈ X₀) : x ∈ (S.stage m).U ∧ x < a.val := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hcap z (by simp [E, hz]), hXa z hz⟩
  let L := (S.stage m).U.filter (· < a.val)
  have cutoff : ∃ d : S.Limit, d < a ∧
      ∀ x ∈ (S.stage m).U, x < a.val → x ≤ d.val := by
    by_cases hL : L.Nonempty
    · have hd := L.max'_mem hL
      refine ⟨⟨L.max' hL, S.mem_carrier m (Finset.mem_filter.mp hd).1⟩,
        (Finset.mem_filter.mp hd).2, ?_⟩
      intro x hx hxa
      exact L.le_max' x (Finset.mem_filter.mpr ⟨hx, hxa⟩)
    · obtain ⟨f, hf⟩ := hS.firstCondition (S.rel_two_one hrel) {a} (by
        intro z hz
        have hza : z = a := Finset.mem_singleton.mp hz
        simpa only [hza] using hab)
      refine ⟨f a, hf.1 a (Finset.mem_singleton_self a), ?_⟩
      intro x hx hxa
      exact (hL ⟨x, Finset.mem_filter.mpr ⟨hx, hxa⟩⟩).elim
  obtain ⟨d, hda, hd⟩ := cutoff
  obtain ⟨Y, hY, hcopy⟩ := hcof d hda
  by_cases hne : Y.Nonempty
  · let Y₀ : Finset ℚ := Y.image Subtype.val
    have hY₀ (y : ℚ) (hy : y ∈ Y₀) :
        y ∈ S.carrier ∧ Str.JustBelow (S.stage m).U a.val y := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      refine ⟨z.property, ha, (hY z hz).2, ?_⟩
      intro x hx hxa
      exact (hd x hx hxa).trans_lt (hY z hz).1
    have hcopy₀ : CoversStructure (S.rel .one) (S.rel .two) (X₀ ∪ Y₀) P₁ P₂ := by
      have h := hcopy.image Subtype.val (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      simpa only [Finset.image_union] using h
    obtain ⟨Z, hZ, hcZ⟩ := hS.transfer_copy m ha hb hc hab hcb
      ((S.rel_iff m ha hb .two).mp hrel) X₀ Y₀ hX₀ hY₀
      (hne.image Subtype.val) hcopy₀
    let q : ℚ → S.Limit := fun x => if hx : x ∈ S.carrier then ⟨x, hx⟩ else a
    have q_val (x : ℚ) (hx : x ∈ S.carrier) : (q x).val = x := by
      simp only [q, dif_pos hx]
    have q_on (x : S.Limit) : q x.val = x := Subtype.ext (q_val x.val x.property)
    have hqX : X₀.image q = X := by
      rw [Finset.image_image]
      calc
        X.image (q ∘ Subtype.val) = X.image id :=
          Finset.image_congr (fun x _ => q_on x)
        _ = X := Finset.image_id
    have hcarrier (x : ℚ) (hx : x ∈ X₀ ∪ Z) : x ∈ S.carrier := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact S.mem_carrier m (hX₀ x hx).1
      · exact (hZ x hx).1
    refine ⟨Z.image q, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      change c.val < (q y).val ∧ (q y).val < b.val
      rw [q_val y (hZ y hy).1]
      exact (hZ y hy).2
    · have h : CoversStructure (S.limitRel .one) (S.limitRel .two)
          ((X₀ ∪ Z).image q) P₁ P₂ := hcZ.image q
        (fun x hx y hy hxy => by
          change (q x).val < (q y).val
          rwa [q_val x (hcarrier x hx), q_val y (hcarrier y hy)])
        (fun x hx y hy hxy => by
          change S.rel .one (q x).val (q y).val
          rwa [q_val x (hcarrier x hx), q_val y (hcarrier y hy)])
        (fun x hx y hy hxy => by
          change S.rel .two (q x).val (q y).val
          rwa [q_val x (hcarrier x hx), q_val y (hcarrier y hy)])
      rw [Finset.image_union, hqX] at h
      exact h
  · have hYempty : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst Y
    exact ⟨∅, fun _ h => (Finset.notMem_empty _ h).elim, hcopy⟩

end GeneratingSequence
end Alexander313.Carlson
