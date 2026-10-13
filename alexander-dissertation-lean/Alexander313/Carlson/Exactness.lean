import Alexander313.Carlson.GeneratingRules

/-!
# Exact subpatterns and initial cuts

Carlson, Definition 15.5 and Lemma 15.6, in the pure language. The initial
span of `P` in `Q` consists of the points of `Q` below some point of `P`.
For a nonempty finite `P` this is precisely the cut through its maximum;
for an empty `P` it is empty. Exactness means that `P` generates this span
and the span is 1-correct in `Q`.

For any downward closed carrier, 1-correctness is equivalent to the
absence of first-relation edges leaving it. This characterization is the
cut condition used in Carlson's isominimal restriction lemma.
-/

noncomputable section

namespace Alexander313.Carlson.Str

variable {α : Type*} [LinearOrder α]

/-- The carrier points at or below the specified cutoff. -/
def initialCut (Q : Str α) (a : α) : Str α :=
  Q.restrict (Q.U.filter (fun x => x ≤ a))

@[simp] theorem mem_initialCut {Q : Str α} {a x : α} :
    x ∈ (Q.initialCut a).U ↔ x ∈ Q.U ∧ x ≤ a := by
  simp [initialCut, restrict]

theorem initialCut_isSub (Q : Str α) (a : α) : IsSub (Q.initialCut a) Q :=
  Q.restrict_isSub (Finset.filter_subset _ _)

/-- The initial span through a finite carrier, including its empty case. -/
def initialSpan (Q : Str α) (U : Finset α) : Str α :=
  Q.restrict (Q.U.filter (fun x => ∃ p ∈ U, x ≤ p))

@[simp] theorem mem_initialSpan {Q : Str α} {U : Finset α} {x : α} :
    x ∈ (Q.initialSpan U).U ↔ x ∈ Q.U ∧ ∃ p ∈ U, x ≤ p := by
  simp [initialSpan, restrict]

theorem initialSpan_isSub (Q : Str α) (U : Finset α) : IsSub (Q.initialSpan U) Q :=
  Q.restrict_isSub (Finset.filter_subset _ _)

@[simp] theorem initialSpan_empty (Q : Str α) :
    Q.initialSpan ∅ = Q.restrict ∅ := by
  simp [initialSpan]

theorem initialSpan_eq_initialCut (Q : Str α) (U : Finset α) (hU : U.Nonempty) :
    Q.initialSpan U = Q.initialCut (U.max' hU) := by
  apply congrArg Q.restrict
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, p, hp, hxp⟩
    exact ⟨hx, hxp.trans (U.le_max' p hp)⟩
  · rintro ⟨hx, hxa⟩
    exact ⟨hx, U.max' hU, U.max'_mem hU, hxa⟩

theorem initialSpan_eq_of_bounded {P Q : Str α}
    (hb : ∀ x ∈ Q.U, ∃ p ∈ P.U, x ≤ p) : Q.initialSpan P.U = Q := by
  have hU : Q.U.filter (fun x => ∃ p ∈ P.U, x ≤ p) = Q.U :=
    Finset.filter_true_of_mem hb
  cases Q
  simp only [initialSpan, hU, restrict]

/-- For an initial subcarrier, correctness says exactly that no first
edge can cross its boundary. -/
theorem kCorrect_one_iff_no_crossing {Q : Str α} {U : Finset α}
    (hU : U ⊆ Q.U)
    (hlower : ∀ x ∈ Q.U, ∀ p ∈ U, x ≤ p → x ∈ U) :
    KCorrect (Q.restrict U) Q .one ↔
      ∀ x ∈ U, ∀ y ∈ Q.U, Q.r₁ x y → y ∈ U := by
  constructor
  · intro hc x hx y hy hxy
    by_cases hle : y ≤ x
    · exact hlower y hy x hx hle
    · obtain ⟨p, hp, _⟩ := hc x x y (hU hx) hy
        ⟨hx, le_rfl, fun _ _ h => h⟩ (lt_of_not_ge hle) hxy
      exact hlower y hy p hp.1 hp.2.1
  · intro hclosed p x y hx hy hp hpy hxy
    have hxU := hlower x hx p hp.1 hp.2.1
    have hpx : p = x := hp.unique ⟨hxU, le_rfl, fun _ _ h => h⟩
    subst p
    have hyU := hclosed x hxU y hy hxy
    exact ⟨y, ⟨hyU, le_rfl, fun _ _ h => h⟩, hxy⟩

theorem initialCut_correct_iff (Q : Str α) (a : α) :
    KCorrect (Q.initialCut a) Q .one ↔
      ∀ x ∈ Q.U, x ≤ a → ∀ y ∈ Q.U, Q.r₁ x y → y ≤ a := by
  have h := kCorrect_one_iff_no_crossing
    (Q := Q) (U := Q.U.filter (fun x => x ≤ a))
    (Finset.filter_subset _ _)
    (fun x hx p hp hxp => Finset.mem_filter.mpr
      ⟨hx, hxp.trans (Finset.mem_filter.mp hp).2⟩)
  refine h.trans ⟨?_, ?_⟩
  · intro h x hx hxa y hy hxy
    exact (Finset.mem_filter.mp
      (h x (Finset.mem_filter.mpr ⟨hx, hxa⟩) y hy hxy)).2
  · intro h x hx y hy hxy
    obtain ⟨hx, hxa⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hy, h x hx hxa y hy hxy⟩

theorem initialSpan_correct_iff (Q : Str α) (U : Finset α) :
    KCorrect (Q.initialSpan U) Q .one ↔
      ∀ x ∈ (Q.initialSpan U).U, ∀ y ∈ Q.U, Q.r₁ x y →
        y ∈ (Q.initialSpan U).U :=
  kCorrect_one_iff_no_crossing (Finset.filter_subset _ _)
    (fun x hx p hp hxp => by
      obtain ⟨_, q, hq, hpq⟩ := mem_initialSpan.mp hp
      exact mem_initialSpan.mpr ⟨hx, q, hq, hxp.trans hpq⟩)

/-- Carlson's Definition 15.5, with the initial span avoiding an
undefined maximum for the empty pattern. -/
structure Exact (P Q : Str α) : Prop where
  pattern : Q.IsPattern
  generates : Generates P (Q.initialSpan P.U)
  correct : KCorrect (Q.initialSpan P.U) Q .one

namespace Exact

variable {P Q R : Str α}

/-- Lemma 15.6(3): exactness includes an actual induced subpattern. -/
theorem isSub (h : Exact P Q) : IsSub P Q :=
  h.generates.isSub.trans (Q.initialSpan_isSub P.U)

theorem source_pattern (h : Exact P Q) : P.IsPattern := h.generates.source_pattern

/-- Lemma 15.6(1): a generated extension is exact. -/
theorem of_generates (d : Generates P Q) : Exact P Q := by
  have hspan := initialSpan_eq_of_bounded d.continuous.2.1
  exact ⟨d.target_pattern, hspan.symm ▸ d, hspan.symm ▸ KCorrect.refl Q .one⟩

theorem refl (hP : P.IsPattern) : Exact P P := of_generates (Generates.refl hP)

/-- Lemma 15.6(2): exactness passes to every intermediate subpattern. -/
theorem restrict (h : Exact P R) (hPQ : IsSub P Q) (hQR : IsSub Q R) :
    Exact P Q := by
  have hspan : IsSub (Q.initialSpan P.U) (R.initialSpan P.U) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨hx, hp⟩ := mem_initialSpan.mp hx
      exact mem_initialSpan.mpr ⟨hQR.1 hx, hp⟩
    · intro x hx y hy
      exact hQR.2 x (mem_initialSpan.mp hx).1 y (mem_initialSpan.mp hy).1
  have hbase : P.U ⊆ (Q.initialSpan P.U).U := by
    intro x hx
    exact mem_initialSpan.mpr ⟨hPQ.1 hx, x, hx, le_rfl⟩
  refine ⟨h.pattern.mono hQR, h.generates.restrict hspan hbase, ?_⟩
  apply (initialSpan_correct_iff Q P.U).mpr
  intro x hx y hy hxy
  have hxR : x ∈ (R.initialSpan P.U).U := hspan.1 hx
  have hyR := (initialSpan_correct_iff R P.U).mp h.correct x hxR y
    (hQR.1 hy) ((hQR.2 x (mem_initialSpan.mp hx).1 y hy).1.mp hxy)
  exact mem_initialSpan.mpr ⟨hy, (mem_initialSpan.mp hyR).2⟩

end Exact

end Alexander313.Carlson.Str
