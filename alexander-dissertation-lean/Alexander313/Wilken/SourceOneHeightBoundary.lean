import Alexander313.Wilken.SourceOneCanonicalHeight
import Alexander313.Wilken.FiniteBoundaryIdentity
import Alexander313.Wilken.GlobalBaseArithmetic

/-!
# Lemma 2.22 at the special original base one

The descending endpoint is the actual θ₀(θ₁(...θₙ(0)...)), including
θ₀(0)=1 at index zero. Genuine finite coverage and the constructed minimum
fragment identify its strict initial interval with canonical height ≤n.
This proves the exact minimum for every original raw low code and literal
height for every original normal low tree. The zero case is proved through
the original parameter admission rather than an epsilon-base hypothesis.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.HeightBoundary

noncomputable def endpoint (n : Nat) : Ordinal.{0} := globalDescendingTerm 1 n 0

theorem endpoint_zero : endpoint 0 = 1 := by
  change globalCollapse 1 0 0 = 1
  simpa only [omegaSequence_zero] using globalCollapse_zero 1 zero_lt_one
    Ordinal.isPrincipal_add_one 0

theorem endpoint_eq_finiteBoundary (n : Nat) (hn : 0 < n) :
    endpoint n = finiteBoundary 1 n 0 :=
  (finiteBoundary_eq_globalDescendingTerm 1 zero_lt_one n 0 hn).symm

theorem endpoint_lt_cardinal (n : Nat) : endpoint n < omegaSequence 1 1 := by
  by_cases hn : n = 0
  · subst n
    rw [endpoint_zero]
    simpa only [omegaSequence_zero] using (omegaSequence_strictMono 1) (by omega : 0 < 1)
  · rw [endpoint_eq_finiteBoundary n (by omega)]
    exact finiteBoundary_lt_cardinal 1 zero_lt_one n 0 (by omega)

theorem input_spec (c : Nat) (hc : PublicCodes.lowCheckCode c = true) :
    PublicCodes.checkCode c = true ∧ PublicCodes.interpretation c < omegaSequence 1 1 := by
  have hs := Bool.and_eq_true_iff.mp hc
  obtain ⟨t, rfl, ht⟩ := (PublicCodes.checkCode_iff c).mp hs.1
  have hsort : t.outerSort ≤ 1 := by
    simpa only [PublicCodes.outerSortCode_code, decide_eq_true_eq] using hs.2
  exact ⟨by simpa only [PublicCodes.checkCode_code] using ht,
    by simpa only [PublicCodes.interpretation_code] using
      (PublicCodes.denote_lt_iff_outerSort_le t ht 1 (by omega)).mpr hsort⟩

theorem canonicalHeightCode_le_iff_finiteBoundary (n c : Nat)
    (hc : PublicCodes.lowCheckCode c = true) (hn : 0 < n) :
    CanonicalHeight.canonicalHeightCode c ≤ n ↔ PublicCodes.interpretation c < finiteBoundary 1 n 0 := by
  have hs := input_spec c hc
  rw [CanonicalHeight.canonicalHeightCode_fragment_iff n c hs.1]
  constructor
  · rintro ⟨t, ht, hv⟩
    have hvf : denote n t = PublicCodes.interpretation c :=
      (PublicCodes.denote_eq_finite n t ht).symm.trans hv
    have hnotation := (PublicCodes.sourceNotation_iff_natTerm n hn _).mpr ⟨t, ht, hvf⟩
    exact (source_finite_notation_low_iff_lt_boundary 1 zero_lt_one n 0 hn _).mp
      ⟨hnotation, hs.2⟩
  · intro hb
    have hnotation := ((source_finite_notation_low_iff_lt_boundary 1 zero_lt_one n 0 hn _).mpr hb).1
    obtain ⟨t, ht, hv⟩ := (PublicCodes.sourceNotation_iff_natTerm n hn _).mp hnotation
    exact ⟨t, ht, (PublicCodes.denote_eq_finite n t ht).trans hv⟩

theorem canonicalHeightCode_le_iff_endpoint (n c : Nat)
    (hc : PublicCodes.lowCheckCode c = true) :
    CanonicalHeight.canonicalHeightCode c ≤ n ↔ PublicCodes.interpretation c < endpoint n := by
  by_cases hn : n = 0
  · subst n
    rw [Nat.le_zero, endpoint_zero, CanonicalHeight.canonicalHeightCode_zero_iff c (input_spec c hc).1]
    simp
  · rw [endpoint_eq_finiteBoundary n (by omega)]
    exact canonicalHeightCode_le_iff_finiteBoundary n c hc (by omega)

/-- The exact printed minimum, for every original raw base-one low code. -/
theorem source_lemma_2_22 (c : Nat) (hc : PublicCodes.lowCheckCode c = true) :
    IsLeast {n : Nat | PublicCodes.interpretation c < endpoint n}
      (CanonicalHeight.canonicalHeightCode c) := by
  constructor
  · exact (canonicalHeightCode_le_iff_endpoint _ c hc).mp le_rfl
  · intro n hn; exact (canonicalHeightCode_le_iff_endpoint n c hc).mpr hn

theorem normalCode_height_le_iff_endpoint (n c : Nat)
    (hc : PublicCodes.lowCheckCode c = true) (hn : Comparison.acceptedCode c = true) :
    heightCode c ≤ n ↔ PublicCodes.interpretation c < endpoint n := by
  rw [← CanonicalHeight.canonicalHeightCode_normal c hn]
  exact canonicalHeightCode_le_iff_endpoint n c hc

theorem source_lemma_2_22_normalCode (c : Nat) (hc : PublicCodes.lowCheckCode c = true)
    (hn : Comparison.acceptedCode c = true) :
    IsLeast {n : Nat | PublicCodes.interpretation c < endpoint n} (heightCode c) := by
  simpa only [CanonicalHeight.canonicalHeightCode_normal c hn] using source_lemma_2_22 c hc

theorem source_lemma_2_22_term (n : Nat) (t : RelativeTerm Nat)
    (ht : admissible n t) (hn : Normal n t) (hlow : t.outerSort ≤ 1) :
    IsLeast {m : Nat | PublicCodes.denote t < endpoint m} t.height := by
  have hc : PublicCodes.lowCheckCode t.code = true := by
    rw [PublicCodes.lowCheckCode_code, PublicCodes.lowCheck, Bool.and_eq_true]
    exact ⟨Height.admitted_checked n t ht, by simpa only [decide_eq_true_eq] using hlow⟩
  have ha : Comparison.acceptedCode t.code = true := by
    rw [Comparison.acceptedCode_code, Bool.and_eq_true]
    exact ⟨Height.admitted_checked n t ht, (Comparison.normalCheck_correct n t ht).mpr hn⟩
  simpa only [PublicCodes.interpretation_code, heightCode_code] using source_lemma_2_22_normalCode t.code hc ha

theorem canonicalHeightCode_eq_succ_iff_strip (n c : Nat) (hc : PublicCodes.lowCheckCode c = true) :
    CanonicalHeight.canonicalHeightCode c = n + 1 ↔
      endpoint n ≤ PublicCodes.interpretation c ∧ PublicCodes.interpretation c < endpoint (n + 1) := by
  have h0 := canonicalHeightCode_le_iff_endpoint n c hc
  have h1 := canonicalHeightCode_le_iff_endpoint (n + 1) c hc
  constructor
  · intro hh
    refine ⟨?_, h1.mp (by omega)⟩
    exact le_of_not_gt (fun hv => by have h := h0.mpr hv; omega)
  · rintro ⟨hlo, hhi⟩
    have hupper := h1.mpr hhi
    have hlower : ¬CanonicalHeight.canonicalHeightCode c ≤ n := fun h => (h0.mp h).not_ge hlo
    omega

def belowEndpointCheck (n c : Nat) : Bool :=
  PublicCodes.lowCheckCode c && decide (CanonicalHeight.canonicalHeightCode c ≤ n)

theorem belowEndpointCheck_primrec : Primrec₂ belowEndpointCheck :=
  (Primrec.and.comp (PublicCodes.lowCheckCode_primrec.comp Primrec.snd)
    (Primrec.nat_le.comp (CanonicalHeight.canonicalHeightCode_primrec.comp Primrec.snd) Primrec.fst).decide).to₂

theorem belowEndpointCheck_exact (n c : Nat) : belowEndpointCheck n c = true ↔
    PublicCodes.lowCheckCode c = true ∧ PublicCodes.interpretation c < endpoint n := by
  simp only [belowEndpointCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_le_iff_endpoint n c hc).mp hh⟩
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_le_iff_endpoint n c hc).mpr hh⟩

theorem belowEndpointCheck_invariant (n c d : Nat) (hc : PublicCodes.lowCheckCode c = true)
    (hd : PublicCodes.lowCheckCode d = true) (hv : PublicCodes.interpretation c = PublicCodes.interpretation d) :
    belowEndpointCheck n c = belowEndpointCheck n d := by
  apply Bool.eq_iff_iff.mpr
  simp only [belowEndpointCheck_exact, hc, hd, hv]

end Alexander313.Wilken.RelativeTerm.SourceOne.HeightBoundary
