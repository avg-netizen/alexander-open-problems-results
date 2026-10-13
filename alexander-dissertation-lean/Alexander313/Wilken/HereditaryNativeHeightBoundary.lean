import Alexander313.Wilken.HereditaryNativeCanonicalHeight
import Alexander313.Wilken.FiniteBoundaryIdentity

/-!
# Actual descending endpoints and native value height

The endpoint is literally θ₀(θ₁(...θₙ(0)...)), using the constructed
global collapses. For n>0 its equality with the real finite boundary,
genuine finite coverage, and original native parameter coverage identify
its initial interval with values having a representation in fragment n.
At n=0 the actual endpoint is the admitted epsilon base itself.

This proves the minimum-index characterization of source Lemma 2.22 on
EVERY original native low input. Raw inputs use the genuine normalizer's
canonical value height; original weak-normal inputs use their literal
height. It also proves the exact successive endpoint strips and genuine
normal endpoint witnesses. No endpoint, coverage, height or effectivity
oracle is assumed. Parameters remain atomic original public payloads.
The PR endpoint predicates retain the original coded-epsilon and low
admission checks. All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.HeightBoundary

open ThetaCourse

/-- The literal descending endpoint in Lemma 2.22, including θ₀(0). -/
noncomputable def endpoint (q n : Nat) : Ordinal.{0} :=
  globalDescendingTerm (base q) n 0

theorem endpoint_zero (q : Nat) (hq : baseCheck q = true) : endpoint q 0 = base q := by
  change globalCollapse (base q) 0 0 = base q
  simpa only [omegaSequence_zero] using globalCollapse_zero (base q) (base_pos q hq)
    (BaseTransformation.base_additive q hq) 0

theorem endpoint_eq_finiteBoundary (q n : Nat) (hq : baseCheck q = true) (hn : 0 < n) :
    endpoint q n = finiteBoundary (base q) n 0 :=
  (finiteBoundary_eq_globalDescendingTerm (base q) (base_pos q hq) n 0 hn).symm

theorem endpoint_lt_cardinal (q n : Nat) (hq : baseCheck q = true) :
    endpoint q n < omegaSequence (base q) 1 := by
  by_cases hn : n = 0
  · subst n
    rw [endpoint_zero q hq]
    simpa only [omegaSequence_zero] using (omegaSequence_strictMono (base q)) (by omega : 0 < 1)
  · rw [endpoint_eq_finiteBoundary q n hq (by omega)]
    exact finiteBoundary_lt_cardinal (base q) (base_pos q hq) n 0 (by omega)

/-- The original low parser supplies both the original base and the
actual low cardinal bound; neither is an additional semantic premise. -/
theorem input_spec (q c : Nat) (hc : lowCheckCode q c = true) :
    checkCode q c = true ∧ baseCheck q = true ∧
      interpretation q c < omegaSequence (base q) 1 := by
  obtain ⟨t, ht, hs⟩ := (lowCheckCode_exact q c).mp hc
  have h : check q t = true ∧ t.outerSort ≤ 1 := by
    simpa only [lowCheck, Bool.and_eq_true, decide_eq_true_eq] using hs
  refine ⟨(Bool.and_eq_true.mp hc).1, (Bool.and_eq_true.mp h.1).1, ?_⟩
  simpa only [← ht, interpretation_code] using
    (denote_lt_iff_outerSort_le q t h.1 1 (by omega)).mpr h.2

/-- For positive fragment indices, the finite endpoint criterion is
derived from the actual source notation grammar and its genuine coverage. -/
theorem canonicalHeightCode_le_iff_finiteBoundary (q n c : Nat)
    (hc : lowCheckCode q c = true) (hn : 0 < n) :
    CanonicalHeight.canonicalHeightCode q c ≤ n ↔
      interpretation q c < finiteBoundary (base q) n 0 := by
  have hs := input_spec q c hc
  rw [CanonicalHeight.canonicalHeightCode_fragment_iff q n c hs.1]
  constructor
  · rintro ⟨t, ht, hv⟩
    have hvf : finiteDenote q n t = interpretation q c :=
      (denote_eq_finite q n hs.2.1 t ht.2).symm.trans hv
    have hnotation := (sourceNotation_iff_checked q hs.2.1 n hn _).mpr ⟨t, ht, hvf⟩
    exact (source_finite_notation_low_iff_lt_boundary (base q) (base_pos q hs.2.1)
      n 0 hn _).mp ⟨hnotation, hs.2.2⟩
  · intro hb
    have hnotation := ((source_finite_notation_low_iff_lt_boundary (base q)
      (base_pos q hs.2.1) n 0 hn _).mpr hb).1
    obtain ⟨t, ht, hv⟩ := (sourceNotation_iff_checked q hs.2.1 n hn _).mp hnotation
    exact ⟨t, ht, (denote_eq_finite q n hs.2.1 t ht.2).trans hv⟩

/-- Full source endpoint characterization, with the zero-index base
case proved separately rather than passed to a positive-index theorem. -/
theorem canonicalHeightCode_le_iff_endpoint (q n c : Nat) (hc : lowCheckCode q c = true) :
    CanonicalHeight.canonicalHeightCode q c ≤ n ↔ interpretation q c < endpoint q n := by
  have hs := input_spec q c hc
  by_cases hn : n = 0
  · subst n
    rw [Nat.le_zero, endpoint_zero q hs.2.1]
    exact CanonicalHeight.canonicalHeightCode_zero_iff_below_base q c hs.1
  · rw [endpoint_eq_finiteBoundary q n hs.2.1 (by omega)]
    exact canonicalHeightCode_le_iff_finiteBoundary q n c hc (by omega)

/-- The exact minimum printed in Lemma 2.22, on every original raw low
input. The height is computed by actual native normalization. -/
theorem source_lemma_2_22 (q c : Nat) (hc : lowCheckCode q c = true) :
    IsLeast {n : Nat | interpretation q c < endpoint q n}
      (CanonicalHeight.canonicalHeightCode q c) := by
  constructor
  · exact (canonicalHeightCode_le_iff_endpoint q _ c hc).mp le_rfl
  · intro n hn
    exact (canonicalHeightCode_le_iff_endpoint q n c hc).mpr hn

theorem normalCode_height_le_iff_endpoint (q n c : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.Normal q (rawTree c)) :
    heightCode c ≤ n ↔ interpretation q c < endpoint q n := by
  have ha := (Comparison.acceptedCode_exact q c).mpr ⟨(input_spec q c hc).1, hn⟩
  rw [← CanonicalHeight.canonicalHeightCode_normal q c ha]
  exact canonicalHeightCode_le_iff_endpoint q n c hc

theorem source_lemma_2_22_normalCode (q c : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.Normal q (rawTree c)) :
    IsLeast {n : Nat | interpretation q c < endpoint q n} (heightCode c) := by
  have ha := (Comparison.acceptedCode_exact q c).mpr ⟨(input_spec q c hc).1, hn⟩
  simpa only [CanonicalHeight.canonicalHeightCode_normal q c ha] using source_lemma_2_22 q c hc

theorem source_lemma_2_22_term (q : Nat) (t : RelativeTerm Nat) (ht : lowCheck q t = true)
    (hn : Comparison.Normal q t) :
    IsLeast {n : Nat | denote q t < endpoint q n} t.height := by
  have hc : lowCheckCode q t.code = true := by simpa only [lowCheckCode_code] using ht
  simpa only [interpretation_code, heightCode_code] using
    source_lemma_2_22_normalCode q t.code hc (by simpa only [rawTree_code] using hn)

theorem canonicalHeightCode_eq_zero_iff_endpoint (q c : Nat) (hc : lowCheckCode q c = true) :
    CanonicalHeight.canonicalHeightCode q c = 0 ↔ interpretation q c < endpoint q 0 := by
  simpa only [Nat.le_zero] using canonicalHeightCode_le_iff_endpoint q 0 c hc

theorem canonicalHeightCode_eq_succ_iff_strip (q n c : Nat) (hc : lowCheckCode q c = true) :
    CanonicalHeight.canonicalHeightCode q c = n + 1 ↔
      endpoint q n ≤ interpretation q c ∧ interpretation q c < endpoint q (n + 1) := by
  have h0 := canonicalHeightCode_le_iff_endpoint q n c hc
  have h1 := canonicalHeightCode_le_iff_endpoint q (n + 1) c hc
  constructor
  · intro hh
    refine ⟨?_, h1.mp (by omega)⟩
    exact le_of_not_gt (fun hv => by have h := h0.mpr hv; omega)
  · rintro ⟨hlo, hhi⟩
    have hupper := h1.mpr hhi
    have hlower : ¬ CanonicalHeight.canonicalHeightCode q c ≤ n :=
      fun h => (h0.mp h).not_ge hlo
    omega

theorem normalCode_height_eq_succ_iff_strip (q n c : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.Normal q (rawTree c)) :
    heightCode c = n + 1 ↔
      endpoint q n ≤ interpretation q c ∧ interpretation q c < endpoint q (n + 1) := by
  have ha := (Comparison.acceptedCode_exact q c).mpr ⟨(input_spec q c hc).1, hn⟩
  rw [← CanonicalHeight.canonicalHeightCode_normal q c ha]
  exact canonicalHeightCode_eq_succ_iff_strip q n c hc

/-- Every displayed endpoint has a genuine next-fragment source
presentation, including the base endpoint at index zero. -/
theorem endpoint_next_notation (q n : Nat) (hq : baseCheck q = true) :
    sourceNotation (base q) (n + 1) 0 (endpoint q n) := by
  rw [endpoint, globalDescendingTerm_eq_firstApproximant (base q) (base_pos q hq) n 0
    (Nat.zero_le n)]
  exact finiteApproximant_lower_notation (base q) (base_pos q hq) (n + 1) 0
    (by omega) 0 le_rfl 1

/-- Genuine admitted normal witnesses show sharpness: the nth endpoint
has canonical height exactly n+1, never height at most n. -/
theorem endpoint_witness (q n : Nat) (hq : baseCheck q = true) :
    ∃ c, lowCheckCode q c = true ∧ Comparison.acceptedCode q c = true ∧
      interpretation q c = endpoint q n ∧ heightCode c = n + 1 := by
  obtain ⟨t, ht, hvf⟩ := (sourceNotation_iff_checked q hq (n + 1) (by omega) _).mp
    (endpoint_next_notation q n hq)
  have htcheck : check q t = true := (check_exact q t).mpr ⟨hq, n + 1, ht⟩
  have hv : denote q t = endpoint q n := (denote_eq_finite q (n + 1) hq t ht.2).trans hvf
  have hs : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le q t htcheck 1 (by omega)).mp
    (by simpa only [hv] using endpoint_lt_cardinal q n hq)
  have htc : checkCode q t.code = true := by simpa only [checkCode_code] using htcheck
  let c := Normalization.normalizeCode q t.code
  have hn := Normalization.normalizeCode_accepted q t.code htc
  have hcvalue : interpretation q c = endpoint q n := hn.2.trans
    (by simpa only [interpretation_code] using hv)
  have hcn := (Comparison.acceptedCode_exact q c).mp hn.1
  obtain ⟨u, hu, huc⟩ := (checkCode_exact q c).mp hcn.1
  have huvalue : denote q u = endpoint q n := by
    simpa only [← hu, interpretation_code] using hcvalue
  have hus : u.outerSort ≤ 1 := (denote_lt_iff_outerSort_le q u huc 1 (by omega)).mp
    (by simpa only [huvalue] using endpoint_lt_cardinal q n hq)
  have hclow : lowCheckCode q c = true := by
    rw [← hu, lowCheckCode_code]
    exact Bool.and_eq_true.mpr ⟨huc, by simpa only [decide_eq_true_eq] using hus⟩
  have hheight := CanonicalHeight.canonicalHeightCode_le_representation q c t hcn.1 htcheck
    (hcvalue.trans hv.symm)
  have htn := Height.admissible_height_le q (n + 1) t ht
  have hupper := hheight.trans htn
  have hlower : ¬ CanonicalHeight.canonicalHeightCode q c ≤ n := by
    intro h
    have hbad := (canonicalHeightCode_le_iff_endpoint q n c hclow).mp h
    rw [hcvalue] at hbad
    exact lt_irrefl _ hbad
  refine ⟨c, hclow, hn.1, hcvalue, ?_⟩
  rw [← CanonicalHeight.canonicalHeightCode_normal q c hn.1]
  omega

theorem endpoint_strictMono (q : Nat) (hq : baseCheck q = true) : StrictMono (endpoint q) := by
  intro n m hnm
  obtain ⟨c, hc, hn, hv, hh⟩ := endpoint_witness q n hq
  have ha := (Comparison.acceptedCode_exact q c).mp hn
  have hbound := (normalCode_height_le_iff_endpoint q m c hc ha.2).mp (by omega)
  simpa only [hv] using hbound

/-- This finite kernel decides comparison with the actual ordinal
endpoint after the semantic endpoint equivalence above has been proved. -/
def belowEndpointCheck (q n c : Nat) : Bool :=
  lowCheckCode q c && decide (CanonicalHeight.canonicalHeightCode q c ≤ n)

theorem belowEndpointCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => belowEndpointCheck p.1.1 p.1.2 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hn := Primrec.snd.comp Primrec.fst
  have hh := CanonicalHeight.canonicalHeightCode_primrec.comp hq Primrec.snd
  exact Primrec.and.comp (lowCheckCode_primrec.comp hq Primrec.snd)
    (Primrec.nat_le.comp hh hn).decide

theorem belowEndpointCheck_exact (q n c : Nat) : belowEndpointCheck q n c = true ↔
    lowCheckCode q c = true ∧ interpretation q c < endpoint q n := by
  simp only [belowEndpointCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_le_iff_endpoint q n c hc).mp hh⟩
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_le_iff_endpoint q n c hc).mpr hh⟩

def exactHeightCheck (q n c : Nat) : Bool :=
  lowCheckCode q c && (CanonicalHeight.canonicalHeightCode q c == n)

theorem exactHeightCheck_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => exactHeightCheck p.1.1 p.1.2 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hn := Primrec.snd.comp Primrec.fst
  exact Primrec.and.comp (lowCheckCode_primrec.comp hq Primrec.snd)
    (Primrec.beq.comp (CanonicalHeight.canonicalHeightCode_primrec.comp hq Primrec.snd) hn)

theorem exactHeightCheck_zero_exact (q c : Nat) : exactHeightCheck q 0 c = true ↔
    lowCheckCode q c = true ∧ interpretation q c < endpoint q 0 := by
  simp only [exactHeightCheck, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_eq_zero_iff_endpoint q c hc).mp hh⟩
  · rintro ⟨hc, hh⟩; exact ⟨hc, (canonicalHeightCode_eq_zero_iff_endpoint q c hc).mpr hh⟩

theorem exactHeightCheck_succ_exact (q n c : Nat) : exactHeightCheck q (n + 1) c = true ↔
    lowCheckCode q c = true ∧ endpoint q n ≤ interpretation q c ∧
      interpretation q c < endpoint q (n + 1) := by
  simp only [exactHeightCheck, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hc, hh⟩
    exact ⟨hc, (canonicalHeightCode_eq_succ_iff_strip q n c hc).mp hh⟩
  · rintro ⟨hc, hh⟩
    exact ⟨hc, (canonicalHeightCode_eq_succ_iff_strip q n c hc).mpr hh⟩

theorem belowEndpointCheck_invariant (q n c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode q d = true) (hv : interpretation q c = interpretation q d) :
    belowEndpointCheck q n c = belowEndpointCheck q n d := by
  apply Bool.eq_iff_iff.mpr
  simp only [belowEndpointCheck_exact, hc, hd, hv]

theorem exactHeightCheck_invariant (q n c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode q d = true) (hv : interpretation q c = interpretation q d) :
    exactHeightCheck q n c = exactHeightCheck q n d := by
  simp only [exactHeightCheck, hc, hd, Bool.true_and,
    CanonicalHeight.canonicalHeightCode_invariant q c d (input_spec q c hc).1
      (input_spec q d hd).1 hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.HeightBoundary
