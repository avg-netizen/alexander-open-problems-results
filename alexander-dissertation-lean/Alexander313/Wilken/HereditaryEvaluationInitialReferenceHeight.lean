import Alexander313.Wilken.HereditaryEvaluationReferenceCardinality
import Alexander313.Wilken.SourceOneNativeMuHeight
import Alexander313.Wilken.PublicEpsilonNativeMuBaseValueInvariance
import Alexander313.Wilken.HereditaryEvaluationComponents

/-!
# The genuine first-source height bounds the whole proper reference

The real source dictionary computes the original checked Normal root of
the first proper epsilon, at source one or its genuine selected positive
endpoint. Its literal root height is the canonical source value-height.
The true public mu definition, actual changed base, and original mu height
theorems derive the strict bound on the next independently searched height.
All later calls then bound the entire reference length. A global tail's
true gap derives both proper admission and the printed initial endpoint.
This proves the component COUNT bound of Definition3.35; it does not yet
bound each component LENGTH or prove recursive lSeq descent. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialReferenceHeight

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open EvaluationReferenceHeight

def initialHeight (gamma : Nat) : Nat := cond (PublicEpsilonSourceDictionary.level gamma == 0)
  (heightCode (PublicEpsilonSourceDictionary.sourceRootCode gamma))
  (heightCode (MuPublicDictionary.Support.nativeRoot gamma))

theorem initialHeight_primrec : Primrec initialHeight :=
  (Primrec.beq.comp PublicEpsilonSourceDictionary.level_primrec (Primrec.const 0)).cond
    (heightCode_primrec.comp PublicEpsilonSourceDictionary.sourceRootCode_primrec)
    (heightCode_primrec.comp MuPublicDictionary.Support.nativeRoot_primrec)

theorem initialHeight_positive (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true) : 0 < initialHeight gamma := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have hr := (MuPublicDictionary.Support.source_one_root gamma hg hl).1
    obtain ⟨t, ht, _, _, _⟩ := (SourceOneIota.rootCheck_exact _).mp hr
    simp only [initialHeight, hl, beq_self_eq_true, Bool.cond_true, ht,
      RelativeTerm.heightCode_code, RelativeTerm.height]
    exact Nat.zero_lt_one.trans_le (le_max_left _ _)
  · have hr := (MuPublicDictionary.Support.native_root gamma hg hl).1
    obtain ⟨t, ht, _, _, _⟩ := (rootCheck_exact _ _).mp hr
    have hz := beq_eq_false_iff_ne.mpr hl
    simp only [initialHeight, hz, Bool.cond_false, ht,
      RelativeTerm.heightCode_code, RelativeTerm.height]
    exact Nat.zero_lt_one.trans_le (le_max_left _ _)

/-- The first strict decrease is derived from the ACTUAL selected original
source root. The next height is the result of the actual literal-base LOW
search, and independent public mu supplies its only value bound. -/
theorem next_height_lt_initial (gamma beta height : Nat)
    (hh : height ∈ execute gamma beta)
    (hcover : unionInterpretation beta ≤ publicMuValue gamma) : height < initialHeight gamma := by
  obtain ⟨hi, d, hd, hheight⟩ := (execute_graph gamma beta height).mp hh
  have hg := ((PublicMts.inputCheck_exact gamma beta).mp hi).1
  have hcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
  have hs := SkNextSearch.Support.search_spec gamma beta d hd
  have hpublic := (MuPublicDictionary.publicCode_spec gamma hg).2
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · let root := PublicEpsilonSourceDictionary.sourceRootCode gamma
    have hr := MuPublicDictionary.Support.source_one_root gamma hg hl
    have hp := SourceOneIota.alphaCode_spec root hr.1
    have hbase : SourceOneIota.alphaCode root = gamma :=
      Canonical.check_value_injective _ _ hp.1 hcanon (hp.2.trans hr.2)
    have hmu : publicMuValue gamma = SourceOneIota.Mu.sourceValue root := by
      simpa only [publicMuValue, hpublic, MuPublicDictionary.Support.sourceValue,
        hl, beq_self_eq_true, Bool.cond_true, root]
    have hlow : lowCheckCode (SourceOneIota.alphaCode root) d = true := by rw [hbase]; exact hs.1
    have hm := SourceOneIota.Mu.muCode_spec root hr.1
    have hbound : interpretation (SourceOneIota.alphaCode root) d ≤
        interpretation (SourceOneIota.alphaCode root) (SourceOneIota.Mu.muCode root) := by
      rw [hm.2.2, hbase, hs.2.2.2, ← hmu]
      exact hcover
    have hmono := NativeContext.Mu.HeightSupport.canonicalHeightCode_mono_low _ _ _ hlow hm.1 hbound
    obtain ⟨lambda, hlambda⟩ := SourceOneIota.Lambda.execute_returns root hr.1
    have hdesc := (hmono.trans
      (SourceOneIota.Mu.Height.muCode_canonical_height_le_lambda root lambda hlambda)).trans_lt
      (SourceOneIota.Lambda.source_lemma_2_48_c root lambda hlambda)
    rw [hbase, ← hheight, SourceOne.CanonicalHeight.canonicalHeightCode_normal _
      (SourceOneIota.HeightSupport.root_source_accepted root hr.1)] at hdesc
    simpa only [initialHeight, hl, beq_self_eq_true, Bool.cond_true, root] using hdesc
  · let q := MuPublicDictionary.Support.nativeContext gamma
    let root := MuPublicDictionary.Support.nativeRoot gamma
    have hr := MuPublicDictionary.Support.native_root gamma hg hl
    have hp := betaCode_spec q root hr.1
    have hbase : betaCode q root = gamma :=
      Canonical.check_value_injective _ _ hp.1 hcanon (hp.2.trans hr.2)
    have hz := beq_eq_false_iff_ne.mpr hl
    have hmu : publicMuValue gamma = Mu.sourceValue q root := by
      simpa only [publicMuValue, hpublic, MuPublicDictionary.Support.sourceValue,
        hz, Bool.cond_false, q, root]
    have hbound : interpretation (betaCode q root) d ≤ Mu.sourceValue q root := by
      rw [hbase, hs.2.2.2, ← hmu]
      exact hcover
    have hdesc := SkHeight.low_next_height_lt_root q root d hr.1
      (by rw [hbase]; exact hs.1) hbound
    rw [hbase, ← hheight, CanonicalHeight.canonicalHeightCode_normal q root
      (RootLowCollapse.root_accepted q root hr.1)] at hdesc
    simpa only [initialHeight, hz, Bool.cond_false, root] using hdesc

/-- Independent proper Reference alone bounds its whole cardinality by
the genuine canonical height at the first selected ORIGINAL source. -/
theorem reference_length_le (gamma : Nat) (rest : List Nat)
    (hr : PublicTrackingSequences.Reference (gamma :: rest)) :
    (gamma :: rest).length ≤ initialHeight gamma := by
  cases rest with
  | nil =>
    simpa only [List.length_singleton] using
      Nat.succ_le_of_lt (initialHeight_positive gamma (hr.nodes gamma List.mem_cons_self))
  | cons beta rest =>
    cases hr with
    | cons gamma beta rest hgamma hlt hcover ht =>
      obtain ⟨height, hh, hb⟩ := EvaluationReferenceCardinality.reference_returns_bound gamma beta rest
        (.cons gamma beta rest hgamma hlt hcover ht)
      have hc : unionInterpretation beta ≤ publicMuValue gamma := by
        simpa only [publicMuValue, SkPublicRecurrence.muValue] using hcover
      have hd := next_height_lt_initial gamma beta height hh hc
      simp only [List.length_cons] at hb ⊢
      omega

/-- At the actual initial base one, the original checked Normal root has
exactly the genuine original source-one canonical value-height. -/
theorem initialHeight_at_one (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    initialHeight gamma = SourceOne.CanonicalHeight.canonicalHeightCode
      (PublicEpsilonSourceDictionary.sourceRootCode gamma) := by
  have hr := (MuPublicDictionary.Support.source_one_root gamma hg hl).1
  rw [SourceOne.CanonicalHeight.canonicalHeightCode_normal _
    (SourceOneIota.HeightSupport.root_source_accepted _ hr)]
  simp only [initialHeight, hl, beq_self_eq_true, Bool.cond_true]

/-- At a positive actual initial endpoint, the selected original Normal
root is admitted at the literal endpoint with exactly the same height. -/
theorem initialHeight_at_endpoint (m gamma : Nat) (hm : 0 < m)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = m) :
    initialHeight gamma = CanonicalHeight.canonicalHeightCode
      (GlobalTrackingSequences.endpointCode m) (MuPublicDictionary.Support.nativeRoot gamma) := by
  have hn : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by omega
  have hr := (MuPublicDictionary.Support.native_root gamma hg hn).1
  have he : base (MuPublicDictionary.Support.nativeContext gamma) =
      base (GlobalTrackingSequences.endpointCode m) := by
    change base (NativePublicBridge.contextCode (PublicEpsilonSourceDictionary.sourceIndex gamma)) =
      unionInterpretation (GlobalTrackingSequences.endpointCode m)
    rw [NativePublicBridge.contextCode_value, PublicEpsilonSourceDictionary.endpointCode_value]
    congr 1
    simp only [PublicEpsilonSourceDictionary.sourceIndex, hl]
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hc := MuCoveredRelativeAssignment.Support.base_caller _ (GlobalMuDictionary.Support.endpoint_input n)
  have ht := Mu.BaseValueInvariance.root_caller _ _ _ hr hc he
  rw [CanonicalHeight.canonicalHeightCode_normal _ _ (RootLowCollapse.root_accepted _ _ ht)]
  simp only [initialHeight, beq_eq_false_iff_ne.mpr hn, Bool.cond_false]

/-- The actual global gap computes the true initial source and derives
the full n+1 component COUNT bound in h=ht_initial(alpha1)+1. -/
theorem global_component_count_le (m gamma : Nat) (rest : List Nat)
    (hr : GlobalTrackingSequences.EpsilonReference (gamma :: rest))
    (hg : GlobalTrackingSequences.TailGap m (gamma :: rest)) :
    (gamma :: rest).length + 1 ≤ initialHeight gamma + 1 := by
  have hp := (GlobalTrackingSequences.SmallHSupport.epsilonReference_in_gap m _ hr hg).1
  exact Nat.add_le_add_right (reference_length_le gamma rest hp) 1

/-- An actual full component execution has at most the printed h entries
when its actually computed proper tail is nonempty. The numerical segment,
its strict gap and every proper caller are derived from its exact graph. -/
theorem execute_count_le_initial (codes : List Nat) (out : List EvaluationBlocks.Block)
    (ho : out ∈ EvaluationComponents.execute codes) (gamma : Nat) (rest : List Nat)
    (ht : EvaluationComponents.Support.properTail codes = gamma :: rest) :
    out.length ≤ initialHeight gamma + 1 := by
  have hs := EvaluationComponents.Support.tracking_segment codes
    ((EvaluationComponents.execute_graph codes out).mp ho).1
  rw [ht] at hs
  have hb := global_component_count_le _ gamma rest hs.2.1 hs.2.2
  rw [EvaluationComponents.execute_count codes out ho, ht]
  exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialReferenceHeight
