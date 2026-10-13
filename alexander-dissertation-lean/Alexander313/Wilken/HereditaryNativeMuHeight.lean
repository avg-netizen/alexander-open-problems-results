import Alexander313.Wilken.HereditaryNativeMuHeightSupport

/-!
# The actual height inequalities in source Lemma 3.7

The genuine mu producer's finite-tail and omega-power height bounds combine
with the derived actual coefficient-versus-lambda comparison. The already
proved executing lambda height then supplies the strict original-root bound.
Both heights use their literal actual bases. Original raw epsilon roots are
included through the real normalizer and its proved canonical-height
invariance. No height, output-admission or normalized-domain oracle occurs.
Only the height clauses of Lemma 3.7 are claimed here. Uncompiled sources.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.Height

open NativePublicBridge (contextCode)
open HeightSupport

theorem muCode_height_le_lambda (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    heightCode (muCode s a) ≤ CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) out := by
  have ha := (Lambda.execute_spec s a out ho).1
  exact (muCode_height_mappedCoefficient s a ha).trans
    (mappedCoefficient_canonical_height_le_lambda s a out ho)

theorem muCode_canonical_height_le_lambda (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) (muCode s a) ≤
      CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) out := by
  rw [CanonicalHeight.canonicalHeightCode_normal _ _
    (muCode_spec s a (Lambda.execute_spec s a out ho).1).2.1]
  exact muCode_height_le_lambda s a out ho

/-- The two genuine canonical heights use their actual different bases,
exactly as printed: ht_alpha(mu_tau_alpha)<=ht_alpha(lambda_tau_alpha)
and ht_alpha(lambda_tau_alpha)<ht_tau(alpha). -/
theorem source_lemma_3_7_height (s a mout lout : Nat)
    (hm : mout ∈ execute s a) (hl : lout ∈ Lambda.execute s a) :
    CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) mout ≤
        CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) lout ∧
      CanonicalHeight.canonicalHeightCode (Iota.alphaCode s a) lout <
        CanonicalHeight.canonicalHeightCode (contextCode s) a := by
  obtain ⟨ha, rfl⟩ := (execute_graph s a mout).mp hm
  exact ⟨muCode_canonical_height_le_lambda s a lout hl,
    Lambda.Height.execute_canonical_height_lt_root s a lout hl⟩

/-- Actual Normal output/root height is the corresponding canonical height,
so the same printed inequalities hold for the literal executing codes. -/
theorem source_lemma_3_7_normal_height (s a mout lout : Nat)
    (hm : mout ∈ execute s a) (hl : lout ∈ Lambda.execute s a) :
    heightCode mout ≤ heightCode lout ∧ heightCode lout < heightCode a := by
  have hs := source_lemma_3_7_height s a mout lout hm hl
  have hm' := execute_spec s a mout hm
  have hl' := Lambda.execute_spec s a lout hl
  simpa only [CanonicalHeight.canonicalHeightCode_normal _ mout hm'.2.2.1,
    CanonicalHeight.canonicalHeightCode_normal _ lout hl'.2.1,
    CanonicalHeight.canonicalHeightCode_normal _ a
      (Iota.HeightSupport.root_accepted s a hl'.1)] using hs

private theorem raw_lambda_high (s a out : Nat) (ha : Raw.inputCheck s a = true)
    (ho : out ∈ Lambda.Branches.Raw.execute s a) :
    out ∈ Lambda.execute s (Raw.normalizedRoot s a) := by
  have hs := Bool.and_eq_true.mp ha
  have hb : out ∈ Lambda.Branches.execute s (Raw.normalizedRoot s a) := by
    simpa only [Lambda.Branches.Raw.execute, hs.1, Bool.cond_true] using ho
  simpa only [Lambda.Branches.execute, (Bool.and_eq_true.mp hs.1).2,
    hs.2, Bool.cond_true] using hb

theorem raw_muCode_height_le_lambda (s a out : Nat) (ha : Raw.inputCheck s a = true)
    (ho : out ∈ Lambda.Branches.Raw.execute s a) :
    heightCode (Raw.muCode s a) ≤
      CanonicalHeight.canonicalHeightCode (Raw.outputContext s a) out := by
  have hl := raw_lambda_high s a out ha ho
  simpa only [Raw.muCode, ha, Bool.cond_true, Raw.outputContext] using
    muCode_height_le_lambda s (Raw.normalizedRoot s a) out hl

/-- Both original raw execution domains are genuine source guards. The
strict right bound is the canonical height of the ORIGINAL raw root. -/
theorem source_lemma_3_7_raw_height (s a mout lout : Nat)
    (hm : mout ∈ Raw.execute s a) (hl : lout ∈ Lambda.Branches.Raw.execute s a) :
    CanonicalHeight.canonicalHeightCode (Raw.outputContext s a) mout ≤
        CanonicalHeight.canonicalHeightCode (Raw.outputContext s a) lout ∧
      CanonicalHeight.canonicalHeightCode (Raw.outputContext s a) lout <
        CanonicalHeight.canonicalHeightCode (contextCode s) a := by
  have hm' := Raw.execute_spec s a mout hm
  have hs := Bool.and_eq_true.mp hm'.1
  have hl' := raw_lambda_high s a lout hm'.1 hl
  have hc : checkCode (contextCode s) a = true :=
    (Bool.and_eq_true.mp (Bool.and_eq_true.mp hs.1).1).1
  have hn := Normalization.normalizeCode_accepted (contextCode s) a hc
  have hheight : CanonicalHeight.canonicalHeightCode (contextCode s) (Raw.normalizedRoot s a) =
      CanonicalHeight.canonicalHeightCode (contextCode s) a :=
    CanonicalHeight.canonicalHeightCode_invariant _ _ _
      ((Comparison.acceptedCode_exact _ _).mp hn.1).1 hc hn.2
  refine ⟨?_, ?_⟩
  · rw [CanonicalHeight.canonicalHeightCode_normal _ _ hm'.2.2.1]
    obtain ⟨ha, rfl⟩ := (Raw.execute_graph s a mout).mp hm
    exact raw_muCode_height_le_lambda s a lout ha hl
  · simpa only [Raw.outputContext, hheight] using
      Lambda.Height.execute_canonical_height_lt_root s (Raw.normalizedRoot s a) lout hl'

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Mu.Height
