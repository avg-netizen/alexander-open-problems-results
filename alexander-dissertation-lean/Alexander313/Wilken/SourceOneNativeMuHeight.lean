import Alexander313.Wilken.SourceOneNativeMuHeightSupport

/-!
# Source Lemma 3.7 height inequalities at the original base one

Actual finite-tail and omega-power producers bound mu height by the genuine
iota coefficient height. The derived coefficient-versus-lambda comparison
then gives ht_alpha(mu) <= ht_alpha(lambda) < ht_one(original root).
The actual raw lambda executes the original normalizer and lambda on the
same genuine raw epsilon-root guard as mu; its proved original value-height
invariance retains the ORIGINAL raw root bound. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.Height

theorem muCode_height_le_lambda (a out : Nat) (ho : out ∈ Lambda.execute a) :
    heightCode (muCode a) ≤ NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) out := by
  have ha := (Lambda.execute_spec a out ho).1
  exact (muCode_height_mappedCoefficient a ha).trans
    (HeightSupport.mappedCoefficient_canonical_height_le_lambda a out ho)

theorem muCode_canonical_height_le_lambda (a out : Nat) (ho : out ∈ Lambda.execute a) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) (muCode a) ≤
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) out := by
  rw [NativeContext.CanonicalHeight.canonicalHeightCode_normal _ _
    (muCode_spec a (Lambda.execute_spec a out ho).1).2.1]
  exact muCode_height_le_lambda a out ho

theorem source_lemma_3_7_height (a mout lout : Nat)
    (hm : mout ∈ execute a) (hl : lout ∈ Lambda.execute a) :
    NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) mout ≤
        NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) lout ∧
      NativeContext.CanonicalHeight.canonicalHeightCode (alphaCode a) lout <
        SourceOne.CanonicalHeight.canonicalHeightCode a := by
  obtain ⟨ha, rfl⟩ := (execute_graph a mout).mp hm
  exact ⟨muCode_canonical_height_le_lambda a lout hl, Lambda.source_lemma_2_48_c a lout hl⟩

theorem source_lemma_3_7_normal_height (a mout lout : Nat)
    (hm : mout ∈ execute a) (hl : lout ∈ Lambda.execute a) :
    heightCode mout ≤ heightCode lout ∧ heightCode lout < heightCode a := by
  have hs := source_lemma_3_7_height a mout lout hm hl
  have hm' := execute_spec a mout hm
  have hl' := Lambda.execute_spec a lout hl
  simpa only [NativeContext.CanonicalHeight.canonicalHeightCode_normal _ mout hm'.2.2.1,
    NativeContext.CanonicalHeight.canonicalHeightCode_normal _ lout hl'.2.1,
    SourceOne.CanonicalHeight.canonicalHeightCode_normal _
      (SourceOneIota.HeightSupport.root_source_accepted a hl'.1)] using hs

namespace Raw

theorem muCode_height_le_lambda (a out : Nat) (ha : Mu.Raw.inputCheck a = true)
    (ho : out ∈ Lambda.Raw.execute a) :
    heightCode (Mu.Raw.muCode a) ≤
      NativeContext.CanonicalHeight.canonicalHeightCode (Mu.Raw.outputContext a) out := by
  have hl := (Lambda.Raw.execute_graph a out).mp ho
  simpa only [Mu.Raw.muCode, ha, Bool.cond_true, Mu.Raw.outputContext] using
    Height.muCode_height_le_lambda (Mu.Raw.normalizedRoot a) out hl.2

theorem source_lemma_3_7_height (a mout lout : Nat)
    (hm : mout ∈ Mu.Raw.execute a) (hl : lout ∈ Lambda.Raw.execute a) :
    NativeContext.CanonicalHeight.canonicalHeightCode (Mu.Raw.outputContext a) mout ≤
        NativeContext.CanonicalHeight.canonicalHeightCode (Mu.Raw.outputContext a) lout ∧
      NativeContext.CanonicalHeight.canonicalHeightCode (Mu.Raw.outputContext a) lout <
        SourceOne.CanonicalHeight.canonicalHeightCode a := by
  have hm' := Mu.Raw.execute_spec a mout hm
  refine ⟨?_, ?_⟩
  · rw [NativeContext.CanonicalHeight.canonicalHeightCode_normal _ _ hm'.2.2.1]
    obtain ⟨ha, rfl⟩ := (Mu.Raw.execute_graph a mout).mp hm
    exact muCode_height_le_lambda a lout ha hl
  · exact Lambda.Raw.source_lemma_2_48_c a lout hl

end Raw
end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.Height
