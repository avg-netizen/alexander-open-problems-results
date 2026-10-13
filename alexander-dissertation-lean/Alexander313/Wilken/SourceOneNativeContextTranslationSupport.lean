import Alexander313.Wilken.SourceOneNativeMuBounds
import Alexander313.Wilken.SourceOneNativeBoundedContextMuTranslation
import Alexander313.Wilken.PublicEpsilonNativeContextTranslationSupport
import Alexander313.Wilken.HereditaryAddition

/-!
# Genuine original-source-one contextual translation callers

The original checker remains check zero. Actual source addition and the
real theta checker construct the ORIGINAL alpha-plus comparison code.
The genuine alpha-context enclosure licenses LOW coverage above alpha.
The dictionary's selected endpoint is PROVED equal to the ORIGINAL
source-one endpoint, so the constructed target high root has its actual
old generic mu caller without an added selected-endpoint premise. Native
operations occur only at the genuine epsilon alphaCode, never base one.
Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.ContextTranslation.Support

open ThetaCourse

def sourceSuccessorCode (alpha : Nat) : Nat := BoundedPublicReturn.nodeCode 0
  (Addition.normalizedSumCode 0 (OmegaQuotient.argumentCode alpha) OmegaQuotient.unitTerm.code)

theorem sourceSuccessorCode_primrec : Primrec sourceSuccessorCode :=
  BoundedPublicReturn.nodeCode_primrec.comp (Primrec.const 0)
    (Addition.normalizedSumCode_primrec.comp ((Primrec.const 0).pair
      (OmegaQuotient.argumentCode_primrec.pair (Primrec.const OmegaQuotient.unitTerm.code))))

theorem sourceSuccessorCode_spec (alpha : Nat) (ha : rootCheck alpha = true) :
    Theta.acceptedCode 0 (sourceSuccessorCode alpha) = true ∧
      interpretation 0 (sourceSuccessorCode alpha) = Enclosure.sourceAlphaPlus alpha := by
  have hc := (Theta.acceptedCode_iff 0 _).mp (OmegaQuotient.argument_accepted alpha ha)
  have hu : checkCode 0 OmegaQuotient.unitTerm.code = true := by
    simpa only [checkCode_code] using OmegaQuotient.unitTerm_spec.1
  have hs := Addition.normalizedSumCode_checked 0 (OmegaQuotient.argumentCode alpha)
    OmegaQuotient.unitTerm.code hc.1 hu
  have hv : interpretation 0
      (Addition.normalizedSumCode 0 (OmegaQuotient.argumentCode alpha) OmegaQuotient.unitTerm.code) =
        interpretation 0 (OmegaQuotient.argumentCode alpha) + 1 := by
    simpa only [interpretation_code, OmegaQuotient.unitTerm_spec.2.2] using hs.2
  have hsort : interpretation 0
      (Addition.normalizedSumCode 0 (OmegaQuotient.argumentCode alpha) OmegaQuotient.unitTerm.code) <
        omegaSequence (finiteBase 0) (0 + 2) := by
    rw [hv]
    exact (Mu.Bounds.source_successor_argument_spec alpha ha).2.1
  have ht := BoundedPublicReturn.nodeCode_spec 0 _ hs.1 hsort
  refine ⟨ht.1, ?_⟩
  simpa only [sourceSuccessorCode, hv, Enclosure.sourceAlphaPlus, Lambda.argumentCode] using ht.2

/-- Actual target-boundary coverage and the genuine source-one selected
endpoint identity supply the COMPLETE target mu root caller. -/
theorem target_root_exists (alpha beta : Nat) (ha : rootCheck alpha = true)
    (hb : rootCheck beta = true) (hp : interpretation 0 alpha < interpretation 0 beta)
    (hu : interpretation 0 beta < Enclosure.sourceAlphaPlus alpha) :
    ∃ d, NativeContext.PublicEpsilonIota.rootCheck (alphaCode alpha) d = true ∧
      NativeContext.interpretation (alphaCode alpha) d = interpretation 0 beta := by
  have hs := Enclosure.delta_enclosure_spec alpha ha
  have hlow : NativeContext.lowCheckCode (alphaCode alpha) (Enclosure.deltaEnclosureTerm alpha).code = true := by
    simp only [NativeContext.lowCheckCode_code, NativeContext.lowCheck, hs.1,
      Enclosure.deltaEnclosureTerm, RelativeTerm.outerSort, decide_true, Bool.true_and]
  have hboundary := NativeContext.checked_low_bound (alphaCode alpha) _ hlow
  rw [NativeContext.interpretation_code, Enclosure.delta_enclosure_eq_sourceAlphaPlus alpha ha] at hboundary
  obtain ⟨d, hd, hv⟩ := NativeContext.ContextTranslation.Support.root_exists_of_boundary
    (alphaCode alpha) (alphaCode_baseCheck alpha ha) (interpretation 0 beta)
    (by rw [OrderSupport.alpha_base alpha ha]; exact hp) (root_epsilon beta hb) (hu.trans hboundary)
  obtain ⟨t, he, ht, hn, hh⟩ := (NativeContext.RootLowCollapse.rootCheck_exact _ d).mp hd
  have hc := BoundedContextReturn.intermediate_root_caller alpha ha t ht hn hh
    (by simpa only [he, NativeContext.interpretation_code, hv] using hu)
  exact ⟨d, by simpa only [← he] using hc, hv⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.ContextTranslation.Support
