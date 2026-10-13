import Alexander313.Wilken.HereditaryPublicMtsInfinitySupport
import Alexander313.Wilken.HereditaryEvaluationReferenceHeight
import Alexander313.Wilken.PublicEpsilonNativeTrackingEndpointSupport
import Alexander313.Wilken.SourceOneNativeTrackingEndpointSupport

/-!
# Genuine public OWN nesting inside one selected original source

The real full boundary and finite least-source scan force every canonical
value in an original OWN interval to have the same source level. The two
selected original HIGH roots therefore enter the actual same-source
endpoint-nesting theorem directly. No incoming-context mu identity outside
OWN or supplied returned representative is used. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ReachBoundSupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota

/-- The original root is strictly below its genuinely computed successor. -/
theorem root_lt_own (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    unionInterpretation gamma < ContextSupport.ownCeiling gamma := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have ha := MuPublicDictionary.Support.source_one_root gamma hg hl
    have hb := (SourceOneIota.Enclosure.delta_enclosure_spec _ ha.1).2.2.2
    rw [SourceOneIota.Enclosure.delta_enclosure_eq_sourceAlphaPlus _ ha.1, ha.2] at hb
    simpa only [ContextSupport.ownCeiling, hl, beq_self_eq_true, Bool.cond_true] using hb
  · have ha := MuPublicDictionary.Support.native_root gamma hg hl
    have hb := Enclosure.root_lt_enclosure _ _ ha.1
    rw [Enclosure.delta_enclosure_value _ _ ha.1, ha.2] at hb
    simpa only [ContextSupport.ownCeiling, beq_eq_false_iff_ne.mpr hl, Bool.cond_false] using hb

/-- The actual failed finite endpoint tests give source equality within
OWN; the input may be any canonical value there. -/
theorem level_eq_of_own_interval (gamma beta : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hb : Canonical.check beta = true)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hcut : unionInterpretation beta < ContextSupport.ownCeiling gamma) :
    PublicEpsilonSourceDictionary.level beta = PublicEpsilonSourceDictionary.level gamma := by
  have hs := (MuPublicDictionary.Support.inputCheck_exact gamma).mp hg
  have hfloor := PublicEpsilonSourceDictionary.proper_lower gamma hs.1 hs.2
  have hbound := hcut.trans (ContextSupport.ownCeiling_boundary gamma hg)
  rw [InfinitySupport.public_boundary_eq gamma hg] at hbound
  have hgap : GlobalTrackingSequences.TailGap (PublicEpsilonSourceDictionary.level gamma) [beta] := by
    change sourceUpsilon (PublicEpsilonSourceDictionary.level gamma : Ordinal.{0}) <
        unionInterpretation beta ∧ unionInterpretation beta <
      sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0})
    rw [PublicUpsilonSegment.successor_value]
    refine ⟨?_, hbound⟩
    cases hl : PublicEpsilonSourceDictionary.level gamma with
    | zero =>
      rw [Nat.cast_zero, sourceUpsilon_zero]
      exact (EpsilonOffsets.epsilon_pos_principal
        ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).2.1).1.trans hlt
    | succ m =>
      simpa only [hl, PublicUpsilonSegment.successor_value] using hfloor.trans hlt
  exact GlobalTrackingSequences.SmallHSupport.level_eq_of_gap _ beta hb hgap

/-- Independently selected genuine original roots prove strict public
successor nesting on every actual OWN interval. -/
theorem own_nested (gamma beta : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hcut : unionInterpretation beta < ContextSupport.ownCeiling gamma) :
    ContextSupport.ownCeiling beta < ContextSupport.ownCeiling gamma := by
  have hlevel := level_eq_of_own_interval gamma beta hg
    ((MuPublicDictionary.Support.inputCheck_image beta).mp hb).1 hlt hcut
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have hlb := hlevel.trans hl
    have ha := MuPublicDictionary.Support.source_one_root gamma hg hl
    have hd := MuPublicDictionary.Support.source_one_root beta hb hlb
    have hp : Hereditary.interpretation 0 (PublicEpsilonSourceDictionary.sourceRootCode gamma) <
        Hereditary.interpretation 0 (PublicEpsilonSourceDictionary.sourceRootCode beta) := by
      rw [ha.2, hd.2]
      exact hlt
    have hc : Hereditary.interpretation 0 (PublicEpsilonSourceDictionary.sourceRootCode beta) <
        SourceOneIota.Enclosure.sourceAlphaPlus (PublicEpsilonSourceDictionary.sourceRootCode gamma) := by
      simpa only [hd.2, ContextSupport.ownCeiling, hl, beq_self_eq_true, Bool.cond_true] using hcut
    have he := SourceOneIota.SourceAdditiveTracking.EndpointSupport.endpoint_nested _ _
      ha.1 hd.1 hp hc
    simpa only [ContextSupport.ownCeiling, hl, hlb, beq_self_eq_true, Bool.cond_true] using he
  · have hlb : PublicEpsilonSourceDictionary.level beta ≠ 0 := by rw [hlevel]; exact hl
    have ha := MuPublicDictionary.Support.native_root gamma hg hl
    have hd := MuPublicDictionary.Support.native_root beta hb hlb
    have hq : MuPublicDictionary.Support.nativeContext beta =
        MuPublicDictionary.Support.nativeContext gamma := by
      simp only [MuPublicDictionary.Support.nativeContext, PublicEpsilonSourceDictionary.sourceIndex, hlevel]
    have hr : Mu.inputCheck (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot beta) = true := by simpa only [hq] using hd.1
    have hv : interpretation (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot beta) = unionInterpretation beta := by
      simpa only [hq] using hd.2
    have hp : interpretation (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot gamma) <
      interpretation (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot beta) := by rw [ha.2, hv]; exact hlt
    have hc : interpretation (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot beta) <
      Enclosure.sourceAlphaPlus (MuPublicDictionary.Support.nativeContext gamma)
        (MuPublicDictionary.Support.nativeRoot gamma) := by
      simpa only [hv, ContextSupport.ownCeiling, beq_eq_false_iff_ne.mpr hl, Bool.cond_false] using hcut
    have he := SourceAdditiveTracking.EndpointSupport.endpoint_nested _ _ _ ha.1 hr hp hc
    simpa only [ContextSupport.ownCeiling, beq_eq_false_iff_ne.mpr hl,
      beq_eq_false_iff_ne.mpr hlb, Bool.cond_false, hq] using he

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ReachBoundSupport
