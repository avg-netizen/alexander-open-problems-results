import Alexander313.Wilken.HereditaryEvaluationOwnCeilingHeight
import Alexander313.Wilken.HereditaryEvaluationInitialHeightPublicAgreement

/-!
# Computed public initial height is monotone along proper mu coverage

Independent canonical epsilon adjacency derives the real OWN checker,
literal search and parsed HIGH root. Actual contextual return supplies
its original source HIGH representative. That representative lies below
the original OWN successor, whose canonical height is bounded by the
original root. Genuine public-code value injection and original height
invariance then compare the independently computed public initial heights.
No return-height estimate, chosen source or next-height oracle is supplied.
Finite-boundary transitions and component LENGTH remain separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialHeightCoveredMonotonicity

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open EvaluationReferenceHeight EvaluationInitialReferenceHeight

theorem adjacency_monotone (gamma beta : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hb : Canonical.check beta = true)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hcover : unionInterpretation beta ≤ publicMuValue gamma) :
    initialHeight beta ≤ initialHeight gamma := by
  have hi := adjacency_caller gamma beta hg hb he hlt hcover
  obtain ⟨d, hd⟩ := PublicMts.search_returns gamma beta hi
  have hn := parsed_high gamma beta d hi hd hlt he
  have hv := (PublicMts.nativeRoot_spec gamma beta d hi hd).2
  have hcut : interpretation gamma (PublicMts.nativeRoot gamma d) <
      PublicMts.ContextSupport.ownCeiling gamma :=
    hv.trans_lt ((PublicMts.inputCheck_exact gamma beta).mp hi).2.2.2.2.2
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · let a := PublicEpsilonSourceDictionary.sourceRootCode gamma
    let next := PublicMts.nativeRoot gamma d
    have ha := PublicMts.ContextSupport.source_one_base gamma hg hl
    have hnext : Mu.inputCheck (SourceOneIota.alphaCode a) next = true := by
      rw [ha.2]; exact hn
    have hbound : interpretation (SourceOneIota.alphaCode a) next <
        SourceOneIota.Enclosure.sourceAlphaPlus a := by
      simpa only [ha.2, PublicMts.ContextSupport.ownCeiling, hl,
        beq_self_eq_true, Bool.cond_true, a, next] using hcut
    have hs := SourceOneIota.SkContextFidelity.sourceRoot_spec a next ha.1 hnext hbound
    have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec
      (SourceOneIota.SkContextFidelity.sourceRoot a next) (SourceOneIota.root_low _ hs.1)
    have hpublic : SourceOneIota.SourceTrackingRaw.Support.publicCode
        (SourceOneIota.SkContextFidelity.sourceRoot a next) = beta :=
      Canonical.check_value_injective _ _ hp.1 hb
        (hp.2.trans (hs.2.1.trans (by rw [ha.2]; exact hv)))
    have hold : SourceOneIota.SourceTrackingRaw.Support.publicCode a = gamma := ha.2
    have hheight := EvaluationOwnCeilingHeight.source_one_inside a
      (SourceOneIota.SkContextFidelity.sourceRoot a next) ha.1 hs.1
      (hs.2.1.trans_lt hbound)
    rw [← EvaluationInitialHeightPublicAgreement.source_one _ hs.1,
      ← EvaluationInitialHeightPublicAgreement.source_one a ha.1,
      hpublic, hold] at hheight
    exact hheight
  · let s := PublicEpsilonSourceDictionary.sourceIndex gamma
    let q := MuPublicDictionary.Support.nativeContext gamma
    let a := MuPublicDictionary.Support.nativeRoot gamma
    let next := PublicMts.nativeRoot gamma d
    have ha := PublicMts.ContextSupport.positive_base gamma hg hl
    have hnext : Mu.inputCheck (betaCode q a) next = true := by rw [ha.2]; exact hn
    have hbound : interpretation (betaCode q a) next < Enclosure.sourceAlphaPlus q a := by
      have hz := beq_eq_false_iff_ne.mpr hl
      simpa only [ha.2, PublicMts.ContextSupport.ownCeiling, hz, Bool.cond_false,
        q, a, next] using hcut
    have hs := ContextTranslation.Return.returnedRoot_spec q a next ha.1 hnext
    have hp := UniformPublicReturn.publicCode_spec q (ContextTranslation.Return.returnedRoot q a next)
      ((UniformPublicReturn.inputCheck_exact _ _).mpr (RootLowCollapse.root_low _ _ hs.1))
    have hpublic : UniformPublicReturn.publicCode q (ContextTranslation.Return.returnedRoot q a next) = beta :=
      Canonical.check_value_injective _ _ hp.1 hb
        (hp.2.trans (hs.2.trans (by rw [ha.2]; exact hv)))
    have hold : UniformPublicReturn.publicCode q a = gamma := ha.2
    have hheight := EvaluationOwnCeilingHeight.positive_inside q a
      (ContextTranslation.Return.returnedRoot q a next) ha.1 hs.1 (hs.2.trans_lt hbound)
    rw [← EvaluationInitialHeightPublicAgreement.positive s _ hs.1,
      ← EvaluationInitialHeightPublicAgreement.positive s a ha.1,
      hpublic, hold] at hheight
    exact hheight

/-- Genuine independent public references propagate the computed bound
to every later entry; no list of chosen heights is an input. -/
theorem reference_height_bound (gamma : Nat) (rest : List Nat)
    (hr : PublicTrackingSequences.Reference (gamma :: rest)) :
    ∀ beta ∈ gamma :: rest, initialHeight beta ≤ initialHeight gamma := by
  induction rest generalizing gamma with
  | nil =>
    intro beta hb
    have he : beta = gamma := List.mem_singleton.mp hb
    subst beta
    exact le_rfl
  | cons next rest ih =>
    cases hr with
    | cons gamma next rest hg hlt hcover ht =>
      have hs := ht.epsilons next List.mem_cons_self
      have hc : unionInterpretation next ≤ publicMuValue gamma := by
        simpa only [publicMuValue, SkPublicRecurrence.muValue] using hcover
      have hm := adjacency_monotone gamma next hg hs.1 hs.2.1 hlt hc
      intro beta hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_rfl
      · exact (ih next ht beta hb).trans hm

theorem global_tail_height_bound (m gamma : Nat) (rest : List Nat)
    (hr : GlobalTrackingSequences.EpsilonReference (gamma :: rest))
    (hg : GlobalTrackingSequences.TailGap m (gamma :: rest)) :
    ∀ beta ∈ gamma :: rest, initialHeight beta ≤ initialHeight gamma :=
  reference_height_bound gamma rest
    (GlobalTrackingSequences.SmallHSupport.epsilonReference_in_gap m _ hr hg).1

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationInitialHeightCoveredMonotonicity
