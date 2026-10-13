import Alexander313.Wilken.HereditaryMuCoveredRelativePublicFidelitySupport
import Alexander313.Wilken.PublicEpsilonNativeContextTranslation
import Alexander313.Wilken.SourceOneNativeContextTranslationSupport

/-!
# Executed OWN interval and original mu columns for public localization

The selected proper public epsilon has an actual original source root.
Its original successor code computes a canonical OWN alpha-plus ceiling.
The genuine native enclosure proves that ceiling lies below the actual
native grammar boundary. Every HIGH localization entry below this computed
ceiling therefore enters the existing contextual-return theorem in its
original source, before independent public mu is identified. No arbitrary
RAW or value-only cross-context mu equality is asserted. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ContextSupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota

def sourceOneCeiling (gamma : Nat) : Nat :=
  SourceOneIota.SourceTrackingRaw.Support.publicCode
    (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode
      (PublicEpsilonSourceDictionary.sourceRootCode gamma))

def positiveCeiling (gamma : Nat) : Nat :=
  UniformPublicReturn.publicCode (MuPublicDictionary.Support.nativeContext gamma)
    (ContextTranslation.sourceSuccessorCode (MuPublicDictionary.Support.nativeContext gamma)
      (MuPublicDictionary.Support.nativeRoot gamma))

def ceilingCode (gamma : Nat) : Nat := cond (PublicEpsilonSourceDictionary.level gamma == 0)
  (sourceOneCeiling gamma) (positiveCeiling gamma)

theorem sourceOneCeiling_primrec : Primrec sourceOneCeiling :=
  SourceOneIota.SourceTrackingRaw.Support.publicCode_primrec.comp
    (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode_primrec.comp
      PublicEpsilonSourceDictionary.sourceRootCode_primrec)

theorem positiveCeiling_primrec : Primrec positiveCeiling := by
  have hq := MuPublicDictionary.Support.nativeContext_primrec
  have ha := MuPublicDictionary.Support.nativeRoot_primrec
  exact UniformPublicReturn.publicCode_primrec.comp hq
    (ContextTranslation.sourceSuccessorCode_primrec.comp hq ha)

theorem ceilingCode_primrec : Primrec ceilingCode :=
  (Primrec.beq.comp PublicEpsilonSourceDictionary.level_primrec (Primrec.const 0)).cond
    sourceOneCeiling_primrec positiveCeiling_primrec

def ownCeiling (gamma : Nat) : Ordinal.{0} := cond (PublicEpsilonSourceDictionary.level gamma == 0)
  (SourceOneIota.Enclosure.sourceAlphaPlus (PublicEpsilonSourceDictionary.sourceRootCode gamma))
  (Enclosure.sourceAlphaPlus (MuPublicDictionary.Support.nativeContext gamma)
    (MuPublicDictionary.Support.nativeRoot gamma))

theorem source_one_base (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    SourceOneIota.Mu.inputCheck (PublicEpsilonSourceDictionary.sourceRootCode gamma) = true ∧
      SourceOneIota.alphaCode (PublicEpsilonSourceDictionary.sourceRootCode gamma) = gamma := by
  have ha := MuPublicDictionary.Support.source_one_root gamma hg hl
  have hc := SourceOneIota.alphaCode_spec _ ha.1
  have hgcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
  exact ⟨ha.1, Canonical.check_value_injective _ _ hc.1 hgcanon (hc.2.trans ha.2)⟩

theorem positive_base (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    Mu.inputCheck (MuPublicDictionary.Support.nativeContext gamma)
      (MuPublicDictionary.Support.nativeRoot gamma) = true ∧
    betaCode (MuPublicDictionary.Support.nativeContext gamma)
      (MuPublicDictionary.Support.nativeRoot gamma) = gamma := by
  have ha := MuPublicDictionary.Support.native_root gamma hg hl
  have hc := betaCode_spec _ _ ha.1
  have hgcanon := ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
  exact ⟨ha.1, Canonical.check_value_injective _ _ hc.1 hgcanon (hc.2.trans ha.2)⟩

/-- The source-zero successor remains an actual original LOW theta-zero
code. This does not invoke a native grammar at base one. -/
theorem source_one_successor_low (a : Nat) (ha : SourceOneIota.Mu.inputCheck a = true) :
    Hereditary.lowCheckCode 0 (SourceOneIota.ContextTranslation.Support.sourceSuccessorCode a) = true := by
  have hs := SourceOneIota.ContextTranslation.Support.sourceSuccessorCode_spec a ha
  have hc := ((Theta.acceptedCode_iff 0 _).mp hs.1).1
  have ht : Hereditary.check 0 (.theta 0 (ThetaCourse.rawTree
      (Addition.normalizedSumCode 0 (SourceOneIota.OmegaQuotient.argumentCode a)
        SourceOneIota.OmegaQuotient.unitTerm.code))) = true := by
    simpa only [SourceOneIota.ContextTranslation.Support.sourceSuccessorCode,
      SourceOneIota.BoundedPublicReturn.nodeCode, Hereditary.checkCode_code] using hc
  simp only [SourceOneIota.ContextTranslation.Support.sourceSuccessorCode,
    SourceOneIota.BoundedPublicReturn.nodeCode, Hereditary.lowCheckCode_code, Hereditary.lowCheck, ht,
    RelativeTerm.outerSort, Nat.zero_add, le_refl, decide_true, Bool.true_and]

theorem source_one_ceiling_spec (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    Canonical.check (sourceOneCeiling gamma) = true ∧
      unionInterpretation (sourceOneCeiling gamma) =
        SourceOneIota.Enclosure.sourceAlphaPlus (PublicEpsilonSourceDictionary.sourceRootCode gamma) := by
  have ha := (source_one_base gamma hg hl).1
  have hs := SourceOneIota.ContextTranslation.Support.sourceSuccessorCode_spec _ ha
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec _ (source_one_successor_low _ ha)
  exact ⟨hp.1, hp.2.trans hs.2⟩

theorem positive_ceiling_spec (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    Canonical.check (positiveCeiling gamma) = true ∧
      unionInterpretation (positiveCeiling gamma) =
        Enclosure.sourceAlphaPlus (MuPublicDictionary.Support.nativeContext gamma)
          (MuPublicDictionary.Support.nativeRoot gamma) := by
  have hs := ContextTranslation.sourceSuccessorCode_spec _ _ (positive_base gamma hg hl).1
  have hp := UniformPublicReturn.publicCode_spec _ _ ((UniformPublicReturn.inputCheck_exact _ _).mpr hs.1)
  exact ⟨hp.1, hp.2.trans hs.2.2⟩

theorem ceilingCode_spec (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    Canonical.check (ceilingCode gamma) = true ∧
      unionInterpretation (ceilingCode gamma) = ownCeiling gamma := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · simpa only [ceilingCode, ownCeiling, hl, beq_self_eq_true, Bool.cond_true] using
      source_one_ceiling_spec gamma hg hl
  · have hz : (PublicEpsilonSourceDictionary.level gamma == 0) = false := beq_eq_false_iff_ne.mpr hl
    simpa only [ceilingCode, ownCeiling, hz, Bool.cond_false] using positive_ceiling_spec gamma hg hl

/-- The semantic ceiling is below the actual grammar boundary at the
literal public gamma, by its genuinely checked native enclosure. -/
theorem ownCeiling_boundary (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    ownCeiling gamma < globalBoundary (base gamma) 0 := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have ha := source_one_base gamma hg hl
    have hs := SourceOneIota.Enclosure.delta_enclosure_spec _ ha.1
    have hlow : lowCheckCode
        (SourceOneIota.alphaCode (PublicEpsilonSourceDictionary.sourceRootCode gamma))
        (SourceOneIota.Enclosure.deltaEnclosureTerm (PublicEpsilonSourceDictionary.sourceRootCode gamma)).code = true := by
      simp only [lowCheckCode_code, lowCheck, hs.1, SourceOneIota.Enclosure.deltaEnclosureTerm,
        RelativeTerm.outerSort, Nat.zero_add, le_refl, decide_true, Bool.true_and]
    have hb := checked_low_bound _ _ hlow
    rw [interpretation_code, SourceOneIota.Enclosure.delta_enclosure_eq_sourceAlphaPlus _ ha.1,
      ha.2] at hb
    simpa only [ownCeiling, hl, beq_self_eq_true, Bool.cond_true] using hb
  · have ha := positive_base gamma hg hl
    have hs := Enclosure.delta_enclosure_code_spec _ _ ha.1
    have hb := checked_low_bound _ _ hs.1
    rw [hs.2.2, ha.2] at hb
    have hz : (PublicEpsilonSourceDictionary.level gamma == 0) = false := beq_eq_false_iff_ne.mpr hl
    simpa only [ownCeiling, hz, Bool.cond_false] using hb

/-- Actual source-zero contextual fidelity uses the OWN interval, rather
than strengthening the root caller to a selected public-mu cutoff. -/
theorem source_one_public_mu (gamma root : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0)
    (hr : Mu.inputCheck gamma root = true)
    (hcut : interpretation gamma root < ownCeiling gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  let a := PublicEpsilonSourceDictionary.sourceRootCode gamma
  have ha := source_one_base gamma hg hl
  have hn : Mu.inputCheck (SourceOneIota.alphaCode a) root = true := by rw [ha.2]; exact hr
  have hb : interpretation (SourceOneIota.alphaCode a) root < SourceOneIota.Enclosure.sourceAlphaPlus a := by
    simpa only [ha.2, ownCeiling, hl, beq_self_eq_true, Bool.cond_true, a] using hcut
  have hs := SourceOneIota.SkContextFidelity.sourceRoot_spec a root ha.1 hn hb
  have ht := CoveredPublicMu.Support.source_one_root_public_mu (SourceOneIota.SkContextFidelity.sourceRoot a root) hs.1
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec _ (SourceOneIota.root_low _ hs.1)
  have hu := UniformPublicReturn.publicCode_spec gamma root
    ((UniformPublicReturn.inputCheck_exact gamma root).mpr (root_low gamma root hr))
  have hv : Hereditary.interpretation 0 (SourceOneIota.SkContextFidelity.sourceRoot a root) =
      interpretation gamma root := by simpa only [ha.2] using hs.2.1
  have he : UniformPublicReturn.publicCode gamma root =
      SourceOneIota.SourceTrackingRaw.Support.publicCode (SourceOneIota.SkContextFidelity.sourceRoot a root) :=
    Canonical.check_value_injective _ _ hu.1 hp.1 (hu.2.trans (hv.symm.trans hp.2.symm))
  have hm : SourceOneIota.Mu.sourceValue (SourceOneIota.SkContextFidelity.sourceRoot a root) =
      Mu.sourceValue gamma root := by simpa only [ha.2] using hs.2.2.2
  rw [he]
  exact ⟨ht.1, ht.2.trans hm⟩

theorem positive_public_mu (gamma root : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0)
    (hr : Mu.inputCheck gamma root = true)
    (hcut : interpretation gamma root < ownCeiling gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  let q := MuPublicDictionary.Support.nativeContext gamma
  let a := MuPublicDictionary.Support.nativeRoot gamma
  have ha := positive_base gamma hg hl
  have hn : Mu.inputCheck (betaCode q a) root = true := by rw [ha.2]; exact hr
  have hz : (PublicEpsilonSourceDictionary.level gamma == 0) = false := beq_eq_false_iff_ne.mpr hl
  have hb : interpretation (betaCode q a) root < Enclosure.sourceAlphaPlus q a := by
    simpa only [ha.2, ownCeiling, hz, Bool.cond_false, q, a] using hcut
  have hs := ContextTranslation.Return.returnedRoot_spec q a root ha.1 hn
  have hm := ContextTranslation.MuInvariance.returned_sourceValue_eq q a root ha.1 hn hb
  have ht := CoveredPublicMu.Support.positive_root_public_mu (PublicEpsilonSourceDictionary.sourceIndex gamma)
    (ContextTranslation.Return.returnedRoot q a root) hs.1
  have he : UniformPublicReturn.publicCode gamma root =
      UniformPublicReturn.publicCode q (ContextTranslation.Return.returnedRoot q a root) :=
    UniformPublicReturn.publicCode_value_invariant gamma q root _
      ((UniformPublicReturn.inputCheck_exact gamma root).mpr (root_low gamma root hr))
      ((UniformPublicReturn.inputCheck_exact q _).mpr (root_low q _ hs.1))
      (by simpa only [ha.2] using hs.2.symm)
  have hmu : Mu.sourceValue q (ContextTranslation.Return.returnedRoot q a root) = Mu.sourceValue gamma root := by
    simpa only [ha.2] using hm
  rw [he]
  exact ⟨ht.1, ht.2.trans hmu⟩

theorem high_public_mu (gamma root : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hr : Mu.inputCheck gamma root = true)
    (hcut : interpretation gamma root < ownCeiling gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · exact source_one_public_mu gamma root hg hl hr hcut
  · exact positive_public_mu gamma root hg hl hr hcut

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.ContextSupport
