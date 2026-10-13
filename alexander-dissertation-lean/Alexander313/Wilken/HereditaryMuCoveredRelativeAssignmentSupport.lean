import Alexander313.Wilken.HereditaryGlobalTrackingSequences
import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingReturn
import Alexander313.Wilken.PublicEpsilonNativeSkNextSearchSupport

/-!
# Genuine relative-assignment callers from independent extended-mu covers

The selected original mu code is admitted LOW at the SAME epsilon value.
Its actual bound therefore derives the whole covered principal caller.
At a finite upsilon endpoint, extended mu is exactly its original LOW
boundary. That boundary has the printed singleton extension, rather than
a fictitious LOW representative. No source, representative or bound oracle.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuCoveredRelativeAssignment.Support

open NativeContext
open GlobalTrackingSequences (muValue)
open GlobalTrackingSequences.RecognitionSupport (coverCheck coverCheck_primrec coverCheck_exact)
open NativeContext.SourceTrackingSequences.Support (canonical_not_less_exact)

theorem base_caller (gamma : Nat) (hi : GlobalMuDictionary.Support.inputCheck gamma = true) :
    baseCheck gamma = true := by
  have hs := (GlobalMuDictionary.Support.inputCheck_exact gamma).mp hi
  exact (baseCheck_exact gamma).mpr ⟨Canonical.check_original hs.1, hs.2⟩

/-- Both actual original-source branches return their mu in the original
gamma LOW grammar. The value of that grammar base is derived literally. -/
theorem proper_mu_boundary (gamma : Nat)
    (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    unionInterpretation (MuPublicDictionary.publicCode gamma) <
      globalBoundary (unionInterpretation gamma) 0 := by
  rw [(MuPublicDictionary.publicCode_spec gamma hi).2]
  cases hl : PublicEpsilonSourceDictionary.level gamma with
  | zero =>
    have hr := MuPublicDictionary.Support.source_one_root gamma hi hl
    have hm := SourceOneIota.Mu.muCode_spec _ hr.1
    have hb := checked_low_bound _ _ hm.1
    rw [hm.2.2, SourceOneIota.OrderSupport.alpha_base _ hr.1, hr.2] at hb
    simpa only [MuPublicDictionary.Support.sourceValue, hl, beq_self_eq_true,
      Bool.cond_true] using hb
  | succ s =>
    have hn : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by rw [hl]; omega
    have hr := MuPublicDictionary.Support.native_root gamma hi hn
    have hm := PublicEpsilonUnboundedIota.Mu.muCode_spec _ _ hr.1
    have hb := checked_low_bound _ _ hm.1
    rw [hm.2.2, PublicEpsilonUnboundedIota.beta_base _ _ hr.1, hr.2] at hb
    have hne : (s + 1 == 0) = false := by simp
    simpa only [MuPublicDictionary.Support.sourceValue, hl, hne, Bool.cond_false] using hb

theorem endpoint_mu_boundary (gamma : Nat)
    (hi : GlobalMuDictionary.Support.inputCheck gamma = true)
    (he : PublicEpsilonSourceDictionary.basePoint gamma = true) :
    muValue gamma = globalBoundary (unionInterpretation gamma) 0 := by
  have hs := (GlobalMuDictionary.endpoint_extension gamma hi he).2.2
  have hv := (PublicEpsilonSourceDictionary.basePoint_exact gamma
    ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp hi).1).mp he
  simpa only [muValue, PublicUpsilonSegment.successor_value, hv, finiteBase_succ] using hs

theorem extended_mu_boundary (gamma : Nat)
    (hi : GlobalMuDictionary.Support.inputCheck gamma = true) :
    muValue gamma ≤ globalBoundary (unionInterpretation gamma) 0 := by
  cases he : PublicEpsilonSourceDictionary.basePoint gamma with
  | true => exact (endpoint_mu_boundary gamma hi he).le
  | false =>
    have hp := GlobalMuDictionary.Support.proper_caller gamma hi he
    simpa only [muValue, GlobalMuDictionary.publicCode_proper gamma hp] using
      (proper_mu_boundary gamma hp).le

def inputCheck (gamma beta : Nat) : Bool :=
  (PublicTrackingSequences.principalCheck beta && !(Canonical.less beta gamma)) &&
    coverCheck gamma beta

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp
    (Primrec.and.comp (PublicTrackingSequences.principalCheck_primrec.comp Primrec.snd)
      (Primrec.not.comp (Canonical.Effective.less_primrec.comp Primrec.snd Primrec.fst)))
    coverCheck_primrec).to₂

theorem inputCheck_exact (gamma beta : Nat) : inputCheck gamma beta = true ↔
    GlobalMuDictionary.Support.inputCheck gamma = true ∧ Canonical.check beta = true ∧
      0 < unionInterpretation beta ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation beta) ∧
        unionInterpretation gamma ≤ unionInterpretation beta ∧
          unionInterpretation beta ≤ muValue gamma := by
  rw [inputCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hp, hfloor⟩, hcover⟩
    have hc := (coverCheck_exact gamma beta).mp hcover
    have hg := ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp hc.1).1
    have hs := (PublicTrackingSequences.principalCheck_exact beta).mp hp
    exact ⟨hc.1, hc.2.1, hs.2.1, hs.2.2,
      (canonical_not_less_exact beta gamma hc.2.1 hg).mp hfloor, hc.2.2⟩
  · rintro ⟨hg, hb, hpos, hp, hfloor, hcover⟩
    have hc := ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp hg).1
    exact ⟨⟨(PublicTrackingSequences.principalCheck_exact beta).mpr ⟨hb, hpos, hp⟩,
      (canonical_not_less_exact beta gamma hb hc).mpr hfloor⟩,
      (coverCheck_exact gamma beta).mpr ⟨hg, hb, hcover⟩⟩

def boundaryCheck (gamma beta : Nat) : Bool :=
  PublicEpsilonSourceDictionary.basePoint gamma && (GlobalMuDictionary.publicCode gamma == beta)

theorem boundaryCheck_primrec : Primrec₂ boundaryCheck :=
  (Primrec.and.comp (PublicEpsilonSourceDictionary.basePoint_primrec.comp Primrec.fst)
    (Primrec.beq.comp (GlobalMuDictionary.publicCode_primrec.comp Primrec.fst) Primrec.snd)).to₂

theorem boundaryCheck_exact (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    boundaryCheck gamma beta = true ↔ PublicEpsilonSourceDictionary.basePoint gamma = true ∧
      unionInterpretation beta = globalBoundary (unionInterpretation gamma) 0 := by
  have hs := (inputCheck_exact gamma beta).mp hi
  rw [boundaryCheck, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨he, hcode⟩
    exact ⟨he, (congrArg unionInterpretation hcode).symm.trans
      (endpoint_mu_boundary gamma hs.1 he)⟩
  · rintro ⟨he, hv⟩
    exact ⟨he, Canonical.check_value_injective _ _
      (GlobalMuDictionary.publicCode_spec gamma hs.1).1 hs.2.1
      ((endpoint_mu_boundary gamma hs.1 he).trans hv.symm)⟩

/-- Failure of the real boundary branch forces a strict LOW bound from
the independently computed mu, including every proper source spelling. -/
theorem ordinary_bound (gamma beta : Nat) (hi : inputCheck gamma beta = true)
    (hboundary : boundaryCheck gamma beta = false) :
    unionInterpretation beta < globalBoundary (unionInterpretation gamma) 0 := by
  have hs := (inputCheck_exact gamma beta).mp hi
  cases he : PublicEpsilonSourceDictionary.basePoint gamma with
  | false =>
    have hp := GlobalMuDictionary.Support.proper_caller gamma hs.1 he
    have hmu : muValue gamma < globalBoundary (unionInterpretation gamma) 0 := by
      simpa only [muValue, GlobalMuDictionary.publicCode_proper gamma hp] using
        proper_mu_boundary gamma hp
    exact hs.2.2.2.2.2.trans_lt hmu
  | true =>
    have hle := hs.2.2.2.2.2.trans (extended_mu_boundary gamma hs.1)
    apply lt_of_le_of_ne hle
    intro hv
    have ht := (boundaryCheck_exact gamma beta hi).mpr ⟨he, hv⟩
    rw [hboundary] at ht
    cases ht

theorem search_returns (gamma beta : Nat) (hi : inputCheck gamma beta = true)
    (hboundary : boundaryCheck gamma beta = false) :
    ∃ raw, raw ∈ PublicEpsilonUnboundedIota.SkNextSearch.Support.search gamma beta :=
  PublicEpsilonUnboundedIota.SkNextSearch.Support.search_returns gamma beta
    (base_caller gamma ((inputCheck_exact gamma beta).mp hi).1)
    ((inputCheck_exact gamma beta).mp hi).2.1 (ordinary_bound gamma beta hi hboundary)

theorem assignment_caller (gamma beta raw : Nat) (hi : inputCheck gamma beta = true)
    (hr : raw ∈ PublicEpsilonUnboundedIota.SkNextSearch.Support.search gamma beta) :
    SourceAdditiveTracking.Assignment.inputCheck gamma raw = true := by
  have hs := (inputCheck_exact gamma beta).mp hi
  have ht := PublicEpsilonUnboundedIota.SkNextSearch.Support.search_spec gamma beta raw hr
  exact (SourceAdditiveTracking.Assignment.inputCheck_exact gamma raw).mpr
    ⟨ht.1, by simpa only [ht.2.2.2, base] using hs.2.2.2.2.1,
      by simpa only [ht.2.2.2] using hs.2.2.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.MuCoveredRelativeAssignment.Support
