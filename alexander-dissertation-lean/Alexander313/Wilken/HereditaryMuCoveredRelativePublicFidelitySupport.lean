import Alexander313.Wilken.HereditaryMuCoveredRelativeAssignment
import Alexander313.Wilken.HereditaryMuPublicDictionaryAgreement
import Alexander313.Wilken.PublicEpsilonNativeMuBaseValueInvariance
import Alexander313.Wilken.PublicEpsilonNativeSkContextFidelity
import Alexander313.Wilken.SourceOneNativeSkContextFidelity

/-!
# Actual public mu fidelity of covered native epsilon entries

An admitted HIGH entry at the literal canonical epsilon gamma is covered
by the independently executing extended mu of gamma. At a proper gamma
the actual selected original-source mu is below its OWN alpha-plus, so the
true contextual return supplies an original-source HIGH representative
and its actual mu equality. The original-source dictionary agreement then
identifies the independent public query at this entry. A finite endpoint
uses genuine SAME-base spelling invariance and retains the literal source.
No arbitrary RAW tracker or value-only cross-context mu equality is used.
Every source selection, HIGH representative and interval caller derives
from the original covered-entry guards. Source-only uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.CoveredPublicMu.Support

theorem positive_root_public_mu (s root : Nat)
    (hr : Mu.inputCheck (NativePublicBridge.contextCode s) root = true) :
    MuPublicDictionary.Support.inputCheck
        (UniformPublicReturn.publicCode (NativePublicBridge.contextCode s) root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode
        (UniformPublicReturn.publicCode (NativePublicBridge.contextCode s) root)) =
          Mu.sourceValue (NativePublicBridge.contextCode s) root := by
  have hraw : SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) root = true :=
    (SourceTrackingRaw.Support.inputCheck_exact _ root).mpr
      ⟨root_low _ root hr, root_base_lt _ root hr, root_epsilon _ root hr⟩
  exact ⟨MuPublicDictionary.Agreement.positive_caller s root hraw,
    (MuPublicDictionary.Agreement.positive_public_mu s root hraw).trans
      (SourceTrackingRaw.Support.muValue_eq _ root root hraw hr rfl)⟩

theorem source_one_root_public_mu (root : Nat)
    (hr : SourceOneIota.Mu.inputCheck root = true) :
    MuPublicDictionary.Support.inputCheck (SourceOneIota.SourceTrackingRaw.Support.publicCode root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode
        (SourceOneIota.SourceTrackingRaw.Support.publicCode root)) = SourceOneIota.Mu.sourceValue root := by
  have hraw : SourceOneIota.SourceTrackingRaw.Support.inputCheck root = true :=
    (SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact root).mpr
      ⟨SourceOneIota.root_low root hr,
        EpsilonOffsets.epsilon_one_lt (SourceOneIota.root_epsilon root hr),
        SourceOneIota.root_epsilon root hr⟩
  exact ⟨MuPublicDictionary.Agreement.source_one_caller root hraw,
    (MuPublicDictionary.Agreement.source_one_public_mu root hraw).trans
      (SourceOneIota.SourceTrackingRaw.Support.muValue_eq root root hraw hr rfl)⟩

/-- At a finite endpoint only base spelling changes. The actual target
root and full source cutoff derive from its second-context checker. -/
theorem endpoint_public_mu (gamma root : Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (hb : PublicEpsilonSourceDictionary.basePoint gamma = true)
    (hr : Mu.inputCheck gamma root = true) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  have hs := PublicEpsilonSourceDictionary.base_point_spec gamma hg hb
  have he : base gamma = base (NativePublicBridge.contextCode (PublicEpsilonSourceDictionary.sourceIndex gamma)) :=
    hs.2.2.symm
  have ht := Mu.BaseValueInvariance.root_caller gamma _ root hr hs.2.1 he
  have hp := positive_root_public_mu (PublicEpsilonSourceDictionary.sourceIndex gamma) root ht
  have hcode := UniformPublicReturn.publicCode_same_base gamma _ root (source_checked gamma root hr)
    hs.2.1 he (root_low gamma root hr)
  rw [hcode]
  exact ⟨hp.1, hp.2.trans (Mu.BaseValueInvariance.sourceValue_eq gamma _ root hr hs.2.1 he).symm⟩

/-- The proper source-one dictionary derives its original root and OWN
interval, and the real contextual theorem supplies the returned HIGH
representative. Original check0 supplies the independent public mu caller. -/
theorem proper_source_one_public_mu (gamma root : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0)
    (hr : Mu.inputCheck gamma root = true)
    (hbound : interpretation gamma root ≤ GlobalTrackingSequences.muValue gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  let a := PublicEpsilonSourceDictionary.sourceRootCode gamma
  have ha := MuPublicDictionary.Support.source_one_root gamma hg hl
  have hcanon := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp
    ((MuPublicDictionary.Support.inputCheck_exact gamma).mp hg).1
  have hc := SourceOneIota.alphaCode_spec a ha.1
  have he : SourceOneIota.alphaCode a = gamma :=
    Canonical.check_value_injective _ _ hc.1 hcanon.1 (hc.2.trans ha.2)
  have hmu : GlobalTrackingSequences.muValue gamma = SourceOneIota.Mu.sourceValue a := by
    rw [GlobalTrackingSequences.muValue, GlobalMuDictionary.publicCode_proper gamma hg,
      (MuPublicDictionary.publicCode_spec gamma hg).2]
    simp only [MuPublicDictionary.Support.sourceValue, hl, beq_self_eq_true, Bool.cond_true, a]
  have hn : Mu.inputCheck (SourceOneIota.alphaCode a) root = true := by rw [he]; exact hr
  have hcut : interpretation (SourceOneIota.alphaCode a) root < SourceOneIota.Enclosure.sourceAlphaPlus a := by
    rw [he]
    exact (hbound.trans_eq hmu).trans_lt (SourceOneIota.SkContextFidelity.mu_lt_sourceAlphaPlus a ha.1)
  have hs := SourceOneIota.SkContextFidelity.sourceRoot_spec a root ha.1 hn hcut
  have ht := source_one_root_public_mu (SourceOneIota.SkContextFidelity.sourceRoot a root) hs.1
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec _
    (SourceOneIota.root_low _ hs.1)
  have hu := UniformPublicReturn.publicCode_spec gamma root
    ((UniformPublicReturn.inputCheck_exact gamma root).mpr (root_low gamma root hr))
  have hv : Hereditary.interpretation 0 (SourceOneIota.SkContextFidelity.sourceRoot a root) =
      interpretation gamma root := by simpa only [he] using hs.2.1
  have hcode : UniformPublicReturn.publicCode gamma root =
      SourceOneIota.SourceTrackingRaw.Support.publicCode (SourceOneIota.SkContextFidelity.sourceRoot a root) :=
    Canonical.check_value_injective _ _ hu.1 hp.1
      (hu.2.trans (hv.symm.trans hp.2.symm))
  have hm : SourceOneIota.Mu.sourceValue (SourceOneIota.SkContextFidelity.sourceRoot a root) =
      Mu.sourceValue gamma root := by simpa only [he] using hs.2.2.2
  rw [hcode]
  exact ⟨ht.1, ht.2.trans hm⟩

/-- At a proper positive source the real original HIGH root, actual mu
and its OWN successor bound derive the true contextual-return caller.
The returned original root enters the independent SAME-source dictionary. -/
theorem proper_positive_public_mu (gamma root : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0)
    (hr : Mu.inputCheck gamma root = true)
    (hbound : interpretation gamma root ≤ GlobalTrackingSequences.muValue gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  let q := MuPublicDictionary.Support.nativeContext gamma
  let a := MuPublicDictionary.Support.nativeRoot gamma
  have ha := MuPublicDictionary.Support.native_root gamma hg hl
  have hc := betaCode_spec q a ha.1
  have hcanon := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp
    ((MuPublicDictionary.Support.inputCheck_exact gamma).mp hg).1
  have he : betaCode q a = gamma :=
    Canonical.check_value_injective _ _ hc.1 hcanon.1 (hc.2.trans ha.2)
  have hz : (PublicEpsilonSourceDictionary.level gamma == 0) = false := beq_eq_false_iff_ne.mpr hl
  have hmu : GlobalTrackingSequences.muValue gamma = Mu.sourceValue q a := by
    rw [GlobalTrackingSequences.muValue, GlobalMuDictionary.publicCode_proper gamma hg,
      (MuPublicDictionary.publicCode_spec gamma hg).2]
    simp only [MuPublicDictionary.Support.sourceValue, hz, Bool.cond_false, q, a]
  have hn : Mu.inputCheck (betaCode q a) root = true := by rw [he]; exact hr
  have hcut : interpretation (betaCode q a) root < Enclosure.sourceAlphaPlus q a := by
    rw [he]
    exact (hbound.trans_eq hmu).trans_lt (SkContextFidelity.mu_lt_sourceAlphaPlus q a ha.1)
  have hs := ContextTranslation.Return.returnedRoot_spec q a root ha.1 hn
  have hm := ContextTranslation.MuInvariance.returned_sourceValue_eq q a root ha.1 hn hcut
  have ht := positive_root_public_mu (PublicEpsilonSourceDictionary.sourceIndex gamma)
    (ContextTranslation.Return.returnedRoot q a root) hs.1
  have hcode : UniformPublicReturn.publicCode gamma root =
      UniformPublicReturn.publicCode q (ContextTranslation.Return.returnedRoot q a root) :=
    UniformPublicReturn.publicCode_value_invariant gamma q root _
      ((UniformPublicReturn.inputCheck_exact gamma root).mpr (root_low gamma root hr))
      ((UniformPublicReturn.inputCheck_exact q _).mpr (root_low q _ hs.1))
      (by simpa only [he] using hs.2.symm)
  have hm : Mu.sourceValue q (ContextTranslation.Return.returnedRoot q a root) = Mu.sourceValue gamma root := by
    simpa only [he] using hm
  rw [hcode]
  exact ⟨ht.1, ht.2.trans hm⟩

/-- The actual covered HIGH entry guard alone derives independent proper
public mu admission and equality. Source selection and every OWN endpoint
caller are constructed in the exhaustive endpoint/source-one/positive split. -/
theorem high_root_public_mu (gamma root : Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (hr : Mu.inputCheck gamma root = true)
    (hbound : interpretation gamma root ≤ GlobalTrackingSequences.muValue gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma root) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma root)) =
        Mu.sourceValue gamma root := by
  cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
  | true => exact endpoint_public_mu gamma root hg hb hr
  | false =>
    have hp := GlobalMuDictionary.Support.proper_caller gamma hg hb
    by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
    · exact proper_source_one_public_mu gamma root hp hl hr hbound
    · exact proper_positive_public_mu gamma root hp hl hr hbound

/-- The genuine original raw parser supplies a HIGH representative with
the same VALUE; whole canonical return then preserves the literal public
entry. The actual coverage bound supplies every contextual caller. -/
theorem raw_public_mu (gamma raw : Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (hr : SourceTrackingRaw.Support.inputCheck gamma raw = true)
    (hbound : interpretation gamma raw ≤ GlobalTrackingSequences.muValue gamma) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma raw) = true ∧
      unionInterpretation (MuPublicDictionary.publicCode (UniformPublicReturn.publicCode gamma raw)) =
        SourceTrackingRaw.Support.muValue gamma raw := by
  have hs := SourceTrackingRaw.Support.rootCode_spec gamma raw hr
  have ht := high_root_public_mu gamma (SourceTrackingRaw.Support.rootCode gamma raw) hg hs.2.1
    (hs.2.2.le.trans hbound)
  have he := UniformPublicReturn.publicCode_value_invariant gamma gamma raw
    (SourceTrackingRaw.Support.rootCode gamma raw)
    ((UniformPublicReturn.inputCheck_exact gamma raw).mpr hs.1)
    ((UniformPublicReturn.inputCheck_exact gamma _).mpr (root_low gamma _ hs.2.1)) hs.2.2.symm
  rw [he]
  exact ht

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.CoveredPublicMu.Support
