import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextAssignmentReturn
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingConditionalReplacement
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingConditionalReplacement

/-!
# Actual original-zero and native conditional replacement value agreement

Both independently executing rows retain their actual checked RAW trackers,
LOW factors and factor-to-FINAL callers. Equal head and factor VALUES give
the same canonical public raised context and target. The real raised search
therefore emits the same word, and both genuine original returns preserve
its VALUES. Ordinary products have the shared product value. No contextual
mu equation, original syntax injection or assignment composition is assumed.
Source-only uncompiled candidates; the original source is literal check zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextConditionalValues

open NativeContext.SourceTrackingSequences (lastCode)

theorem publicCode_eq (q c d : Nat) (hc : lowCheckCode 0 c = true)
    (hd : NativeContext.lowCheckCode q d = true)
    (hv : interpretation 0 c = NativeContext.interpretation q d) :
    SourceTrackingRaw.Support.publicCode c = NativeContext.UniformPublicReturn.publicCode q d := by
  have hs := SourceTrackingRaw.Support.publicCode_spec c hc
  have ht := NativeContext.UniformPublicReturn.publicCode_spec q d
    ((NativeContext.UniformPublicReturn.inputCheck_exact q d).mpr hd)
  exact Canonical.check_value_injective _ _ hs.1 ht.1 (hs.2.trans (hv.trans ht.2.symm))

/-- Genuine canonical emissions identify the literal raised search inputs,
without identifying either original checked spelling. -/
theorem raisedWord_eq (q head other factor otherFactor : Nat)
    (hh : lowCheckCode 0 head = true) (ht : NativeContext.lowCheckCode q other = true)
    (hf : lowCheckCode 0 factor = true) (hg : NativeContext.lowCheckCode q otherFactor = true)
    (hv : interpretation 0 head = NativeContext.interpretation q other)
    (he : interpretation 0 factor = NativeContext.interpretation q otherFactor) :
    ReplacementSupport.raisedWord head factor =
      NativeContext.SourceAdditiveTracking.ReplacementSupport.raisedWord q other otherFactor := by
  have hb := publicCode_eq q head other hh ht hv
  have hp := publicCode_eq q factor otherFactor hf hg he
  simp only [ReplacementSupport.raisedWord, ReplacementSupport.raisedSearch,
    ReplacementSupport.raisedBaseCode,
    NativeContext.SourceAdditiveTracking.ReplacementSupport.raisedWord,
    NativeContext.SourceAdditiveTracking.ReplacementSupport.raisedSearch,
    NativeContext.SourceAdditiveTracking.ReplacementSupport.raisedBaseCode, hb, hp]

/-- Both independent original returns preserve the common actual raised
word. The actual LOW and strict raised callers remain explicit. -/
theorem raisedReplacement_values_eq (q head other factor otherFactor : Nat)
    (word otherWord : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (ht : NativeContext.SourceTrackingRaw.Support.inputCheck q other = true)
    (hf : lowCheckCode 0 factor = true) (hg : NativeContext.lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (hv : interpretation 0 head = NativeContext.interpretation q other)
    (he : interpretation 0 factor = NativeContext.interpretation q otherFactor)
    (hw : word ∈ Replacement.raisedReplacement head factor)
    (ho : otherWord ∈ NativeContext.SourceAdditiveTracking.Replacement.raisedReplacement q other otherFactor) :
    word.map (interpretation 0) = otherWord.map (NativeContext.interpretation q) := by
  have hlow := ((SourceTrackingRaw.Support.inputCheck_exact head).mp hh).1
  have htlow := ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact q other).mp ht).1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation q otherFactor) := by simpa only [he] using hm
  have hlt' : NativeContext.interpretation q other < NativeContext.interpretation q otherFactor := by
    simpa only [hv, he] using hlt
  obtain ⟨raised, hra, _, _, hvalues, _, _⟩ :=
    Replacement.raisedReplacement_spec head factor word hh hf hm hlt hw
  obtain ⟨otherRaised, hrb, _, hotherValues, _, _⟩ :=
    NativeContext.SourceAdditiveTracking.Replacement.raisedReplacement_spec q other otherFactor
      otherWord ht hg hm' hlt' ho
  have hp := raisedWord_eq q head other factor otherFactor hlow htlow hf hg hv he
  have hraised : raised = otherRaised := Part.mem_unique (by rw [hp] at hra; exact hra) hrb
  have hb : ReplacementSupport.raisedBaseCode head =
      NativeContext.SourceAdditiveTracking.ReplacementSupport.raisedBaseCode q other :=
    publicCode_eq q head other hlow htlow hv
  exact hvalues.trans (by rw [hraised, hb]; exact hotherValues.symm)

/-- Every actual paired original-zero/native row has the same replacement
VALUES. Both full tracker and factor-to-FINAL callers are retained. -/
theorem conditional_values_eq (q : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (ht : NativeContext.SourceTrackingRaw.trackingCheck q otherHeads = true)
    (head other factor otherFactor : Nat) (hhead : head ∈ heads) (hother : other ∈ otherHeads)
    (hf : lowCheckCode 0 factor = true) (hg : NativeContext.lowCheckCode q otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (hc : NativeContext.interpretation q otherFactor ≤ NativeContext.interpretation q (lastCode otherHeads))
    (hv : interpretation 0 head = NativeContext.interpretation q other)
    (he : interpretation 0 factor = NativeContext.interpretation q otherFactor)
    (word otherWord : List Nat)
    (hw : word ∈ ConditionalReplacement.execute head factor)
    (ho : otherWord ∈ NativeContext.SourceAdditiveTracking.ConditionalReplacement.execute q other otherFactor) :
    word.map (interpretation 0) = otherWord.map (NativeContext.interpretation q) := by
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation q otherFactor) := by simpa only [he] using hm
  have ha := ConditionalReplacement.execute_spec heads hh head factor hhead hf hm hb word hw
  have hd := NativeContext.SourceAdditiveTracking.ConditionalReplacement.execute_spec q otherHeads ht
    other otherFactor hother hg hm' hc otherWord ho
  rcases ha.2.2.2.2 with ⟨hlt, hw⟩ | ⟨hle, a, rfl, ha⟩
  · rcases hd.2.2 with ⟨hlt', ho, _⟩ | ⟨hle', b, rfl, hb'⟩
    · exact raisedReplacement_values_eq q head other factor otherFactor word otherWord
        (ConditionalReplacement.raised_member_caller heads hh head factor hhead hlt hb).2
        (NativeContext.SourceAdditiveTracking.ConditionalReplacement.raised_member_caller
          q otherHeads ht other otherFactor hother hlt' hc).2 hf hg hm hlt hv he hw ho
    · have hle : interpretation 0 factor ≤ interpretation 0 head := by
        simpa only [← hv, ← he] using hle'
      exact False.elim (hlt.not_ge hle)
  · rcases hd.2.2 with ⟨hlt', ho, _⟩ | ⟨hle', b, rfl, hb'⟩
    · have hlt : interpretation 0 head < interpretation 0 factor := by
        simpa only [← hv, ← he] using hlt'
      exact False.elim (hlt.not_ge hle)
    · simp only [List.map_cons, List.map_nil, ha, hb', hv, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextConditionalValues
