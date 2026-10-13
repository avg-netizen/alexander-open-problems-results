import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueSupport

/-!
# Actual conditional replacement values across two coded contexts

Both contexts retain their real LOW admissions and executing RAW trackers.
Canonical public head and factor emissions with equal VALUES are literally
equal, so the independently executed raised searches use the same actual
epsilon context and target. Their genuine original finite returns preserve
that common raised word. Ordinary replacements have the real shared product
value. No input syntax injection, contextual mu equation, word composition
or lexical comparison is supplied or asserted. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextConditionalValues

open PublicEpsilonUnboundedIota SourceTrackingSequences

theorem publicCode_eq (q r c d : Nat) (hc : lowCheckCode q c = true)
    (hd : lowCheckCode r d = true) (hv : interpretation q c = interpretation r d) :
    UniformPublicReturn.publicCode q c = UniformPublicReturn.publicCode r d :=
  UniformPublicReturn.publicCode_value_invariant q r c d
    ((UniformPublicReturn.inputCheck_exact q c).mpr hc)
    ((UniformPublicReturn.inputCheck_exact r d).mpr hd) hv

/-- Literal raised-context inputs follow from genuine canonical emissions,
even though the original checked head and factor spellings differ. -/
theorem raisedWord_eq (q r head other factor otherFactor : Nat)
    (hh : lowCheckCode q head = true) (ht : lowCheckCode r other = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode r otherFactor = true)
    (hv : interpretation q head = interpretation r other)
    (he : interpretation q factor = interpretation r otherFactor) :
    ReplacementSupport.raisedWord q head factor =
      ReplacementSupport.raisedWord r other otherFactor := by
  have hb := publicCode_eq q r head other hh ht hv
  have hp := publicCode_eq q r factor otherFactor hf hg he
  simp only [ReplacementSupport.raisedWord, ReplacementSupport.raisedSearch,
    ReplacementSupport.raisedBaseCode, hb, hp]

/-- Actual independent finite original-context returns preserve the VALUES
of their common executing raised word, without a return spelling identity. -/
theorem raisedReplacement_values_eq (q r head other factor otherFactor : Nat)
    (word otherWord : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (ht : SourceTrackingRaw.Support.inputCheck r other = true)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode r otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (hv : interpretation q head = interpretation r other)
    (he : interpretation q factor = interpretation r otherFactor)
    (hw : word ∈ Replacement.raisedReplacement q head factor)
    (ho : otherWord ∈ Replacement.raisedReplacement r other otherFactor) :
    word.map (interpretation q) = otherWord.map (interpretation r) := by
  have hlow := ((SourceTrackingRaw.Support.inputCheck_exact q head).mp hh).1
  have htlow := ((SourceTrackingRaw.Support.inputCheck_exact r other).mp ht).1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation r otherFactor) := by simpa only [he] using hm
  have hlt' : interpretation r other < interpretation r otherFactor := by
    simpa only [hv, he] using hlt
  obtain ⟨raised, hra, _, hvalues, _, _⟩ :=
    Replacement.raisedReplacement_spec q head factor word hh hf hm hlt hw
  obtain ⟨otherRaised, hrb, _, hotherValues, _, _⟩ :=
    Replacement.raisedReplacement_spec r other otherFactor otherWord ht hg hm' hlt' ho
  have hp := raisedWord_eq q r head other factor otherFactor hlow htlow hf hg hv he
  have hraised : raised = otherRaised := Part.mem_unique (by rw [hp] at hra; exact hra) hrb
  have hb : ReplacementSupport.raisedBaseCode q head =
      ReplacementSupport.raisedBaseCode r other := publicCode_eq q r head other hlow htlow hv
  exact hvalues.trans (by rw [hraised, hb]; exact hotherValues.symm)

/-- Every paired actual written row has the same actual replacement VALUES.
The two tracker guards and both factor-to-FINAL callers are retained. -/
theorem conditional_values_eq (q r : Nat) (heads otherHeads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (ht : SourceTrackingRaw.trackingCheck r otherHeads = true)
    (head other factor otherFactor : Nat) (hhead : head ∈ heads) (hother : other ∈ otherHeads)
    (hf : lowCheckCode q factor = true) (hg : lowCheckCode r otherFactor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : interpretation r otherFactor ≤ interpretation r (lastCode otherHeads))
    (hv : interpretation q head = interpretation r other)
    (he : interpretation q factor = interpretation r otherFactor)
    (word otherWord : List Nat)
    (hw : word ∈ ConditionalReplacement.execute q head factor)
    (ho : otherWord ∈ ConditionalReplacement.execute r other otherFactor) :
    word.map (interpretation q) = otherWord.map (interpretation r) := by
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation r otherFactor) := by simpa only [he] using hm
  have ha := ConditionalReplacement.execute_spec q heads hh head factor hhead hf hm hb word hw
  have hd := ConditionalReplacement.execute_spec r otherHeads ht other otherFactor hother hg hm' hc otherWord ho
  rcases ha.2.2 with ⟨hlt, hw, _⟩ | ⟨hle, a, rfl, ha⟩
  · rcases hd.2.2 with ⟨hlt', ho, _⟩ | ⟨hle', b, rfl, hb'⟩
    · exact raisedReplacement_values_eq q r head other factor otherFactor word otherWord
        (ConditionalReplacement.raised_member_caller q heads hh head factor hhead hlt hb).2
        (ConditionalReplacement.raised_member_caller r otherHeads ht other otherFactor hother hlt' hc).2
        hf hg hm hlt hv he hw ho
    · have hle : interpretation q factor ≤ interpretation q head := by
        simpa only [← hv, ← he] using hle'
      exact False.elim (hlt.not_ge hle)
  · rcases hd.2.2 with ⟨hlt', ho, _⟩ | ⟨hle', b, rfl, hb'⟩
    · have hlt : interpretation q head < interpretation q factor := by
        simpa only [← hv, ← he] using hlt'
      exact False.elim (hlt.not_ge hle)
    · simp only [List.map_cons, List.map_nil, ha, hb', hv, he]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextConditionalValues
