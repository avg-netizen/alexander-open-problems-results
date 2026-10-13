import Alexander313.Wilken.SourceOneNativeSkNextSearch
import Alexander313.Wilken.SourceOneNativeContextTranslation
import Alexander313.Wilken.PublicEpsilonNativeMuLegacyAgreement

/-!
# Genuine original source-one provenance for continuing sk roots

The actual first-step next is at most source-one mu, hence below its own
original alpha-plus. This derives the selected generic caller used by the
original source-one contextual theorem. The literal legacy/unrestricted
mu agreement then identifies the actual unrestricted native loop mu with
the original source-zero mu of the executing returned HIGH root.
The general step retains previously derived current value/mu fidelity and
derives the next original representative, so Path induction can repeat.
No Native base-one parser or endpoint/representative/mu oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkContextFidelity

theorem mu_lt_sourceAlphaPlus (root : Nat) (ha : Mu.inputCheck root = true) :
    Mu.sourceValue root < Enclosure.sourceAlphaPlus root := by
  have hs := Mu.Bounds.muCode_lt_source_alphaPlus root ha
  rw [(Mu.muCode_spec root ha).2.2] at hs
  exact hs

/-- The legacy selected endpoint is genuinely derived from the ORIGINAL
source-one endpoint and the admitted native HIGH next, never assumed as
an adapter from an unrestricted root alone. -/
theorem legacy_caller_of_bound (root next : Nat) (ha : Mu.inputCheck root = true)
    (hn : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) next = true)
    (hb : NativeContext.interpretation (alphaCode root) next < Enclosure.sourceAlphaPlus root) :
    NativeContext.PublicEpsilonIota.Mu.inputCheck (alphaCode root) next = true := by
  obtain ⟨t, he, ht, hnormal, hh⟩ :=
    (NativeContext.PublicEpsilonUnboundedIota.rootCheck_exact _ next).mp hn
  have hc := BoundedContextReturn.intermediate_root_caller root ha t ht hnormal hh
    (by simpa only [he, NativeContext.interpretation_code] using hb)
  simpa only [← he] using hc

def sourceRoot (root next : Nat) : Nat := BoundedContextReturn.returnedRoot root next

theorem sourceRoot_primrec : Primrec₂ sourceRoot := BoundedContextReturn.returnedRoot_primrec

theorem sourceRoot_spec (root next : Nat) (ha : Mu.inputCheck root = true)
    (hn : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) next = true)
    (hb : NativeContext.interpretation (alphaCode root) next < Enclosure.sourceAlphaPlus root) :
    Mu.inputCheck (sourceRoot root next) = true ∧
      interpretation 0 (sourceRoot root next) = NativeContext.interpretation (alphaCode root) next ∧
      alphaCode (sourceRoot root next) = NativeContext.PublicEpsilonUnboundedIota.betaCode (alphaCode root) next ∧
      Mu.sourceValue (sourceRoot root next) =
        NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue (alphaCode root) next := by
  have hc := legacy_caller_of_bound root next ha hn hb
  have hr := BoundedContextReturn.returnedRoot_iota_caller root next ha hc
  have hv := (BoundedContextReturn.returnedRoot_spec root next ha hc).2.2
  have hbase := (BoundedContextReturn.returnedRoot_alphaCode root next ha hc).trans
    (NativeContext.PublicEpsilonUnboundedIota.LegacyAgreement.betaCode_eq _ _ hc).symm
  have hmu := (ContextTranslation.returned_sourceValue_eq root next ha hc).trans
    (NativeContext.PublicEpsilonUnboundedIota.LegacyAgreement.sourceValue_eq _ _ hc).symm
  exact ⟨hr, hv, hbase, hmu⟩

/-- Every true executing ORIGINAL first step has a real original-source
HIGH returned root with the actual native next value, base and next mu. -/
theorem first_source (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) (hh : out.1 = true) :
    Mu.inputCheck (sourceRoot root out.2) = true ∧
      interpretation 0 (sourceRoot root out.2) = NativeContext.interpretation (alphaCode root) out.2 ∧
      alphaCode (sourceRoot root out.2) = NativeContext.PublicEpsilonUnboundedIota.betaCode (alphaCode root) out.2 ∧
      Mu.sourceValue (sourceRoot root out.2) =
        NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue (alphaCode root) out.2 ∧
      NativeContext.interpretation (alphaCode root) out.2 < Enclosure.sourceAlphaPlus root := by
  have hs := SkNextSearch.execute_spec root cutoff out ho
  have ha := ((SkNextSearch.inputCheck_exact root cutoff).mp hs.1).1
  have hn := (SkNextSearch.execute_continue root cutoff out ho hh).1
  have hbound : NativeContext.interpretation (alphaCode root) out.2 < Enclosure.sourceAlphaPlus root :=
    (hs.2.2.2.1.le.trans (SkNextStepSupport.nextValue_le_mu root (unionInterpretation cutoff))).trans_lt
      (mu_lt_sourceAlphaPlus root ha)
  have hr := sourceRoot_spec root out.2 ha hn hbound
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hbound⟩

theorem current_base_eq (root q current : Nat) (ha : Mu.inputCheck root = true)
    (hc : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck q current = true)
    (hv : interpretation 0 root = NativeContext.interpretation q current) :
    alphaCode root = NativeContext.PublicEpsilonUnboundedIota.betaCode q current := by
  have hs := alphaCode_spec root ha
  have ht := NativeContext.PublicEpsilonUnboundedIota.betaCode_spec q current hc
  exact Canonical.check_value_injective _ _ hs.1 ht.1 (hs.2.trans (hv.trans ht.2.symm))

/-- Repeating the native step with an already derived original-source-one
current representative derives its next original representative and mu;
the representative's OWN original endpoint is the only endpoint used. -/
theorem continued_source (root q current cutoff : Nat)
    (out : NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Step)
    (ha : Mu.inputCheck root = true)
    (ho : out ∈ NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute ((q, current), cutoff))
    (hh : out.1 = true)
    (hv : interpretation 0 root = NativeContext.interpretation q current)
    (hm : Mu.sourceValue root = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current) :
    Mu.inputCheck (sourceRoot root out.2) = true ∧
      interpretation 0 (sourceRoot root out.2) =
        NativeContext.interpretation (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2 ∧
      alphaCode (sourceRoot root out.2) =
        NativeContext.PublicEpsilonUnboundedIota.betaCode
          (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2 ∧
      Mu.sourceValue (sourceRoot root out.2) = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue
        (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2 ∧
      NativeContext.interpretation (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2 <
        Enclosure.sourceAlphaPlus root := by
  have hs := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_spec q current cutoff out ho
  have hc := ((NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.inputCheck_exact q current cutoff).mp hs.1).1
  have hn := (NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_continue q current cutoff out ho hh).1
  have hbase := current_base_eq root q current ha hc hv
  have hnext : NativeContext.PublicEpsilonUnboundedIota.Mu.inputCheck (alphaCode root) out.2 = true := by
    rw [hbase]; exact hn
  have hbound : NativeContext.interpretation (alphaCode root) out.2 < Enclosure.sourceAlphaPlus root := by
    have hle : NativeContext.interpretation (alphaCode root) out.2 ≤ Mu.sourceValue root := by
      rw [hbase, hm, hs.2.2.2.1]
      exact NativeContext.PublicEpsilonUnboundedIota.SkNextStep.nextValue_le_mu q current (unionInterpretation cutoff)
    exact hle.trans_lt (mu_lt_sourceAlphaPlus root ha)
  have hr := sourceRoot_spec root out.2 ha hnext hbound
  rw [hbase] at hr hbound
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hbound⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkContextFidelity
