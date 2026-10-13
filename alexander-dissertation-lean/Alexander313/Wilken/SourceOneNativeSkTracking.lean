import Alexander313.Wilken.SourceOneNativeSkTrackingSupport

/-!
# Actual source-one tracking of the executing initialized sk word

The original first step and the whole real native Path have original
source-zero HIGH representatives with derived mu fidelity. Each true
edge therefore supplies the original strict epsilon reference cover.
The terminal next is the actual positive principal truncation; the
printed M>1 cutoff gives its strict final bound. The real RAW tracker
accepts the complete executing word. No Native base-one or tracking
assignment, endpoint, representative or mu oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkTracking

open Support

theorem path_tracking {cutoff q current : Nat} {word : Word}
    (hp : NativeContext.PublicEpsilonUnboundedIota.SkIteration.Path cutoff (q, current) word)
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) (root : Nat)
    (ha : Mu.inputCheck root = true)
    (hv : interpretation 0 root = NativeContext.interpretation q current)
    (hm : Mu.sourceValue root = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current)
    (codes : List Nat) (hrel : List.Forall₂ EntryMatches word codes) :
    SourceTrackingRaw.trackingCheck codes = true := by
  induction hp generalizing root codes with
  | stop q current hc hcheck hbound =>
    cases hrel with
    | cons hd ht =>
      cases ht
      have he : interpretation 0 _ = interpretation 0 root := hd.2.trans hv.symm
      apply singleton_tracking _ ((Theta.acceptedLowCode_iff 0 _).mp hd.1).1
      · rw [he]; exact root_pos root ha
      · rw [he, ← root_epsilon root ha]
        exact Ordinal.isPrincipal_add_omega0_opow _
      · rw [he]; exact (EpsilonOffsets.epsilon_one_lt (root_epsilon root ha)).le
  | nextStop q current out helig ho hh =>
    cases hrel with
    | cons hd ht =>
      cases ht with
      | cons hn hnil =>
        cases hnil
        have hr := entry_root root q current _ ha hv hm hd
        have hs := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_spec q current cutoff out ho
        have hb := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_source_bounds
          q current cutoff out ho hmul hcut
          ((NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.eligible_exact cutoff q current).mp helig).2.2
        have hnpos := Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_pos_principal
          (NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current) (unionInterpretation cutoff)
        apply pair_tracking _ _ hr.1 ((Theta.acceptedLowCode_iff 0 _).mp hn.1).1
        · rw [hn.2, hs.2.2.2.1]; exact hnpos.1
        · rw [hn.2, hs.2.2.2.1]; exact hnpos.2
        · rw [hn.2]; exact hcut.trans_le hb.1
        · rw [hn.2, hr.2]; exact hb.2.1
  | nextContinue q current out tail helig ho hh ht ih =>
    cases hrel with
    | cons hd htail =>
      have hs := SkContextFidelity.continued_source root q current cutoff out ha ho hh hv hm
      have htracking := ih (SkContextFidelity.sourceRoot root out.2)
        hs.1 hs.2.1 hs.2.2.2.1 _ htail
      obtain ⟨rest, hhead⟩ := ht.head
      rw [hhead] at htail
      cases htail with
      | cons hn hrest =>
        have hr := entry_root root q current _ ha hv hm hd
        have hnraw := entry_root (SkContextFidelity.sourceRoot root out.2)
          (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2 _
          hs.1 hs.2.1 hs.2.2.2.1 hn
        have hspec := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_spec q current cutoff out ho
        have hnext := hspec.2.2.2.2.mp hh
        have hb := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_source_bounds
          q current cutoff out ho hmul hcut
          ((NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.eligible_exact cutoff q current).mp helig).2.2
        apply tracking_prepend _ _ _ hr.1 hnraw.1
        · rw [hd.2, hn.2, hspec.2.2.2.1]; exact hnext.2
        · rw [hn.2, hr.2]; exact hb.2.1
        · rw [hn.2]; exact hcut.trans_le hb.1
        · exact htracking

/-- The real first source-zero root, actual first-step flag and native
Path determine an original RAW tracker, without a supplied tracker. -/
theorem execute_tracking (root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ SkSourceWord.execute (root, cutoff))
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) :
    SourceTrackingRaw.trackingCheck codes = true := by
  obtain ⟨hi, hs⟩ := SkSourceWord.execute_cases root cutoff codes hc
  have ha := ((SkSourceWord.inputCheck_exact root cutoff).mp hi).1
  have hr := original_root root ha
  rcases hs with ⟨hbound, rfl⟩ | ⟨helig, out, ho, hs⟩
  · apply singleton_tracking root (root_low root ha) (root_pos root ha)
    · rw [← root_epsilon root ha]; exact Ordinal.isPrincipal_add_omega0_opow _
    · exact (EpsilonOffsets.epsilon_one_lt (root_epsilon root ha)).le
  · have hspec := SkNextSearch.execute_spec root cutoff out ho
    have hb := SkNextSearch.execute_source_bounds root cutoff out ho hmul hcut
      ((SkSourceWord.Support.eligible_exact root cutoff).mp helig).2.2
    rcases hs with ⟨hh, rfl⟩ | ⟨hh, word, hw, rfl⟩
    · have hn := SkSourceWord.Support.first_stopCode_spec root cutoff out ho
      have hnpos := Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_pos_principal
        (Mu.sourceValue root) (unionInterpretation cutoff)
      apply pair_tracking root _ hr.1 ((Theta.acceptedLowCode_iff 0 _).mp hn.1).1
      · rw [hn.2, hspec.2.2.2.1]; exact hnpos.1
      · rw [hn.2, hspec.2.2.2.1]; exact hnpos.2
      · rw [hn.2]; exact hcut.trans_le hb.1
      · rw [hn.2, hr.2]; exact hb.2.1
    · have hs := SkContextFidelity.first_source root cutoff out ho hh
      have hp := (NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_spec _ _ _ word hw).2.1
      have hrel := first_flatWord_relation root cutoff out ho hh word hw
      have ht := path_tracking hp hmul hcut (SkContextFidelity.sourceRoot root out.2)
        hs.1 hs.2.1 hs.2.2.2.1 _ hrel
      obtain ⟨rest, hhead⟩ := hp.head
      rw [hhead] at hrel
      rw [hhead] at ht ⊢
      cases hrel with
      | cons hd hrest =>
        have hraw := entry_root (SkContextFidelity.sourceRoot root out.2)
          (alphaCode root) out.2 _ hs.1 hs.2.1 hs.2.2.2.1 hd
        apply tracking_prepend root _ _ hr.1 hraw.1
        · rw [hd.2, hspec.2.2.2.1]; exact (hspec.2.2.2.2.mp hh).2
        · rw [hd.2, hr.2]; exact hb.2.1
        · rw [hd.2]; exact hcut.trans_le hb.1
        · exact ht

theorem execute_reference_prefix (root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ SkSourceWord.execute (root, cutoff))
    (hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hcut : 1 < unionInterpretation cutoff) :
    SourceTrackingRaw.referenceCheck (Hereditary.FinePredecessor.stripLast codes) = true :=
  SourceTrackingRaw.tracking_erasure codes (execute_tracking root cutoff codes hc hmul hcut)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkTracking
