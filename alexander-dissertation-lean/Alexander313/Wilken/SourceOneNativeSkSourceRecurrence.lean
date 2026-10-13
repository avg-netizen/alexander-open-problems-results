import Alexander313.Wilken.SourceOneNativeSkTracking

/-!
# Genuine original source-one sk recurrence and maximal stop

The actual initialized word has the original source-zero raw mu at every
epsilon prefix. Real first-step and native Path induction derive each
eligibility comparison, actual overlined truncation and strict epsilon
continuation. Both maximal stopping tests are retained. No Native base-one
parser, global dictionary assignment or recurrence oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceRecurrence

open SkTracking.Support (EntryMatches Word entry_root original_root first_flatWord_relation)

inductive SourcePath (cutoff : Nat) : List Nat → Prop
  | stop (a : Nat) (ha : SourceTrackingRaw.Support.inputCheck a = true)
      (hb : SourceTrackingRaw.Support.muValue a < unionInterpretation cutoff) :
      SourcePath cutoff [a]
  | nextStop (a d : Nat) (ha : SourceTrackingRaw.Support.inputCheck a = true)
      (hl : lowCheckCode 0 d = true)
      (he : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue a)
      (hv : interpretation 0 d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff))
      (hs : ¬(Ordinal.omega0 ^ interpretation 0 d = interpretation 0 d ∧
        interpretation 0 a < interpretation 0 d)) : SourcePath cutoff [a, d]
  | nextContinue (a b : Nat) (xs : List Nat)
      (ha : SourceTrackingRaw.Support.inputCheck a = true)
      (hb : SourceTrackingRaw.Support.inputCheck b = true)
      (he : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue a)
      (hv : interpretation 0 b = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff))
      (hab : interpretation 0 a < interpretation 0 b)
      (ht : SourcePath cutoff (b :: xs)) : SourcePath cutoff (a :: b :: xs)

theorem path_source {cutoff q current : Nat} {word : Word}
    (hp : NativeContext.PublicEpsilonUnboundedIota.SkIteration.Path cutoff (q, current) word)
    (root : Nat) (ha : Mu.inputCheck root = true)
    (hv : interpretation 0 root = NativeContext.interpretation q current)
    (hm : Mu.sourceValue root = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current)
    (codes : List Nat) (hr : List.Forall₂ EntryMatches word codes) :
    SourcePath cutoff codes := by
  induction hp generalizing root codes with
  | stop q current hc hcut hbound =>
    cases hr with
    | cons hd ht =>
      cases ht
      have hs := entry_root root q current _ ha hv hm hd
      exact .stop _ hs.1 (by rw [hs.2]; exact hbound)
  | nextStop q current out helig ho hh =>
    cases hr with
    | cons hd ht =>
      cases ht with
      | cons hn hnil =>
        cases hnil
        have hs := entry_root root q current _ ha hv hm hd
        have hnext := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_spec q current cutoff out ho
        exact .nextStop _ _ hs.1 ((Theta.acceptedLowCode_iff 0 _).mp hn.1).1
          (by rw [hs.2]; exact
            ((NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.eligible_exact cutoff q current).mp helig).2.2)
          (by simpa only [hn.2, hs.2, NativeContext.PublicEpsilonUnboundedIota.SkNextStep.nextValue]
            using hnext.2.2.2.1)
          (by rw [hd.2, hn.2]; exact
            NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_stop q current cutoff out ho hh)
  | nextContinue q current out tail helig ho hh ht ih =>
    cases hr with
    | cons hd htail =>
      have hs := SkContextFidelity.continued_source root q current cutoff out ha ho hh hv hm
      have hsource := ih (SkContextFidelity.sourceRoot root out.2)
        hs.1 hs.2.1 hs.2.2.2.1 _ htail
      obtain ⟨rest, hhead⟩ := ht.head
      rw [hhead] at htail
      cases htail with
      | cons hn hrest =>
        have hraw := entry_root root q current _ ha hv hm hd
        have hnraw := entry_root (SkContextFidelity.sourceRoot root out.2)
          (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2 _
          hs.1 hs.2.1 hs.2.2.2.1 hn
        have hnext := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_spec q current cutoff out ho
        exact .nextContinue _ _ _ hraw.1 hnraw.1
          (by rw [hraw.2]; exact
            ((NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.eligible_exact cutoff q current).mp helig).2.2)
          (by simpa only [hn.2, hraw.2, NativeContext.PublicEpsilonUnboundedIota.SkNextStep.nextValue]
            using hnext.2.2.2.1)
          (by rw [hd.2, hn.2, hnext.2.2.2.1]; exact (hnext.2.2.2.2.mp hh).2)
          hsource

/-- Every actual initialized output carries the exact original raw mu
recurrence, with no current-context fidelity hypothesis at this endpoint. -/
theorem execute_source (root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ SkSourceWord.execute (root, cutoff)) : SourcePath cutoff codes := by
  obtain ⟨hi, hs⟩ := SkSourceWord.execute_cases root cutoff codes hc
  have ha := ((SkSourceWord.inputCheck_exact root cutoff).mp hi).1
  have hr := original_root root ha
  rcases hs with ⟨hbound, rfl⟩ | ⟨helig, out, ho, hs⟩
  · exact .stop root hr.1 (by rw [hr.2]; exact hbound)
  · have hspec := SkNextSearch.execute_spec root cutoff out ho
    have he : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue root := by
      rw [hr.2]
      exact ((SkSourceWord.Support.eligible_exact root cutoff).mp helig).2.2
    rcases hs with ⟨hh, rfl⟩ | ⟨hh, word, hw, rfl⟩
    · have hn := SkSourceWord.Support.first_stopCode_spec root cutoff out ho
      exact .nextStop root _ hr.1 ((Theta.acceptedLowCode_iff 0 _).mp hn.1).1 he
        (by simpa only [hn.2, hr.2, SkNextStepSupport.nextValue] using hspec.2.2.2.1)
        (by rw [hn.2]; exact SkNextSearch.execute_stop root cutoff out ho hh)
    · have hf := SkContextFidelity.first_source root cutoff out ho hh
      have hp := (NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_spec _ _ _ word hw).2.1
      have hrel := first_flatWord_relation root cutoff out ho hh word hw
      have ht := path_source hp (SkContextFidelity.sourceRoot root out.2)
        hf.1 hf.2.1 hf.2.2.2.1 _ hrel
      obtain ⟨rest, hhead⟩ := hp.head
      rw [hhead] at hrel
      rw [hhead] at ht ⊢
      cases hrel with
      | cons hd hrest =>
        have hraw := entry_root (SkContextFidelity.sourceRoot root out.2)
          (alphaCode root) out.2 _ hf.1 hf.2.1 hf.2.2.2.1 hd
        exact .nextContinue root _ _ hr.1 hraw.1 he
          (by simpa only [hd.2, hr.2, SkNextStepSupport.nextValue] using hspec.2.2.2.1)
          (by rw [hd.2, hspec.2.2.2.1]; exact (hspec.2.2.2.2.mp hh).2) ht

theorem SourcePath.first_step {cutoff a b : Nat} {xs : List Nat}
    (hp : SourcePath cutoff (a :: b :: xs)) :
    SourceTrackingRaw.Support.inputCheck a = true ∧
      unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue a ∧
      interpretation 0 b = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue a) (unionInterpretation cutoff) := by
  cases hp with
  | nextStop a b ha hl he hv hs => exact ⟨ha, he, hv⟩
  | nextContinue a b xs ha hb he hv hab ht => exact ⟨ha, he, hv⟩

def Terminal (cutoff final : Nat) : Prop :=
  (SourceTrackingRaw.Support.inputCheck final = true ∧
    SourceTrackingRaw.Support.muValue final < unionInterpretation cutoff) ∨
    ∃ previous, SourceTrackingRaw.Support.inputCheck previous = true ∧
      unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue previous ∧
      interpretation 0 final = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue previous) (unionInterpretation cutoff) ∧
      ¬(Ordinal.omega0 ^ interpretation 0 final = interpretation 0 final ∧
        interpretation 0 previous < interpretation 0 final)

theorem SourcePath.terminal {cutoff : Nat} {codes : List Nat}
    (hp : SourcePath cutoff codes) :
    ∃ before final, codes = before ++ [final] ∧ Terminal cutoff final := by
  induction hp with
  | stop a ha hb => exact ⟨[], a, rfl, Or.inl ⟨ha, hb⟩⟩
  | nextStop a d ha hl he hv hs => exact ⟨[a], d, rfl, Or.inr ⟨a, ha, he, hv, hs⟩⟩
  | nextContinue a b xs ha hb he hv hab ht ih =>
    obtain ⟨before, final, hout, hfinal⟩ := ih
    exact ⟨a :: before, final, by rw [hout]; rfl, hfinal⟩

theorem execute_spec (root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ SkSourceWord.execute (root, cutoff)) :
    SourcePath cutoff codes ∧ (∃ tail, codes = root :: tail) ∧
      1 < interpretation 0 root ∧
      ∃ before final, codes = before ++ [final] ∧ Terminal cutoff final := by
  have hs := SkSourceWord.execute_spec root cutoff codes hc
  have ha := ((SkSourceWord.inputCheck_exact root cutoff).mp hs.1).1
  have hp := execute_source root cutoff codes hc
  exact ⟨hp, hs.2.2.1, EpsilonOffsets.epsilon_one_lt (root_epsilon root ha), hp.terminal⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceRecurrence
