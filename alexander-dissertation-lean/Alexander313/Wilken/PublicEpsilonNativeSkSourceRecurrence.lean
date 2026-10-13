import Alexander313.Wilken.PublicEpsilonNativeSkTracking

/-!
# Genuine original-source sk recurrence and maximal stopping certificate

The native Path is flattened through actual terminating original-source
searches. Current HIGH representatives carry already derived mu fidelity,
so each returned RAW prefix has the real SAME-original-source mu value.
Path induction constructs the exact cutoff comparison and overlined MNF
truncation equation for every step, and preserves both maximal stopping
alternatives. No global dictionary assignment or recurrence is assumed.
The certificate retains actual original checkers and raw spellings; Par,
global spelling-independent sk assignment and evaluation remain separate.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence

open SkSourceWord.Support (EntryMatches)

/-- A finite SAME-original-source recurrence certificate with the actual
RAW epsilon mu dictionary and both genuine maximal stop alternatives. -/
inductive SourcePath (q cutoff : Nat) : List Nat → Prop
  | stop (a : Nat) (ha : SourceTrackingRaw.Support.inputCheck q a = true)
      (hb : SourceTrackingRaw.Support.muValue q a < unionInterpretation cutoff) :
      SourcePath q cutoff [a]
  | nextStop (a d : Nat) (ha : SourceTrackingRaw.Support.inputCheck q a = true)
      (hl : lowCheckCode q d = true)
      (he : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue q a)
      (hv : interpretation q d = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff))
      (hs : ¬(Ordinal.omega0 ^ interpretation q d = interpretation q d ∧
        interpretation q a < interpretation q d)) : SourcePath q cutoff [a, d]
  | nextContinue (a b : Nat) (xs : List Nat)
      (ha : SourceTrackingRaw.Support.inputCheck q a = true)
      (hb : SourceTrackingRaw.Support.inputCheck q b = true)
      (he : unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue q a)
      (hv : interpretation q b = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff))
      (hab : interpretation q a < interpretation q b)
      (ht : SourcePath q cutoff (b :: xs)) : SourcePath q cutoff (a :: b :: xs)

/-- The whole native recurrence and actual returned-entry relation derive
the original-source recurrence; no source mu fidelity remains as input at
the public executing endpoint below. -/
theorem path_source {cutoff r current : Nat} {word : SkIteration.Support.Word}
    (hp : SkIteration.Path cutoff (r, current) word) (q root : Nat)
    (ha : Mu.inputCheck q root = true)
    (hv : interpretation q root = interpretation r current)
    (hm : Mu.sourceValue q root = Mu.sourceValue r current)
    (codes : List Nat) (hr : List.Forall₂ (EntryMatches q) word codes) :
    SourcePath q cutoff codes := by
  induction hp generalizing root codes with
  | stop r current hc hcut hbound =>
    cases hr with
    | cons hd ht =>
      cases ht
      have hs := SkTracking.Support.entry_root q root r current _ ha hv hm hd
      exact .stop _ hs.1 (by rw [hs.2]; exact hbound)
  | nextStop r current out helig ho hh =>
    cases hr with
    | cons hd ht =>
      cases ht with
      | cons hn hnil =>
        cases hnil
        have hs := SkTracking.Support.entry_root q root r current _ ha hv hm hd
        have hnext := SkNextSearch.execute_spec r current cutoff out ho
        exact .nextStop _ _ hs.1 hn.1
          (by rw [hs.2]; exact ((SkIteration.Support.eligible_exact cutoff r current).mp helig).2.2)
          (by simpa only [hn.2.2, hs.2, SkNextStep.nextValue] using hnext.2.2.2.1)
          (by rw [hd.2.2, hn.2.2]; exact SkNextSearch.execute_stop r current cutoff out ho hh)
  | nextContinue r current out tail helig ho hh ht ih =>
    cases hr with
    | cons hd htail =>
      have hs := SkContextFidelity.continued_source q root r current cutoff out ha ho hh hv hm
      have hsource := ih (ContextTranslation.Return.returnedRoot q root out.2)
        hs.1 hs.2.1 hs.2.2.2.1 _ htail
      obtain ⟨rest, hhead⟩ := ht.head
      rw [hhead] at htail
      cases htail with
      | cons hn hrest =>
        have hraw := SkTracking.Support.entry_root q root r current _ ha hv hm hd
        have hnraw := SkTracking.Support.entry_root q
          (ContextTranslation.Return.returnedRoot q root out.2) (betaCode r current) out.2 _
          hs.1 hs.2.1 hs.2.2.2.1 hn
        have hnext := SkNextSearch.execute_spec r current cutoff out ho
        exact .nextContinue _ _ _ hraw.1 hnraw.1
          (by rw [hraw.2]; exact ((SkIteration.Support.eligible_exact cutoff r current).mp helig).2.2)
          (by simpa only [hn.2.2, hraw.2, SkNextStep.nextValue] using hnext.2.2.2.1)
          (by rw [hd.2.2, hn.2.2, hnext.2.2.2.1]; exact (hnext.2.2.2.2.mp hh).2)
          hsource

theorem execute_source (q root cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkSourceWord.execute ((q, root), cutoff)) : SourcePath q cutoff codes := by
  obtain ⟨hi, word, hw, hp, hr⟩ := SkSourceWord.execute_relation q root cutoff codes ho
  have ha := ((SkIteration.inputCheck_exact q root cutoff).mp hi).1
  exact path_source hp q root ha rfl rfl codes hr

theorem SourcePath.head {q cutoff : Nat} {codes : List Nat} (hp : SourcePath q cutoff codes) :
    ∃ a xs, codes = a :: xs ∧ SourceTrackingRaw.Support.inputCheck q a = true := by
  cases hp with
  | stop a ha hb => exact ⟨a, [], rfl, ha⟩
  | nextStop a d ha hl he hv hs => exact ⟨a, [d], rfl, ha⟩
  | nextContinue a b xs ha hb he hv hab ht => exact ⟨a, b :: xs, rfl, ha⟩

theorem SourcePath.first_step {q cutoff a b : Nat} {xs : List Nat}
    (hp : SourcePath q cutoff (a :: b :: xs)) :
    SourceTrackingRaw.Support.inputCheck q a = true ∧
      unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue q a ∧
      interpretation q b = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue q a) (unionInterpretation cutoff) := by
  cases hp with
  | nextStop a b ha hl he hv hs => exact ⟨ha, he, hv⟩
  | nextContinue a b xs ha hb he hv hab ht => exact ⟨ha, he, hv⟩

def Terminal (q cutoff : Nat) (final : Nat) : Prop :=
  (SourceTrackingRaw.Support.inputCheck q final = true ∧
    SourceTrackingRaw.Support.muValue q final < unionInterpretation cutoff) ∨
    ∃ previous, SourceTrackingRaw.Support.inputCheck q previous = true ∧
      unionInterpretation cutoff ≤ SourceTrackingRaw.Support.muValue q previous ∧
      interpretation q final = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
        (SourceTrackingRaw.Support.muValue q previous) (unionInterpretation cutoff) ∧
      ¬(Ordinal.omega0 ^ interpretation q final = interpretation q final ∧
        interpretation q previous < interpretation q final)

/-- The final position satisfies one of the actual maximal stop tests;
the emitted false next is retained in the chronological word. -/
theorem SourcePath.terminal {q cutoff : Nat} {codes : List Nat}
    (hp : SourcePath q cutoff codes) :
    ∃ before final, codes = before ++ [final] ∧ Terminal q cutoff final := by
  induction hp with
  | stop a ha hb => exact ⟨[], a, rfl, Or.inl ⟨ha, hb⟩⟩
  | nextStop a d ha hl he hv hs => exact ⟨[a], d, rfl, Or.inr ⟨a, ha, he, hv, hs⟩⟩
  | nextContinue a b xs ha hb he hv hab ht ih =>
    obtain ⟨before, final, hout, hfinal⟩ := ih
    exact ⟨a :: before, final, by rw [hout]; rfl, hfinal⟩

/-- Actual execution retains the ORIGINAL initial root value, its epsilon
class above delta0=1, and the literal finite maximal source recurrence. -/
theorem execute_spec (q root cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkSourceWord.execute ((q, root), cutoff)) :
    SourcePath q cutoff codes ∧ ∃ a xs, codes = a :: xs ∧
      interpretation q a = interpretation q root ∧ 1 < interpretation q a ∧
      ∃ before final, codes = before ++ [final] ∧ Terminal q cutoff final := by
  obtain ⟨hi, word, hw, hp, hr⟩ := SkSourceWord.execute_relation q root cutoff codes ho
  have ha := ((SkIteration.inputCheck_exact q root cutoff).mp hi).1
  have hsource := path_source hp q root ha rfl rfl codes hr
  obtain ⟨rest, hhead⟩ := hp.head
  rw [hhead] at hr
  cases hr with
  | cons hd htail =>
    exact ⟨hsource, _, _, rfl, hd.2.2,
      by rw [hd.2.2]; exact EpsilonOffsets.epsilon_one_lt (RootLowCollapse.root_epsilon q root ha),
      hsource.terminal⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence
