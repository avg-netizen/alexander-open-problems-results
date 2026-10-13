import Alexander313.Wilken.HereditaryGlobalTrackingAssignmentSupport
import Alexander313.Wilken.HereditaryPublicHSmall

/-!
# Genuine proper tails inside segmented global references

The actual finite endpoint scan and strict extended-mu bound force every
epsilon in a global reference tail to stay in its initial endpoint gap.
All of its proper public mu callers are derived. A proper final epsilon
therefore leaves the literal upsilon base chain intact when an independently
executing sk word is spliced there. No supplied segment, tail restriction,
tracker or evaluation is used. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.SmallHSupport

open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton
  lastCode_append_singleton stripLast_singleton stripLast_append_singleton)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)

theorem level_eq_of_gap (m a : Nat) (hc : Canonical.check a = true)
    (hg : TailGap m [a]) : PublicEpsilonSourceDictionary.level a = m := by
  change sourceUpsilon (m : Ordinal.{0}) < unionInterpretation a ∧
    unionInterpretation a < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) at hg
  have hs := PublicEpsilonSourceDictionary.level_bound a hc
  have hle : PublicEpsilonSourceDictionary.level a ≤ m := by
    by_contra h
    have hm : m < PublicEpsilonSourceDictionary.level a := lt_of_not_ge h
    have hf := hs.2.2 m hm
    exact (not_le_of_gt hg.2) (by
      simpa only [PublicUpsilonSegment.successor_value] using hf)
  have hge : m ≤ PublicEpsilonSourceDictionary.level a := by
    cases m with
    | zero => exact Nat.zero_le _
    | succ n =>
      by_contra h
      have hsmall : PublicEpsilonSourceDictionary.level a + 1 ≤ n + 1 := by omega
      have hb := hs.2.1.trans_le (finiteBase_strictMono.monotone hsmall)
      have hl : finiteBase (n + 1) < unionInterpretation a := by
        simpa only [PublicUpsilonSegment.successor_value] using hg.1
      exact hl.not_ge hb.le
  exact Nat.le_antisymm hle hge

theorem proper_of_gap (m a : Nat)
    (ha : GlobalMuDictionary.Support.inputCheck a = true) (hg : TailGap m [a]) :
    MuPublicDictionary.Support.inputCheck a = true := by
  have hs := (GlobalMuDictionary.Support.inputCheck_exact a).mp ha
  have hl := level_eq_of_gap m a hs.1 hg
  have hb : PublicEpsilonSourceDictionary.basePoint a = false :=
    Bool.eq_false_of_not_eq_true (by
      intro h
      have hv := (PublicEpsilonSourceDictionary.basePoint_exact a hs.1).mp h
      rw [hl] at hv
      cases m with
      | zero =>
        rw [finiteBase_zero] at hv
        exact (EpsilonOffsets.epsilon_one_lt hs.2).ne hv.symm
      | succ n =>
        have hlow : finiteBase (n + 1) < unionInterpretation a := by
          simpa only [TailGap, PublicUpsilonSegment.successor_value] using hg.1
        exact hlow.ne hv.symm)
  exact (MuPublicDictionary.Support.inputCheck_exact a).mpr ⟨ha, hb⟩

/-- Every actual extended-mu edge preserves the original strict endpoint
gap. Thus the whole independent epsilon tail is a true proper reference. -/
theorem epsilonReference_in_gap (m : Nat) (xs : List Nat)
    (hr : EpsilonReference xs) (hg : TailGap m xs) :
    PublicTrackingSequences.Reference xs ∧
      ∀ a ∈ xs, TailGap m [a] ∧ PublicEpsilonSourceDictionary.level a = m := by
  induction hr generalizing m with
  | nil =>
    exact ⟨.nil, fun a ha => False.elim (List.not_mem_nil ha)⟩
  | one a ha =>
    have hp := proper_of_gap m a ha hg
    have hl := level_eq_of_gap m a ((GlobalMuDictionary.Support.inputCheck_exact a).mp ha).1 hg
    refine ⟨.one a hp, ?_⟩
    intro c hc
    simpa only [List.mem_singleton.mp hc] using And.intro hg hl
  | cons a b xs ha hab hcover ht ih =>
    have hga : TailGap m [a] := hg
    have hpa := proper_of_gap m a ha hga
    have hla := level_eq_of_gap m a ((GlobalMuDictionary.Support.inputCheck_exact a).mp ha).1 hga
    have hmu : muValue a < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) := by
      simpa only [muValue, hla] using GlobalMuDictionary.publicCode_proper_bound a hpa
    have hgb : TailGap m (b :: xs) := ⟨hg.1.trans hab, hcover.trans_lt hmu⟩
    obtain ⟨hrelative, hnodes⟩ := ih m hgb
    have hcovered : unionInterpretation b ≤ SkPublicRecurrence.muValue a := by
      simpa only [muValue, GlobalMuDictionary.publicCode_proper a hpa,
        SkPublicRecurrence.muValue] using hcover
    refine ⟨.cons a b xs hpa hab hcovered hrelative, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hga, hla⟩
    · exact hnodes c hc

theorem baseWord_image (m c : Nat) (hc : c ∈ baseWord m) :
    SourceUpsilonImage (unionInterpretation c) := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hc
  refine ⟨((i + 1 : Nat) : Ordinal.{0}), ?_⟩
  rw [← he, PublicEpsilonSourceDictionary.endpointCode_value]
  exact (PublicUpsilonSegment.successor_value i).symm

/-- A proper last epsilon lies in the genuine relative tail, never in the
upsilon base chain. Its literal preceding prefix splits accordingly. -/
theorem proper_last_segment (prefix : List Nat) (gamma : Nat)
    (hr : Reference (prefix ++ [gamma]))
    (ha : MuPublicDictionary.Support.inputCheck gamma = true) :
    ∃ m : Nat, ∃ before : List Nat, prefix = baseWord m ++ before ∧
      PublicTrackingSequences.Reference (before ++ [gamma]) ∧ TailGap m (before ++ [gamma]) := by
  obtain ⟨m, tail, he, ht, hg⟩ := hr
  have hgamma : gamma ∈ tail := by
    have hm : gamma ∈ baseWord m ++ tail := by
      rw [← he]
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    rcases List.mem_append.mp hm with hm | hm
    · exact False.elim (((MuPublicDictionary.Support.inputCheck_image gamma).mp ha).2.2
        (baseWord_image m gamma hm))
    · exact hm
  have hne : tail ≠ [] := fun hn => by rw [hn] at hgamma; exact List.not_mem_nil hgamma
  obtain ⟨last, htail, hh⟩ := stripLast_split tail hne
  have hl : lastCode tail = last := by simp only [lastCode, hh, Option.getD_some]
  have heq := congrArg lastCode he
  rw [lastCode_append_singleton, AssignmentSupport.lastCode_append_nonempty _ _ hne, hl] at heq
  rw [← heq] at htail
  have hp := congrArg stripLast he
  rw [stripLast_append_singleton,
    NativeContext.SourceAdditiveTracking.InsertionFidelitySupport.stripLast_append_nonempty _ _ hne] at hp
  have hrelative := (epsilonReference_in_gap m tail ht hg).1
  rw [htail] at hrelative hg
  exact ⟨m, stripLast tail, hp, hrelative, hg⟩

/-- A true proper relative tracker beginning in a genuine endpoint gap
has its entire reference prefix there and its final value below the next
endpoint. These are consequences of its actual numerical mu covers. -/
theorem relative_tracking_in_gap (m a : Nat) (xs : List Nat)
    (ha : MuPublicDictionary.Support.inputCheck a = true)
    (ht : PublicTrackingSequences.Tracking (a :: xs)) (hg : TailGap m [a]) :
    TailGap m (stripLast (a :: xs)) ∧
      unionInterpretation (lastCode (a :: xs)) < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) ∧
        1 < unionInterpretation (lastCode (a :: xs)) := by
  cases xs with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · rw [stripLast_singleton]; trivial
    · simpa only [lastCode_singleton] using hg.2
    · simpa only [lastCode_singleton] using
        EpsilonOffsets.epsilon_one_lt ((MuPublicDictionary.Support.inputCheck_image a).mp ha).2.1
  | cons b xs =>
    have hp := stripLast_cons_nonempty a (b :: xs) (List.cons_ne_nil _ _)
    have hgap : TailGap m (stripLast (a :: b :: xs)) := by
      simpa only [hp, TailGap] using hg
    have hr := ht.2.2.1
    have hall := (epsilonReference_in_gap m _ (EpsilonReference.of_relative hr) hgap).2
    have hn : stripLast (a :: b :: xs) ≠ [] := by rw [hp]; exact List.cons_ne_nil _ _
    have hm := lastCode_mem _ hn
    have hc := hr.nodes _ hm
    have hlevel := (hall _ hm).2
    have hmu : SkPublicRecurrence.muValue (lastCode (stripLast (a :: b :: xs))) <
        sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) := by
      simpa only [GlobalMuDictionary.publicCode_proper _ hc, SkPublicRecurrence.muValue, hlevel]
        using GlobalMuDictionary.publicCode_proper_bound _ hc
    have hb : 1 < unionInterpretation (lastCode (a :: b :: xs)) ∧
        unionInterpretation (lastCode (a :: b :: xs)) ≤
          SkPublicRecurrence.muValue (lastCode (stripLast (a :: b :: xs))) := by
      simpa only [if_neg hn] using ht.2.2.2.2.2
    exact ⟨hgap, hb.2.trans_lt hmu, hb.1⟩

/-- The original full global reference supplies its concrete segment and
all proper callers for a real sk tracker at its last proper epsilon. -/
theorem global_tracking_splice (prefix : List Nat) (gamma : Nat) (xs : List Nat)
    (hr : Reference (prefix ++ [gamma]))
    (ha : MuPublicDictionary.Support.inputCheck gamma = true)
    (ht : PublicTrackingSequences.Tracking (gamma :: xs)) :
    Tracking (prefix ++ gamma :: xs) := by
  obtain ⟨m, before, hp, hrelative, hg⟩ := proper_last_segment prefix gamma hr ha
  have htracked := PublicHSmall.reference_tracking_splice before gamma xs hrelative ht
  have hbound : TailGap m (stripLast (before ++ gamma :: xs)) ∧
      unionInterpretation (lastCode (before ++ gamma :: xs)) <
        sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) ∧
          1 < unionInterpretation (lastCode (before ++ gamma :: xs)) := by
    cases before with
    | nil =>
      exact relative_tracking_in_gap m gamma xs ha htracked hg
    | cons a rest =>
      have hc := hrelative.nodes a (by exact List.mem_cons_self)
      have hga : TailGap m [a] := hg
      exact relative_tracking_in_gap m a (rest ++ gamma :: xs) hc htracked hga
  have hglobal := AssignmentSupport.tracking_with_baseWord m (before ++ gamma :: xs)
    htracked hbound.1 hbound.2.1.le (fun _ => hbound.2.2)
  simpa only [hp, List.append_assoc] using hglobal

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.SmallHSupport
