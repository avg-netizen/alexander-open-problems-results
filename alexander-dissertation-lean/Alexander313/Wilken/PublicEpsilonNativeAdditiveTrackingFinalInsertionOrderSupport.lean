import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingMultiplicativePrefix
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentCoverPrefix
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingEpsilonSingletonIntervalOrderSupport

/-!
# Actual final insertion and its independent retained prefix

The concrete greatest selector supplies its written split and real cover.
At the final row the observed index and actual table length force an empty
suffix. A genuine multiplicative child supplies independent full executions
at every retained prefix endpoint. Raw admission is derived from its actual
tracker before the independently executed direct-cover theorem is applied.
No semantic output, selected index or mu column is assumed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FinalInsertionOrderSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_split)
open SourceTrackingSequences (stripLast_append_singleton)
open InsertionSupport (Row)

theorem choose_final (q : Nat) (rows : List Row) (n : Nat) (replacement : List Nat)
    (hs : Insertion.choose q rows = some (n, replacement))
    (hn : n + 1 = rows.length) :
    ∃ before current, before ≠ [] ∧ rows = before ++ [current] ∧
      replacement = current.2 ∧
      Insertion.word q rows = before.map Prod.fst ++ current.2 ∧
      Insertion.coverCheck q (lastCode (before.map Prod.fst))
        (Insertion.firstCode current.2) = true := by
  obtain ⟨before, current, after, hne, hrows, hlen, hword, hcover, hnone⟩ :=
    Insertion.choose_spec q rows n replacement hs
  have hl := congrArg List.length hrows
  simp only [List.length_append, List.length_cons] at hl
  have hzero : after.length = 0 := by omega
  have ha : after = [] := List.length_eq_zero_iff.mp hzero
  subst after
  refine ⟨before, current, hne, hrows, hword, ?_, ?_⟩
  · simp only [Insertion.word, hs, hlen, hrows, List.take_left, hword]
  · simpa only [hword] using hcover

/-- Actual M prefix execution derives the retained raw epsilon caller and
an independently executing word with exactly the retained prefix values. -/
theorem retained_prefix_execution (q root : Nat) (before : List Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck q root = true)
    (hne : before ≠ [])
    (he : SourceMultiplicativeTracking.rawWord q root = before ++ [root]) :
    SourceTrackingRaw.Support.inputCheck q (lastCode before) = true ∧
      SourceMultiplicativePrincipal.inputCheck q (lastCode before) = true ∧
      ∃ out, out ∈ Assignment.execute q (lastCode before) ∧
        out.map (interpretation q) = before.map (interpretation q) := by
  have ht := (Assignment.execute_spec q root (SourceMultiplicativeTracking.rawWord q root)
    (Assignment.execute_multiplicative q root hm)).2.1.1
  have hr : SourceTrackingRaw.Reference q before := by
    simpa only [he, stripLast_append_singleton] using
      ((SourceTrackingRaw.trackingCheck_conditions q _).mp ht).2.1
  have hi := hr.nodes (lastCode before) (lastCode_mem before hne)
  obtain ⟨b, hb, hrev⟩ := stripLast_split before hne
  have hl : lastCode before = b := by
    simp only [lastCode, hrev, Option.getD_some]
  have hp : SourceMultiplicativeTracking.rawWord q root = stripLast before ++ b :: [root] := by
    calc
      SourceMultiplicativeTracking.rawWord q root = before ++ [root] := he
      _ = (stripLast before ++ [b]) ++ [root] := congrArg (fun xs => xs ++ [root]) hb
      _ = stripLast before ++ b :: [root] := by simp only [List.append_assoc, List.singleton_append]
  have hs := MultiplicativePrefix.rawWord_prefix q root hm (stripLast before) [root] b hp
  refine ⟨hi, by simpa only [hl] using hs.1, ?_⟩
  obtain ⟨out, ho, hv⟩ := hs.2
  refine ⟨out, by simpa only [hl] using ho, ?_⟩
  exact hv.trans (congrArg (List.map (interpretation q)) hb.symm)

/-- A real raw epsilon parser and same-source value invariance transport
the direct-cover prefix theorem to every original raw spelling. -/
theorem execute_raw_cover_prefix (q b current : Nat) (before out : List Nat)
    (hb : SourceTrackingRaw.Support.inputCheck q b = true)
    (hbc : interpretation q b < interpretation q current)
    (hcover : interpretation q current ≤ SourceTrackingRaw.Support.muValue q b)
    (hbefore : before ∈ Assignment.execute q b)
    (ho : out ∈ Assignment.execute q current) :
    (before.map (interpretation q)).IsPrefix (out.map (interpretation q)) := by
  have hs := SourceTrackingRaw.Support.rootCode_spec q b hb
  have hm := AssignmentCoverPrefixSupport.high_multiplicative_input q _ hs.2.1
  have hr := Assignment.execute_multiplicative q _ hm
  have hv := Assignment.ValueInvariance.execute_values_eq q b
    (SourceTrackingRaw.Support.rootCode q b) before
    (SourceMultiplicativeTracking.rawWord q (SourceTrackingRaw.Support.rootCode q b))
    hbefore hr hs.2.2.symm
  rw [hv]
  exact AssignmentCoverPrefix.execute_covered_prefix q _ current out hs.2.1
    (by simpa only [hs.2.2] using hbc) hcover ho

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FinalInsertionOrderSupport
