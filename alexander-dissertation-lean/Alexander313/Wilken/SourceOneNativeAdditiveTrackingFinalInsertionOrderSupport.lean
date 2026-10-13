import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAppendIntervalOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingMultiplicativePrefix
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentCoverPrefix

/-!
# Genuine final insertion and original raw covering prefixes

The actual greatest selector's numerical final-position condition derives
an empty later table suffix, its original retained heads, and the real mu
cover. Raw epsilon admission constructs the original checked HIGH parser
before using full covered-prefix fidelity. No original normal-spelling
injection, retained word, HIGH caller or output comparison is supplied.
Original source check zero is retained. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FinalInsertionOrderSupport

open InsertionSupport (Row)
open NativeContext.SourceTrackingSequences (lastCode)
open SourceMultiplicativeTracking (rawWord)

/-- The actual selector and a final numerical position derive the real
last row, the whole retained table prefix, and its independently tested cover. -/
theorem final_choice_shape (rows : List Row) (n : Nat) (replacement : List Nat)
    (hs : Insertion.choose rows = some (n, replacement))
    (hl : n + 1 = rows.length) :
    ∃ before current, before ≠ [] ∧ rows = before ++ [current] ∧
      Insertion.word rows = before.map Prod.fst ++ current.2 ∧
        Insertion.coverCheck (lastCode (before.map Prod.fst))
          (Insertion.firstCode current.2) = true := by
  obtain ⟨before, current, after, hne, he, hn, hw, hc, hnone⟩ :=
    Insertion.choose_spec rows n replacement hs
  have hzero : after.length = 0 := by
    have hlength := hl
    simp only [he, List.length_append, List.length_cons, hn] at hlength
    omega
  have ha : after = [] := List.length_eq_zero_iff.mp hzero
  have hrows : rows = before ++ [current] := by simpa only [ha] using he
  refine ⟨before, current, hne, hrows, ?_, ?_⟩
  · rw [Insertion.word, hs, hn, hrows, List.take_left, hw]
  · simpa only [hw] using hc

/-- Genuine original raw epsilon admission supplies the actual HIGH
root before full covered-prefix transport. The independent written word
at the raw endpoint is identified only through actual VALUE invariance. -/
theorem execute_raw_cover_prefix (b input : Nat) (word out : List Nat)
    (hb : SourceTrackingRaw.Support.inputCheck b = true)
    (hw : word ∈ Assignment.execute b) (ho : out ∈ Assignment.execute input)
    (hlt : interpretation 0 b < interpretation 0 input)
    (hc : interpretation 0 input ≤ SourceTrackingRaw.Support.muValue b) :
    (word.map (interpretation 0)).IsPrefix (out.map (interpretation 0)) := by
  have hs := SourceTrackingRaw.Support.rootCode_spec b hb
  let root := SourceTrackingRaw.Support.rootCode b
  have hr : rootCheck root = true := hs.2.1
  have hm := CoverPrefixSupport.high_multiplicative root hr
  have hh := Assignment.execute_multiplicative root hm
  have hvalues := Assignment.ValueInvariance.execute_values_eq b root word (rawWord root)
    hw hh hs.2.2.symm
  have hp := CoverPrefix.execute_high_cover_prefix root input (rawWord root) out hr hh ho
    (by rw [show interpretation 0 root = interpretation 0 b from hs.2.2]; exact hlt)
    (by change interpretation 0 input ≤ Mu.sourceValue root at hc; exact hc)
  rw [← hvalues] at hp
  exact hp

/-- A real covered epsilon prefix and genuine ALL-entry bounds compare
every independently executed smaller assignment with that prefix followed
by the strictly larger final value. No smaller word shape is assumed. -/
theorem execute_covered_final_lex (b input : Nat) (word out : List Nat)
    (bound : Ordinal.{0})
    (hb : SourceTrackingRaw.Support.inputCheck b = true)
    (hm : SourceMultiplicativePrincipal.inputCheck b = true)
    (hw : word ∈ Assignment.execute b) (ho : out ∈ Assignment.execute input)
    (hlt : interpretation 0 input < bound)
    (hc : bound ≤ SourceTrackingRaw.Support.muValue b) :
    List.Lex (· < ·) (out.map (interpretation 0))
      (word.map (interpretation 0) ++ [bound]) := by
  rcases lt_trichotomy (interpretation 0 input) (interpretation 0 b) with hl | he | hg
  · exact List.Lex.append_right (· < ·) [bound]
      (CoverPrefix.execute_right_multiplicative_lex input b out word ho hw hm hl)
  · have hv := Assignment.ValueInvariance.execute_values_eq input b out word ho hw he
    rw [hv]
    simpa only [List.append_nil] using List.Lex.append_left (· < ·)
      (List.Lex.nil : List.Lex (· < ·) ([] : List Ordinal.{0}) [bound])
      (word.map (interpretation 0))
  · exact SourceMultiplicativeTracking.OrderSupport.prefix_singleton_lex _ _ bound
      (execute_raw_cover_prefix b input word out hb hw ho hg (hlt.le.trans hc))
      (fun value hvalue => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hvalue
        exact (Assignment.execute_all_bounds input out ho d hd).trans_lt hlt)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FinalInsertionOrderSupport
