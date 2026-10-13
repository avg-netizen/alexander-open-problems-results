import Alexander313.Wilken.HereditaryGlobalTrackingAssignmentSupport

/-!
# Actual original assignment outputs stay in their genuine finite source

Every bound below follows from the independently computed original RAW
tracker, actual LOW emissions and the genuine selected source grammar.
Positive finite reference prefixes exceed their real epsilon base, and
the final entry is greater than one even when that prefix is empty.
No global tracker or source-bound certificate is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.AssignmentBounds

open GlobalAdditiveTracking
open GlobalAdditiveTracking.Source (level contextCode sourceIndex)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem)

theorem native_boundary (alpha : Nat) (hn : level alpha ≠ 0) :
    globalBoundary (NativeContext.base (contextCode alpha)) 0 = finiteBase (level alpha + 1) := by
  cases hm : level alpha with
  | zero => exact False.elim (hn hm)
  | succ s =>
    simpa only [contextCode, Source.sourceIndex_succ alpha s hm,
      NativePublicBridge.contextCode_value, hm] using (finiteBase_succ (s + 1)).symm

theorem sourceOneExecute_bound (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.sourceOneExecute alpha) :
    ∀ c ∈ codes, unionInterpretation c < sourceUpsilon (1 : Ordinal.{0}) := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff Return.sourceOneWord).mp ho
  have ht := SourceOneIota.SourceAdditiveTracking.Assignment.execute_tracking _ word hw
  have hl := Return.source_one_word_low word ht
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec d (hl d hd)
  have hb : interpretation 0 d < finiteBase 1 :=
    (lt_nextBase_iff_code 0 _).mpr ⟨d, hl d hd, rfl⟩
  exact (hp.2.trans_lt hb).trans_eq (PublicUpsilonSegment.successor_value 0).symm

theorem nativeExecute_bound (alpha : Nat) (codes : List Nat)
    (hn : level alpha ≠ 0) (ho : codes ∈ Return.nativeExecute alpha) :
    ∀ c ∈ codes, unionInterpretation c <
      sourceUpsilon ((level alpha + 1 : Nat) : Ordinal.{0}) := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff (Return.nativeWord alpha)).mp ho
  have ht := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw
  have hl := Return.native_word_low (contextCode alpha) word ht
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hp := NativeContext.UniformPublicReturn.publicCode_spec _ d
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ d).mpr (hl d hd))
  have hb := NativeContext.checked_low_bound _ d (hl d hd)
  rw [native_boundary alpha hn] at hb
  exact (hp.2.trans_lt hb).trans_eq (PublicUpsilonSegment.successor_value _).symm

theorem nativeExecute_prefix_base_lt (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.nativeExecute alpha) :
    ∀ c ∈ stripLast codes, NativeContext.base (contextCode alpha) < unionInterpretation c := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff (Return.nativeWord alpha)).mp ho
  have ht := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ word).mp
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw)
  have hl := Return.native_word_low (contextCode alpha) word
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw)
  intro c hc
  rw [Return.nativeWord, GlobalAdditiveTracking.RelativeCertificate.stripLast_map] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hp := NativeContext.UniformPublicReturn.publicCode_spec _ d
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ d).mpr
      (hl d (Hereditary.FinePredecessor.stripLast_mem word d hd)))
  rw [hp.2]
  exact (ht.2.1.epsilons d hd).2.1

theorem nativeExecute_final_one_lt (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.nativeExecute alpha) : 1 < unionInterpretation (lastCode codes) := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff (Return.nativeWord alpha)).mp ho
  have ht := (NativeContext.SourceTrackingRaw.trackingCheck_conditions _ word).mp
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw)
  have hl := Return.native_word_low (contextCode alpha) word
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ _ word hw)
  have hp := NativeContext.UniformPublicReturn.publicCode_spec _ (lastCode word)
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ _).mpr (hl _ (lastCode_mem word ht.1)))
  rw [Return.nativeWord,
    GlobalAdditiveTracking.RelativeCertificate.lastCode_map _ word ht.1, hp.2]
  by_cases he : stripLast word = []
  · have hb : NativeContext.base (contextCode alpha) ≤ NativeContext.interpretation (contextCode alpha)
        (lastCode word) := by simpa only [if_pos he] using ht.2.2.2.2.2
    have hbase : 1 < NativeContext.base (contextCode alpha) := by
      rw [contextCode, NativePublicBridge.contextCode_value]
      exact EpsilonOffsets.epsilon_one_lt (finiteBase_succ_omegaPower_eq_self (sourceIndex alpha))
    exact hbase.trans_le hb
  · have hb : 1 < NativeContext.interpretation (contextCode alpha) (lastCode word) ∧
        NativeContext.interpretation (contextCode alpha) (lastCode word) ≤
          NativeContext.SourceTrackingRaw.Support.muValue (contextCode alpha) (lastCode (stripLast word)) := by
      simpa only [if_neg he] using ht.2.2.2.2.2
    exact hb.1

theorem nativeExecute_gap (alpha : Nat) (codes : List Nat)
    (hn : level alpha ≠ 0) (ho : codes ∈ Return.nativeExecute alpha) :
    TailGap (level alpha) (stripLast codes) := by
  cases he : stripLast codes with
  | nil => trivial
  | cons a xs =>
    have hm : a ∈ stripLast codes := by rw [he]; exact List.mem_cons_self
    have hlow := nativeExecute_prefix_base_lt alpha codes ho a hm
    have hhigh := nativeExecute_bound alpha codes hn ho a
      (Hereditary.FinePredecessor.stripLast_mem codes a hm)
    have hbase : sourceUpsilon ((level alpha : Nat) : Ordinal.{0}) =
        NativeContext.base (contextCode alpha) := by
      cases hi : level alpha with
      | zero => exact False.elim (hn hi)
      | succ s =>
        simpa only [hi, contextCode, Source.sourceIndex_succ alpha s hi,
          NativePublicBridge.contextCode_value] using PublicUpsilonSegment.successor_value s
    simpa only [TailGap, he, hbase] using And.intro hlow hhigh

theorem sourceOneExecute_gap (alpha : Nat) (codes : List Nat)
    (ho : codes ∈ Return.sourceOneExecute alpha) : TailGap 0 (stripLast codes) := by
  have ht := RelativeCertificate.sourceOneExecute_tracking alpha codes ho
  cases he : stripLast codes with
  | nil => trivial
  | cons a xs =>
    have hm : a ∈ stripLast codes := by rw [he]; exact List.mem_cons_self
    have ha := (ht.2.2.1.epsilons a hm).2.1
    have hpos := EpsilonOffsets.epsilon_pos_principal ha
    have hb := sourceOneExecute_bound alpha codes ho a
      (Hereditary.FinePredecessor.stripLast_mem codes a hm)
    simpa only [TailGap, he, sourceUpsilon_zero] using And.intro hpos.1 hb

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.AssignmentBounds
