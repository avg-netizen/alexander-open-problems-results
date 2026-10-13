import Alexander313.Wilken.HereditaryGlobalTrackingSequencesSupport

/-!
# Finite upsilon-prefix algebra for actual global tracker certificates

The independent global predicate requires its exact printed initial chain.
These finite list lemmas and the actual endpoint mu computation derive the
prefix erasure and final cover. Relative tracker certificates remain genuine
premises here; the actual producer derives them in the next module. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.AssignmentSupport

open GlobalAdditiveTracking.Source (baseWord baseWord_canonical)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton
  stripLast_append_singleton)

theorem baseWord_succ (m : Nat) :
    baseWord (m + 1) = baseWord m ++ [endpointCode (m + 1)] := by
  simp only [GlobalAdditiveTracking.Source.baseWord, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]

theorem baseWord_ne_nil (m : Nat) (hm : m ≠ 0) : baseWord m ≠ [] := by
  intro he
  have hl := congrArg List.length he
  simp only [baseWord_length, List.length_nil] at hl
  exact hm hl

theorem baseWord_last (m : Nat) : lastCode (baseWord (m + 1)) = endpointCode (m + 1) := by
  rw [baseWord_succ, lastCode_append_singleton]

theorem baseWord_stripLast (m : Nat) : stripLast (baseWord (m + 1)) = baseWord m := by
  rw [baseWord_succ, stripLast_append_singleton]

theorem lastCode_append_nonempty (before codes : List Nat) (hne : codes ≠ []) :
    lastCode (before ++ codes) = lastCode codes := by
  obtain ⟨last, he, hh⟩ := stripLast_split codes hne
  have hl : lastCode codes = last := by simp only [lastCode, hh, Option.getD_some]
  calc
    lastCode (before ++ codes) = last := by rw [he, ← List.append_assoc, lastCode_append_singleton]
    _ = lastCode codes := hl.symm

theorem baseWord_final_cover (m : Nat) (hm : m ≠ 0) :
    muValue (lastCode (baseWord m)) = sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) := by
  cases m with
  | zero => exact False.elim (hm rfl)
  | succ n =>
    rw [baseWord_last, muValue, GlobalMuDictionary.publicCode_endpoint,
      PublicEpsilonSourceDictionary.endpointCode_value]
    exact (PublicUpsilonSegment.successor_value (n + 1)).symm

theorem tracking_baseWord (m : Nat) (hm : m ≠ 0) : Tracking (baseWord m) := by
  cases m with
  | zero => exact False.elim (hm rfl)
  | succ n =>
    have he := (GlobalMuDictionary.Support.inputCheck_exact _).mp
      (GlobalMuDictionary.Support.endpoint_input n)
    have hv : unionInterpretation (endpointCode (n + 1)) =
        sourceUpsilon ((n + 1 : Nat) : Ordinal.{0}) :=
      (PublicEpsilonSourceDictionary.endpointCode_value _).trans
        (PublicUpsilonSegment.successor_value n).symm
    have hp := EpsilonOffsets.epsilon_pos_principal he.2
    have hone := EpsilonOffsets.epsilon_one_lt he.2
    refine ⟨baseWord_ne_nil _ (Nat.succ_ne_zero _), baseWord_canonical _, ?_, ?_, ?_, ?_⟩
    · rw [baseWord_stripLast]; exact reference_baseWord n
    · rw [baseWord_last]; exact hp.1
    · rw [baseWord_last]; exact hp.2
    · rw [baseWord_stripLast, baseWord_last]
      by_cases hn : n = 0
      · subst n
        have hempty : baseWord 0 = [] := rfl
        rw [hempty, if_pos rfl]
        exact ⟨hone.le, hv.le⟩
      · rw [if_neg (baseWord_ne_nil n hn), baseWord_final_cover n hn]
        exact ⟨hone, hv.le⟩

/-- The actual relative certificate becomes a global tracker after the
printed upsilon chain, once its real source gap and endpoint bounds hold. -/
theorem tracking_with_baseWord (m : Nat) (codes : List Nat)
    (ht : PublicTrackingSequences.Tracking codes)
    (hg : TailGap m (stripLast codes))
    (hf : unionInterpretation (lastCode codes) ≤ sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}))
    (hone : m ≠ 0 → 1 < unionInterpretation (lastCode codes)) :
    Tracking (baseWord m ++ codes) := by
  have hne : baseWord m ++ codes ≠ [] := fun he => ht.1 (List.append_eq_nil_iff.mp he).2
  have hprefix := NativeContext.SourceAdditiveTracking.InsertionFidelitySupport.stripLast_append_nonempty
    (baseWord m) codes ht.1
  have hlast := lastCode_append_nonempty (baseWord m) codes ht.1
  have hr := ht.2.2.1
  refine ⟨hne, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact baseWord_canonical m c hc
    · exact ht.2.1 c hc
  · rw [hprefix]
    exact ⟨m, stripLast codes, rfl, EpsilonReference.of_relative hr, hg⟩
  · rw [hlast]; exact ht.2.2.2.1
  · rw [hlast]; exact ht.2.2.2.2.1
  · rw [hprefix, hlast]
    by_cases he : stripLast codes = []
    · have hb : 1 ≤ unionInterpretation (lastCode codes) := by
        simpa only [if_pos he] using ht.2.2.2.2.2
      rw [he, List.append_nil]
      by_cases hm : m = 0
      · subst m
        have hempty : baseWord 0 = [] := rfl
        rw [hempty, if_pos rfl]
        exact ⟨hb, hf⟩
      · rw [if_neg (baseWord_ne_nil m hm), baseWord_final_cover m hm]
        exact ⟨hone hm, hf⟩
    · have hnewne : baseWord m ++ stripLast codes ≠ [] :=
        fun h => he (List.append_eq_nil_iff.mp h).2
      have hb : 1 < unionInterpretation (lastCode codes) ∧
          unionInterpretation (lastCode codes) ≤ SkPublicRecurrence.muValue (lastCode (stripLast codes)) := by
        simpa only [if_neg he] using ht.2.2.2.2.2
      have hc := hr.nodes _ (NativeContext.SourceTrackingSequences.lastCode_mem _ he)
      rw [if_neg hnewne, lastCode_append_nonempty _ _ he, muValue,
        GlobalMuDictionary.publicCode_proper _ hc]
      exact hb

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.AssignmentSupport
