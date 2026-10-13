import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment

/-!
# Strict original native epsilon prefix of the complete assignment

The real RAW reference supplies epsilon admission and strict ordering.
For a multiplicative leaf its proper table entries belong to the actual
strict localization path before that path's genuine input-value endpoint.
For a nonmultiplicative input, equality with a prefix epsilon contradicts
the actual M flag. Every upper bound follows from execution. No path,
prefix or endpoint bound is supplied. Source-only uncompiled candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ProperPrefix

open Hereditary.FinePredecessor (stripLast)
open SourceTrackingSequences (stripLast_singleton stripLast_append_singleton)
open SourceMultiplicativeTracking SourceMultiplicativeTracking.Support

private theorem endpoint_append_singleton (xs : List Nat) (d : Nat) :
    SourceLocalization.endpoint (xs ++ [d]) = d := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => exact ih

theorem properPrefix_lt_root (q root : Nat) (hi : SourceLocalization.inputCheck q root = true)
    (d : Nat) (hd : d ∈ properPrefix q root) : interpretation q d < interpretation q root := by
  obtain ⟨tail, hhead⟩ := SourceLocalization.nativePath_head q root
  have hm : d ∈ stripLast tail := by simpa only [properPrefix, hhead, List.tail_cons] using hd
  have hne : tail ≠ [] := by
    intro he
    subst tail
    exact List.not_mem_nil hm
  obtain ⟨last, htail, _⟩ := Hereditary.FinePredecessor.stripLast_split tail hne
  have hp := SourceLocalization.nativePath_strict q root hi
  rw [hhead, List.map_cons] at hp
  have ht := (List.pairwise_cons.mp hp).2
  rw [htail, List.map_append, List.map_singleton] at ht
  have hlt : SourceLocalization.value q d < SourceLocalization.value q last :=
    (List.pairwise_append.mp ht).2.2 _ (List.mem_map.mpr ⟨d, hm, rfl⟩) _ List.mem_cons_self
  have hend : SourceLocalization.endpoint (SourceLocalization.nativePath q root) = last := by
    rw [hhead, htail]
    change SourceLocalization.endpoint ((SourceLocalization.baseRaw q :: stripLast tail) ++ [last]) = last
    exact endpoint_append_singleton _ _
  have hv : interpretation q last = interpretation q root := by
    simpa only [hend, SourceLocalization.value] using SourceLocalization.nativePath_end q root hi
  exact hlt.trans_eq hv

theorem multiplicative_prefix_lt (q current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck q current = true)
    (d : Nat) (hd : d ∈ stripLast (rawWord q current)) :
    interpretation q d < interpretation q current := by
  let root := SourceLocalization.RootAdapter.rootCode q current
  cases hs : select q current (table q (properPrefix q root)) with
  | none =>
    have hw : rawWord q current = [current] := by
      change extend q current (table q (properPrefix q root)) = [current]
      simp only [extend, hs]
    have hn : d ∈ ([] : List Nat) := by simpa only [hw, stripLast_singleton] using hd
    exact False.elim (List.not_mem_nil hn)
  | some e =>
    have hw : rawWord q current = e.2 ++ [current] := by
      change extend q current (table q (properPrefix q root)) = e.2 ++ [current]
      simp only [extend, hs]
    have he : d ∈ e.2 := by simpa only [hw, stripLast_append_singleton] using hd
    have hc := buildRev_word_mem q (properPrefix q root).reverse e (select_mem q current _ e hs) d he
    have hr := SourceLocalization.RootAdapter.rootInput q current
      (SourceMultiplicativePrincipal.rootAdapter_input q current hm)
    exact (properPrefix_lt_root q root hr d (List.mem_reverse.mp hc)).trans_eq
        (SourceLocalization.RootAdapter.rootCode_spec q current
          (SourceMultiplicativePrincipal.rootAdapter_input q current hm)).2

/-- Actual execution alone derives original LOW admission and the strict
epsilon interval for every written proper-prefix entry. -/
theorem execute_prefix_interval (q current : Nat) (out : List Nat)
    (ho : out ∈ Assignment.execute q current) :
    ∀ d ∈ stripLast out, lowCheckCode q d = true ∧ base q < interpretation q d ∧
      Ordinal.omega0 ^ interpretation q d = interpretation q d ∧
        interpretation q d < interpretation q current := by
  have ht := (SourceTrackingRaw.trackingCheck_conditions q out).mp
    (Assignment.execute_tracking q current out ho)
  have hc := (Assignment.inputCheck_exact q current).mp (Assignment.execute_spec q current out ho).1
  intro d hd
  have he := ht.2.1.epsilons d hd
  refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
  cases hm : SourceMultiplicativePrincipal.inputCheck q current with
  | true =>
    have hw : out = rawWord q current := Part.mem_unique ho (Assignment.execute_multiplicative q current hm)
    exact multiplicative_prefix_lt q current hm d (by simpa only [hw] using hd)
  | false =>
    have hle := (Assignment.execute_spec q current out ho).2.1.2.1 d
      (Hereditary.FinePredecessor.stripLast_mem out d hd)
    apply lt_of_le_of_ne hle
    intro hv
    have heps : Ordinal.omega0 ^ interpretation q current = interpretation q current := by
      rw [← hv]
      exact he.2.2.1
    have hmul := (SourceMultiplicativePrincipal.inputCheck_exact q current).mpr
      ⟨hc.1, hc.2.1, SourceMultiplicativePrincipal.epsilon_multiplicative _ heps⟩
    rw [hm] at hmul
    cases hmul

/-- This is genuine source3.21.3 in the original coded epsilon context;
the localization-subsequence clause remains a separate theorem. -/
theorem execute_proper_prefix (q current : Nat) (out : List Nat)
    (ho : out ∈ Assignment.execute q current) :
    ((stripLast out).map (interpretation q)).Pairwise (· < ·) ∧
      (∀ d ∈ stripLast out, base q < interpretation q d ∧
        interpretation q d < interpretation q current ∧
          Ordinal.omega0 ^ interpretation q d = interpretation q d) := by
  have hr := ((SourceTrackingRaw.trackingCheck_conditions q out).mp
    (Assignment.execute_tracking q current out ho)).2.1
  exact ⟨hr.strict, fun d hd =>
    let hs := execute_prefix_interval q current out ho d hd
    ⟨hs.2.1, hs.2.2.2, hs.2.2.1⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ProperPrefix
