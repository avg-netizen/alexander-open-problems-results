import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignment

/-!
# Genuine strict epsilon prefix of the original source-one assignment

The real original RAW Reference supplies strict epsilon prefix values.
Multiplicative leaves use the actual strict localization path and its true
endpoint value. For a nonmultiplicative input, equality with any prefix
epsilon would force the real multiplicative input checker, contradicting
the actual branch. Every proper entry therefore lies strictly between
one and the unchanged original input. No prefix or endpoint bound is an
additional premise; original check zero is retained. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ProperPrefix

open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (stripLast_singleton stripLast_append_singleton)
open SourceMultiplicativeTracking SourceMultiplicativeTracking.Support SourceMultiplicativeTracking.Prefix

private theorem endpoint_append_singleton (xs : List Nat) (d : Nat) :
    Localization.endpoint (xs ++ [d]) = d := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => exact ih

/-- Removing the true last path node leaves values strictly below the
actual original root value, not merely its written endpoint spelling. -/
theorem properPrefix_lt_root (root : Nat) (hi : Localization.inputCheck 0 root = true)
    (d : Nat) (hd : d ∈ properPrefix root) : interpretation 0 d < interpretation 0 root := by
  obtain ⟨tail, hhead⟩ := Localization.nativePath_head 0 root
  have hm : d ∈ stripLast tail := by simpa only [properPrefix, hhead, List.tail_cons] using hd
  have hne : tail ≠ [] := by
    intro he
    subst tail
    exact List.not_mem_nil hm
  obtain ⟨last, htail, _⟩ := Hereditary.FinePredecessor.stripLast_split tail hne
  have hp := Localization.nativePath_strict 0 root hi
  rw [hhead, List.map_cons] at hp
  have ht := (List.pairwise_cons.mp hp).2
  rw [htail, List.map_append, List.map_singleton] at ht
  have hlt : Localization.value 0 d < Localization.value 0 last :=
    (List.pairwise_append.mp ht).2.2 _ (List.mem_map.mpr ⟨d, hm, rfl⟩) _ List.mem_cons_self
  have hend : Localization.endpoint (Localization.nativePath 0 root) = last := by
    rw [hhead, htail]
    change Localization.endpoint ((Localization.baseRaw 0 :: stripLast tail) ++ [last]) = last
    exact endpoint_append_singleton _ _
  have hv : interpretation 0 last = interpretation 0 root := by
    simpa only [hend, Localization.value] using Localization.nativePath_end 0 root hi
  exact hlt.trans_eq hv

theorem multiplicative_prefix_lt (current : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck current = true)
    (d : Nat) (hd : d ∈ stripLast (rawWord current)) :
    interpretation 0 d < interpretation 0 current := by
  let root := SourceLocalization.RootAdapter.rootCode current
  cases hs : select current (table (properPrefix root)) with
  | none =>
    have hw : rawWord current = [current] := by
      change extend current (table (properPrefix root)) = [current]
      simp only [extend, hs]
    have hn : d ∈ ([] : List Nat) := by simpa only [hw, stripLast_singleton] using hd
    exact False.elim (List.not_mem_nil hn)
  | some e =>
    have hw : rawWord current = e.2 ++ [current] := by
      change extend current (table (properPrefix root)) = e.2 ++ [current]
      simp only [extend, hs]
    have he : d ∈ e.2 := by
      simpa only [hw, stripLast_append_singleton] using hd
    have hc := buildRev_word_mem (properPrefix root).reverse e (select_mem current _ e hs) d he
    exact (properPrefix_lt_root root (SourceMultiplicativePrincipal.rootInput current hm)
      d (List.mem_reverse.mp hc)).trans_eq
        (SourceLocalization.RootAdapter.rootCode_value current
          (SourceMultiplicativePrincipal.rootAdapter_input current hm))

private theorem epsilon_is_multiplicative (v : Ordinal.{0})
    (he : Ordinal.omega0 ^ v = v) : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal v := by
  apply (MultiplicativePrincipalArithmetic.multiplicativePrincipal_iff v).mpr
  refine Or.inr ⟨v, ?_⟩
  calc
    v = Ordinal.omega0 ^ v := he.symm
    _ = Ordinal.omega0 ^ (Ordinal.omega0 ^ v) := congrArg (fun x : Ordinal.{0} => Ordinal.omega0 ^ x) he.symm

/-- Actual complete execution derives the strict proper epsilon interval
and its original raw LOW admission for every written prefix entry. -/
theorem execute_prefix_interval (current : Nat) (out : List Nat) (ho : out ∈ Assignment.execute current) :
    ∀ d ∈ stripLast out, lowCheckCode 0 d = true ∧ 1 < interpretation 0 d ∧
      Ordinal.omega0 ^ interpretation 0 d = interpretation 0 d ∧
        interpretation 0 d < interpretation 0 current := by
  have ht := (SourceTrackingRaw.trackingCheck_exact out).mp (Assignment.execute_tracking current out ho)
  have hc := (Assignment.inputCheck_exact current).mp (Assignment.execute_spec current out ho).1
  intro d hd
  have he := ht.2.1.epsilons d hd
  refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
  cases hm : SourceMultiplicativePrincipal.inputCheck current with
  | true =>
    have hw : out = rawWord current := Part.mem_unique ho (Assignment.execute_multiplicative current hm)
    exact multiplicative_prefix_lt current hm d (by simpa only [hw] using hd)
  | false =>
    have hle := Assignment.execute_all_bounds current out ho d (Hereditary.FinePredecessor.stripLast_mem out d hd)
    apply lt_of_le_of_ne hle
    intro hv
    have hinput : Ordinal.omega0 ^ interpretation 0 current = interpretation 0 current := by
      rw [← hv]
      exact he.2.2.1
    have hmul := (SourceMultiplicativePrincipal.inputCheck_exact current).mpr
      ⟨hc.1, hc.2.1, epsilon_is_multiplicative _ hinput⟩
    rw [hm] at hmul
    cases hmul

/-- This is the actual original-source-one3.21.3 statement: the proper
prefix is empty or a strictly increasing epsilon sequence in (1,input). -/
theorem execute_proper_prefix (current : Nat) (out : List Nat) (ho : out ∈ Assignment.execute current) :
    ((stripLast out).map (interpretation 0)).Pairwise (· < ·) ∧
      (∀ d ∈ stripLast out, 1 < interpretation 0 d ∧
        interpretation 0 d < interpretation 0 current ∧
          Ordinal.omega0 ^ interpretation 0 d = interpretation 0 d) := by
  have hr := ((SourceTrackingRaw.trackingCheck_exact out).mp (Assignment.execute_tracking current out ho)).2.1
  exact ⟨hr.strict, fun d hd =>
    let hs := execute_prefix_interval current out ho d hd
    ⟨hs.2.1, hs.2.2.2, hs.2.2.1⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ProperPrefix
