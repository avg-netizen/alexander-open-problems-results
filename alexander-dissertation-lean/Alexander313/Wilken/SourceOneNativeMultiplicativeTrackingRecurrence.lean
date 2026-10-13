import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingRecurrenceSupport
import Alexander313.Wilken.SourceOneNativeMultiplicativePrincipal

/-!
# Genuine original source-one multiplicative tracking recurrence

The actual covered table selects the greatest covered proper localization
position and its stored word has the values of the independently localized
word at that endpoint. Genuine original source-one raw mu spelling fidelity
converts each cover test to the printed actual mu. The selected endpoint's
proper prefix is strictly shorter. All original raw multiplicative callers
including one retain their unchanged final code; the strictly above-one
subdomain realizes Definition3.19. Boundary extension and Definition3.20
remain separate. No Native base-one parser or assigned recurrence is used.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Recurrence

open Support RecurrenceSupport Prefix
open SourceTrackingRaw.Support (coverCheck coverCheck_exact)

theorem properPrefix_muValue (root : Nat) (hi : Localization.inputCheck 0 root = true)
    (d : Nat) (hd : d ∈ properPrefix root) :
    SourceTrackingRaw.Support.muValue d = Mu.sourceValue d :=
  SourceTrackingRaw.Support.muValue_eq d d (properPrefix_raw root hi d hd)
    (properPrefix_high root hi d hd) rfl

theorem table_values_strict (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ((table (properPrefix root)).map (fun e => interpretation 0 e.1)).Pairwise
      (fun a b => b < a) := by
  have he := congrArg (fun xs : List Nat => xs.map (interpretation 0))
    (table_codes (properPrefix root))
  have hm : (table (properPrefix root)).map (fun e => interpretation 0 e.1) =
      (properPrefix root).reverse.map (interpretation 0) := by
    simpa only [List.map_map, Function.comp_def] using he
  rw [hm]
  exact properPrefix_reverse_strict root hi

theorem selected_node (current root : Nat) (e : Entry)
    (hi : Localization.inputCheck 0 root = true)
    (hs : select current (table (properPrefix root)) = some e) :
    e.1 ∈ properPrefix root ∧ Mu.inputCheck e.1 = true ∧
      interpretation 0 current ≤ Mu.sourceValue e.1 := by
  have hm := select_mem current _ e hs
  have hc := List.mem_reverse.mp (buildRev_code_mem (properPrefix root).reverse e hm)
  have hcover := ((coverCheck_exact e.1 current).mp (select_cover current _ e hs)).2.2
  rw [properPrefix_muValue root hi e.1 hc] at hcover
  exact ⟨hc, properPrefix_high root hi e.1 hc, hcover⟩

theorem selected_greatest (current root : Nat) (e : Entry)
    (hi : Localization.inputCheck 0 root = true) (hl : lowCheckCode 0 current = true)
    (hs : select current (table (properPrefix root)) = some e) :
    ∀ d ∈ properPrefix root, interpretation 0 current ≤ Mu.sourceValue d →
      interpretation 0 d ≤ interpretation 0 e.1 := by
  have hg := select_greatest current (table (properPrefix root)) e (table_values_strict root hi) hs
  intro d hd hc
  have hm : d ∈ (table (properPrefix root)).map Prod.fst := by
    rw [table_codes]
    exact List.mem_reverse.mpr hd
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
  have hcover : coverCheck a.1 current = true := by
    rw [he]
    apply (coverCheck_exact d current).mpr
    refine ⟨properPrefix_raw root hi d hd, hl, ?_⟩
    rw [properPrefix_muValue root hi d hd]
    exact hc
  simpa only [he] using hg a ha hcover

theorem selected_none_iff_no_cover (current root : Nat)
    (hi : Localization.inputCheck 0 root = true) (hl : lowCheckCode 0 current = true) :
    select current (table (properPrefix root)) = none ↔
      ∀ d ∈ properPrefix root, Mu.sourceValue d < interpretation 0 current := by
  rw [select_none]
  constructor
  · intro hn d hd
    apply lt_of_not_ge
    intro hcover
    have hm : d ∈ (table (properPrefix root)).map Prod.fst := by
      rw [table_codes]
      exact List.mem_reverse.mpr hd
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    have hp : coverCheck a.1 current = true := by
      rw [he]
      apply (coverCheck_exact d current).mpr
      refine ⟨properPrefix_raw root hi d hd, hl, ?_⟩
      rw [properPrefix_muValue root hi d hd]
      exact hcover
    rw [hn a ha] at hp
    cases hp
  · intro hn e he
    apply Bool.eq_false_of_not_eq_true
    intro hp
    have hd := List.mem_reverse.mp (buildRev_code_mem (properPrefix root).reverse e he)
    have hcover := ((coverCheck_exact e.1 current).mp hp).2.2
    rw [properPrefix_muValue root hi e.1 hd] at hcover
    exact (hn e.1 hd).not_ge hcover

theorem selected_prefix_shorter (current root : Nat) (e : Entry)
    (hi : Localization.inputCheck 0 root = true)
    (hs : select current (table (properPrefix root)) = some e) :
    (properPrefix e.1).length < (properPrefix root).length := by
  obtain ⟨before, after, hp, _⟩ := table_entry_prefix (properPrefix root) e
    (select_mem current _ e hs)
  obtain ⟨suffix, he⟩ := properPrefix_split_path root before after e.1 hp
  have hv := properPrefix_value_prefix root hi before e.1 suffix he
  have hlen : before.length = (properPrefix e.1).length := by
    simpa only [List.length_map] using congrArg List.length hv
  rw [hp, List.length_append, List.length_cons]
  omega

theorem extend_none (current root : Nat)
    (hs : select current (table (properPrefix root)) = none) :
    extend current (table (properPrefix root)) = [current] := by
  simp only [extend, hs]

theorem extend_some_values (current root : Nat) (e : Entry)
    (hi : Localization.inputCheck 0 root = true)
    (hs : select current (table (properPrefix root)) = some e) :
    (extend current (table (properPrefix root))).map (interpretation 0) =
      (word e.1).map (interpretation 0) ++ [interpretation 0 current] := by
  have hw := table_entry_word root hi e (select_mem current _ e hs)
  simp only [extend, hs, List.map_append, List.map_singleton, hw]

theorem word_none (root : Nat) (hs : select root (table (properPrefix root)) = none) :
    word root = [root] := extend_none root root hs

theorem word_some_values (root : Nat) (e : Entry) (hi : Localization.inputCheck 0 root = true)
    (hs : select root (table (properPrefix root)) = some e) :
    (word root).map (interpretation 0) =
      (word e.1).map (interpretation 0) ++ [interpretation 0 root] :=
  extend_some_values root root e hi hs

theorem rawWord_some_spec (current : Nat) (e : Entry)
    (hi : SourceMultiplicativePrincipal.inputCheck current = true)
    (hs : select current (table (properPrefix (SourceLocalization.RootAdapter.rootCode current))) = some e) :
    Mu.inputCheck e.1 = true ∧
      MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 e.1) ∧
      interpretation 0 current ≤ Mu.sourceValue e.1 ∧
      (∀ d ∈ properPrefix (SourceLocalization.RootAdapter.rootCode current),
        interpretation 0 current ≤ Mu.sourceValue d → interpretation 0 d ≤ interpretation 0 e.1) ∧
      (properPrefix e.1).length <
        (properPrefix (SourceLocalization.RootAdapter.rootCode current)).length ∧
      (rawWord current).map (interpretation 0) =
        (word e.1).map (interpretation 0) ++ [interpretation 0 current] := by
  have hr := SourceMultiplicativePrincipal.rootInput current hi
  have hc := (SourceMultiplicativePrincipal.inputCheck_exact current).mp hi
  have he := selected_node current (SourceLocalization.RootAdapter.rootCode current) e hr hs
  have heps := root_epsilon e.1 he.2.1
  have hmul : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 e.1) := by
    apply (MultiplicativePrincipalArithmetic.multiplicativePrincipal_iff _).mpr
    refine Or.inr ⟨interpretation 0 e.1, ?_⟩
    calc
      interpretation 0 e.1 = Ordinal.omega0 ^ interpretation 0 e.1 := heps.symm
      _ = Ordinal.omega0 ^ (Ordinal.omega0 ^ interpretation 0 e.1) :=
        congrArg (fun v : Ordinal.{0} => Ordinal.omega0 ^ v) heps.symm
  refine ⟨he.2.1, hmul, he.2.2, selected_greatest current _ e hr hc.1 hs,
    selected_prefix_shorter current _ e hr hs, ?_⟩
  exact extend_some_values current _ e hr hs

theorem rawWord_none (current : Nat)
    (hs : select current (table (properPrefix (SourceLocalization.RootAdapter.rootCode current))) = none) :
    rawWord current = [current] := extend_none current _ hs

theorem rawWord_multiplicative_checked (current : Nat)
    (hi : SourceMultiplicativePrincipal.inputCheck current = true) :
    SourceTrackingRaw.trackingCheck (rawWord current) = true ∧
      NativeContext.SourceTrackingSequences.lastCode (rawWord current) = current :=
  ⟨rawWord_checked current (SourceMultiplicativePrincipal.rootAdapter_input current hi),
    rawWord_last current⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Recurrence
