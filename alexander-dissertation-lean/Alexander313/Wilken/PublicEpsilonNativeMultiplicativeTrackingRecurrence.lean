import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingRecurrenceSupport
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativePrincipal

/-!
# The actual source3.19 recursive equation on original relative M callers

The executing table selects the greatest covered proper localization
position. Its stored word is now identified with the actual independently
localized word at that selected node. Thus the computed finite word obeys
the printed recursive equation in original ordinal values. The earlier
prefix is strictly shorter, giving the actual localization-length descent.
The raw M caller derives every original principal/localization/high-root
guard and retains its original final code. Boundary/global extensions and
the additive-principal factor/insertion assignment remain separate.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Recurrence

open Support RecurrenceSupport
open SourceTrackingSequences.Support PublicEpsilonUnboundedIota

theorem table_values_strict (q root : Nat)
    (hi : SourceLocalization.inputCheck q root = true) :
    ((table q (properPrefix q root)).map (fun e => interpretation q e.1)).Pairwise
      (fun a b => b < a) := by
  have he := congrArg (fun xs : List Nat => xs.map (interpretation q))
    (table_codes q (properPrefix q root))
  have hm : (table q (properPrefix q root)).map (fun e => interpretation q e.1) =
      (properPrefix q root).reverse.map (interpretation q) := by
    simpa only [List.map_map, Function.comp_def] using he
  rw [hm]
  exact properPrefix_reverse_strict q root hi

theorem selected_node (q current root : Nat) (e : Entry)
    (hi : SourceLocalization.inputCheck q root = true)
    (hs : select q current (table q (properPrefix q root)) = some e) :
    e.1 ∈ properPrefix q root ∧ Mu.inputCheck q e.1 = true ∧
      interpretation q current ≤ Mu.sourceValue q e.1 := by
  have hm := select_mem q current _ e hs
  have hc := List.mem_reverse.mp (buildRev_code_mem q (properPrefix q root).reverse e hm)
  exact ⟨hc, properPrefix_roots q root hi e.1 hc,
    ((coverCheck_exact q e.1 current).mp (select_cover q current _ e hs)).2.2⟩

theorem selected_greatest (q current root : Nat) (e : Entry)
    (hi : SourceLocalization.inputCheck q root = true)
    (hl : lowCheckCode q current = true)
    (hs : select q current (table q (properPrefix q root)) = some e) :
    ∀ d ∈ properPrefix q root, interpretation q current ≤ Mu.sourceValue q d →
      interpretation q d ≤ interpretation q e.1 := by
  have hg := select_greatest q current (table q (properPrefix q root)) e
    (table_values_strict q root hi) hs
  intro d hd hc
  have hm : d ∈ (table q (properPrefix q root)).map Prod.fst := by
    rw [table_codes]
    exact List.mem_reverse.mpr hd
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
  have hcover : coverCheck q a.1 current = true := by
    rw [he]
    exact (coverCheck_exact q d current).mpr ⟨properPrefix_roots q root hi d hd, hl, hc⟩
  simpa only [he] using hg a ha hcover

theorem selected_none_iff_no_cover (q current root : Nat)
    (hi : SourceLocalization.inputCheck q root = true)
    (hl : lowCheckCode q current = true) :
    select q current (table q (properPrefix q root)) = none ↔
      ∀ d ∈ properPrefix q root, Mu.sourceValue q d < interpretation q current := by
  rw [select_none]
  constructor
  · intro hn d hd
    apply lt_of_not_ge
    intro hcover
    have hm : d ∈ (table q (properPrefix q root)).map Prod.fst := by
      rw [table_codes]
      exact List.mem_reverse.mpr hd
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    have hp : coverCheck q a.1 current = true := by
      rw [he]
      exact (coverCheck_exact q d current).mpr ⟨properPrefix_roots q root hi d hd, hl, hcover⟩
    rw [hn a ha] at hp
    cases hp
  · intro hn e he
    apply Bool.eq_false_of_not_eq_true
    intro hp
    have hd := List.mem_reverse.mp (buildRev_code_mem q (properPrefix q root).reverse e he)
    exact (hn e.1 hd).not_ge ((coverCheck_exact q e.1 current).mp hp).2.2

/-- The recursive caller is an actual earlier localization prefix.
Its strict length decrease follows from the literal stored prefix and
the independently proved VALUE-prefix equality. -/
theorem selected_prefix_shorter (q current root : Nat) (e : Entry)
    (hi : SourceLocalization.inputCheck q root = true)
    (hs : select q current (table q (properPrefix q root)) = some e) :
    (properPrefix q e.1).length < (properPrefix q root).length := by
  obtain ⟨before, after, hp, _⟩ := table_entry_prefix q (properPrefix q root) e
    (select_mem q current _ e hs)
  obtain ⟨suffix, he⟩ := properPrefix_split_path q root before after e.1 hp
  have hv := properPrefix_value_prefix q root hi before e.1 suffix he
  have hlen : before.length = (properPrefix q e.1).length := by
    simpa only [List.length_map] using congrArg List.length hv
  rw [hp, List.length_append, List.length_cons]
  omega

theorem extend_none (q current root : Nat)
    (hs : select q current (table q (properPrefix q root)) = none) :
    extend q current (table q (properPrefix q root)) = [current] := by
  simp only [extend, hs]

/-- The actual stored word equals the independently constructed word
at the selected endpoint in ordinal values, yielding source3.19. -/
theorem extend_some_values (q current root : Nat) (e : Entry)
    (hi : SourceLocalization.inputCheck q root = true)
    (hs : select q current (table q (properPrefix q root)) = some e) :
    (extend q current (table q (properPrefix q root))).map (interpretation q) =
      (word q e.1).map (interpretation q) ++ [interpretation q current] := by
  have hw := table_entry_word q root hi e (select_mem q current _ e hs)
  simp only [extend, hs, List.map_append, List.map_singleton, hw]

theorem word_none (q root : Nat)
    (hs : select q root (table q (properPrefix q root)) = none) : word q root = [root] :=
  extend_none q root root hs

theorem word_some_values (q root : Nat) (e : Entry)
    (hi : SourceLocalization.inputCheck q root = true)
    (hs : select q root (table q (properPrefix q root)) = some e) :
    (word q root).map (interpretation q) =
      (word q e.1).map (interpretation q) ++ [interpretation q root] :=
  extend_some_values q root root e hi hs

/-- The genuine raw M caller supplies the independently localized
selected endpoint, covering maximality and the strict recursive decrease.
Only the original computed multiplicative-principal guard is assumed. -/
theorem rawWord_some_spec (q current : Nat) (e : Entry)
    (hi : SourceMultiplicativePrincipal.inputCheck q current = true)
    (hs : select q current
      (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q current))) = some e) :
    Mu.inputCheck q e.1 = true ∧
      MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q e.1) ∧
      interpretation q current ≤ Mu.sourceValue q e.1 ∧
      (∀ d ∈ properPrefix q (SourceLocalization.RootAdapter.rootCode q current),
        interpretation q current ≤ Mu.sourceValue q d → interpretation q d ≤ interpretation q e.1) ∧
      (properPrefix q e.1).length <
        (properPrefix q (SourceLocalization.RootAdapter.rootCode q current)).length ∧
      (rawWord q current).map (interpretation q) =
        (word q e.1).map (interpretation q) ++ [interpretation q current] := by
  have hr := SourceMultiplicativePrincipal.rootInput q current hi
  have hc := (SourceMultiplicativePrincipal.inputCheck_exact q current).mp hi
  have he := selected_node q current (SourceLocalization.RootAdapter.rootCode q current) e hr hs
  refine ⟨he.2.1, SourceMultiplicativePrincipal.epsilon_multiplicative _
    (RootLowCollapse.root_epsilon q e.1 he.2.1), he.2.2,
    selected_greatest q current _ e hr hc.1 hs,
    selected_prefix_shorter q current _ e hr hs, ?_⟩
  exact extend_some_values q current _ e hr hs

theorem rawWord_none (q current : Nat)
    (hs : select q current
      (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q current))) = none) :
    rawWord q current = [current] :=
  extend_none q current _ hs

/-- The complete concrete relative M procedure also has its actual
tracking-image and unchanged final-code certificate. This does not
identify its wider P-domain image with Definition3.20. -/
theorem rawWord_multiplicative_checked (q current : Nat)
    (hi : SourceMultiplicativePrincipal.inputCheck q current = true) :
    SourceTrackingSequences.trackingCheck q (rawWord q current) = true ∧
      SourceTrackingSequences.lastCode (rawWord q current) = current :=
  ⟨rawWord_checked q current (SourceMultiplicativePrincipal.rootAdapter_input q current hi),
    rawWord_last q current⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Recurrence
