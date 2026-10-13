import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingRecurrence
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingSpelling

/-!
# The actual native raw procedure obeys its own endpoint recurrence

The real original final-atom parser, path and table invariance identify
raw and independently localized Node words in ordinal values. The selected
branch thus invokes the SAME raw numerical procedure at its actual endpoint.
No supplied recursive assignment, spelling equality or new caller. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.RawRecurrence

open Support PublicEpsilonUnboundedIota

theorem rawWord_values_word (q root : Nat)
    (hi : SourceLocalization.inputCheck q root = true) :
    (rawWord q root).map (interpretation q) = (word q root).map (interpretation q) := by
  have hs := node_principal_spec q root ((SourceLocalization.inputCheck_exact q root).mp hi)
  have ha : SourceLocalization.RootAdapter.inputCheck q root = true :=
    (SourceLocalization.RootAdapter.inputCheck_exact q root).mpr ⟨hs.1, hs.2.2.2, hs.2.2.1⟩
  have hp := SourceLocalization.RootAdapter.rootCode_spec q root ha
  have hpi := SourceLocalization.RootAdapter.rootInput q root ha
  have hr := properPrefix_roots q _ hpi
  have he : (rawWord q root).map (interpretation q) =
      (word q (SourceLocalization.RootAdapter.rootCode q root)).map (interpretation q) := by
    exact Values.extend_values q root (SourceLocalization.RootAdapter.rootCode q root)
      (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q root)))
      (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q root)))
      (fun e hm => hr e.1 (List.mem_reverse.mp
        (buildRev_code_mem q (properPrefix q (SourceLocalization.RootAdapter.rootCode q root)).reverse e hm)))
      (fun e hm => hr e.1 (List.mem_reverse.mp
        (buildRev_code_mem q (properPrefix q (SourceLocalization.RootAdapter.rootCode q root)).reverse e hm)))
      hs.1 (SourceLocalization.node_low q _ hp.1) hp.2.symm rfl
  exact he.trans (Spelling.word_values_eq q _ root hpi hi hp.2)

/-- The selected branch recurses through the actual independently computed
raw endpoint word, preserving the printed equation in original values. -/
theorem rawWord_some_values (q current : Nat) (e : Entry)
    (hi : SourceMultiplicativePrincipal.inputCheck q current = true)
    (hs : select q current
      (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q current))) = some e) :
    (rawWord q current).map (interpretation q) =
      (rawWord q e.1).map (interpretation q) ++ [interpretation q current] := by
  have hselected := Recurrence.selected_node q current
    (SourceLocalization.RootAdapter.rootCode q current) e
    (SourceMultiplicativePrincipal.rootInput q current hi) hs
  obtain ⟨a, he, ht, hn, _⟩ := (RootLowCollapse.rootCheck_exact q e.1).mp hselected.2.1
  have hei : SourceLocalization.inputCheck q e.1 = true :=
    (SourceLocalization.inputCheck_exact q e.1).mpr ⟨a, he, ht, hn⟩
  have hraw := rawWord_values_word q e.1 hei
  calc
    (rawWord q current).map (interpretation q) =
        (word q e.1).map (interpretation q) ++ [interpretation q current] :=
      (Recurrence.rawWord_some_spec q current e hi hs).2.2.2.2.2
    _ = (rawWord q e.1).map (interpretation q) ++ [interpretation q current] :=
      congrArg (fun xs : List Ordinal.{0} => xs ++ [interpretation q current]) hraw.symm

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.RawRecurrence
