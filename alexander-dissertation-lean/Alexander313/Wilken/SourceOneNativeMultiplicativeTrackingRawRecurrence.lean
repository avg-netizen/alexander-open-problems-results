import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingRecurrence
import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingSpelling

/-!
# The original raw source-one procedure obeys its own endpoint recurrence

The real original final-atom parser preserves every original localization
Node value. Actual table and path value invariance identify its raw input
word with the independently localized Node word. Consequently the selected
branch recurses to the SAME raw input procedure at its actual endpoint.
This is a fidelity equation between two genuine executing finite words,
not a supplied tracking assignment or equality of written paths. No Native
base-one parser, endpoint oracle or Definition3.20 step is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.RawRecurrence

open Support Prefix

theorem rawWord_values_word (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    (rawWord root).map (interpretation 0) = (word root).map (interpretation 0) := by
  have hs := node_principal_spec root ((Localization.inputCheck_exact 0 root).mp hi)
  have ha : SourceLocalization.RootAdapter.inputCheck root = true :=
    (SourceLocalization.RootAdapter.inputCheck_exact root).mpr ⟨hs.1, hs.2.2.2, hs.2.2.1⟩
  have hp := SourceLocalization.RootAdapter.rootCode_spec root ha
  have hpi := SourceLocalization.RootAdapter.rootInput root ha
  have hr := properPrefix_raw _ hpi
  have he : (rawWord root).map (interpretation 0) =
      (word (SourceLocalization.RootAdapter.rootCode root)).map (interpretation 0) := by
    exact Values.extend_values root (SourceLocalization.RootAdapter.rootCode root)
      (table (properPrefix (SourceLocalization.RootAdapter.rootCode root)))
      (table (properPrefix (SourceLocalization.RootAdapter.rootCode root)))
      (fun e hm => hr e.1 (List.mem_reverse.mp
        (buildRev_code_mem (properPrefix (SourceLocalization.RootAdapter.rootCode root)).reverse e hm)))
      (fun e hm => hr e.1 (List.mem_reverse.mp
        (buildRev_code_mem (properPrefix (SourceLocalization.RootAdapter.rootCode root)).reverse e hm)))
      hs.1 (Localization.node_low 0 _ hp.1) hp.2.symm rfl
  exact he.trans (Spelling.word_values_eq _ root hpi hi hp.2)

/-- The actual raw procedure satisfies the selected-endpoint recursion
using its own independently computed raw endpoint procedure. -/
theorem rawWord_some_values (current : Nat) (e : Entry)
    (hi : SourceMultiplicativePrincipal.inputCheck current = true)
    (hs : select current (table (properPrefix (SourceLocalization.RootAdapter.rootCode current))) = some e) :
    (rawWord current).map (interpretation 0) =
      (rawWord e.1).map (interpretation 0) ++ [interpretation 0 current] := by
  have hselected := Recurrence.selected_node current
    (SourceLocalization.RootAdapter.rootCode current) e
    (SourceMultiplicativePrincipal.rootInput current hi) hs
  obtain ⟨a, he, ht, hn, _⟩ := (rootCheck_exact e.1).mp hselected.2.1
  have hei : Localization.inputCheck 0 e.1 = true :=
    (Localization.inputCheck_exact 0 e.1).mpr ⟨a, he, ht, hn⟩
  have hraw := rawWord_values_word e.1 hei
  calc
    (rawWord current).map (interpretation 0) =
        (word e.1).map (interpretation 0) ++ [interpretation 0 current] :=
      (Recurrence.rawWord_some_spec current e hi hs).2.2.2.2.2
    _ = (rawWord e.1).map (interpretation 0) ++ [interpretation 0 current] :=
      congrArg (fun xs : List Ordinal.{0} => xs ++ [interpretation 0 current]) hraw.symm

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.RawRecurrence
