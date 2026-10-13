import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingValues
import Alexander313.Wilken.PublicEpsilonNativeLocalizationValueInvariance

/-!
# Actual native tracking words are invariant in ordinal values

Actual cross-support localization and mu-cover/table invariance identify
the computed words at equally valued genuine original callers. At the
base value the proper prefix is empty, so the original code is returned
as the literal singleton. No path spelling or tracking oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Spelling

open Support Values PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast)

theorem properPrefix_values_eq (q c d : Nat)
    (hc : SourceLocalization.inputCheck q c = true)
    (hd : SourceLocalization.inputCheck q d = true)
    (he : interpretation q c = interpretation q d) :
    (properPrefix q c).map (interpretation q) =
      (properPrefix q d).map (interpretation q) := by
  have hp := SourceLocalization.ValueInvariance.nativePath_values_eq q c d hc hd he
  have ht := congrArg (fun xs : List Ordinal.{0} => xs.tail.reverse.tail.reverse) hp
  simpa only [SourceLocalization.value, properPrefix, stripLast,
    List.map_reverse, List.map_tail] using ht

theorem word_values_eq (q c d : Nat)
    (hc : SourceLocalization.inputCheck q c = true)
    (hd : SourceLocalization.inputCheck q d = true)
    (he : interpretation q c = interpretation q d) :
    (word q c).map (interpretation q) = (word q d).map (interpretation q) := by
  have hp := properPrefix_values_eq q c d hc hd he
  have hcr := properPrefix_roots q c hc
  have hdr := properPrefix_roots q d hd
  have ht := table_values q (properPrefix q c) (properPrefix q d) hcr hdr hp
  rw [word, word]
  exact extend_values q c d (table q (properPrefix q c)) (table q (properPrefix q d))
    (fun a ha => hcr a.1 (List.mem_reverse.mp
      (buildRev_code_mem q (properPrefix q c).reverse a ha)))
    (fun a ha => hdr a.1 (List.mem_reverse.mp
      (buildRev_code_mem q (properPrefix q d).reverse a ha)))
    (SourceLocalization.node_low q c ((SourceLocalization.inputCheck_exact q c).mp hc))
    (SourceLocalization.node_low q d ((SourceLocalization.inputCheck_exact q d).mp hd)) he ht

theorem rawWord_values_eq (q c d : Nat)
    (hc : SourceLocalization.RootAdapter.inputCheck q c = true)
    (hd : SourceLocalization.RootAdapter.inputCheck q d = true)
    (he : interpretation q c = interpretation q d) :
    (rawWord q c).map (interpretation q) = (rawWord q d).map (interpretation q) := by
  have hrc := SourceLocalization.RootAdapter.rootInput q c hc
  have hrd := SourceLocalization.RootAdapter.rootInput q d hd
  have hroots : interpretation q (SourceLocalization.RootAdapter.rootCode q c) =
      interpretation q (SourceLocalization.RootAdapter.rootCode q d) :=
    (SourceLocalization.RootAdapter.rootCode_spec q c hc).2.trans
      (he.trans (SourceLocalization.RootAdapter.rootCode_spec q d hd).2.symm)
  have hp := properPrefix_values_eq q _ _ hrc hrd hroots
  have hcr := properPrefix_roots q _ hrc
  have hdr := properPrefix_roots q _ hrd
  have ht := table_values q _ _ hcr hdr hp
  rw [rawWord, rawWord]
  exact extend_values q c d _ _
    (fun a ha => hcr a.1 (List.mem_reverse.mp
      (buildRev_code_mem q (properPrefix q (SourceLocalization.RootAdapter.rootCode q c)).reverse a ha)))
    (fun a ha => hdr a.1 (List.mem_reverse.mp
      (buildRev_code_mem q (properPrefix q (SourceLocalization.RootAdapter.rootCode q d)).reverse a ha)))
    ((SourceLocalization.RootAdapter.inputCheck_exact q c).mp hc).1
    ((SourceLocalization.RootAdapter.inputCheck_exact q d).mp hd).1 he ht

theorem properPrefix_at_base (q c : Nat)
    (hc : SourceLocalization.inputCheck q c = true)
    (he : interpretation q c = base q) : properPrefix q c = [] := by
  have hp := SourceLocalization.ValueInvariance.nativePath_base_values q c hc he
  have ht : (SourceLocalization.nativePath q c).tail.map (SourceLocalization.value q) = [] := by
    simpa only [List.map_tail, List.tail_cons, List.tail_nil] using congrArg List.tail hp
  have hn : (SourceLocalization.nativePath q c).tail = [] := List.eq_nil_of_map_eq_nil ht
  simp only [properPrefix, hn, stripLast, List.reverse_nil, List.tail_nil]

theorem word_at_base (q c : Nat) (hc : SourceLocalization.inputCheck q c = true)
    (he : interpretation q c = base q) : word q c = [c] := by
  simp only [word, properPrefix_at_base q c hc he, table, List.reverse_nil,
    buildRev, select, extend]

theorem rawWord_at_base (q c : Nat)
    (hc : SourceLocalization.RootAdapter.inputCheck q c = true)
    (he : interpretation q c = base q) : rawWord q c = [c] := by
  have hp := properPrefix_at_base q (SourceLocalization.RootAdapter.rootCode q c)
    (SourceLocalization.RootAdapter.rootInput q c hc)
    ((SourceLocalization.RootAdapter.rootCode_spec q c hc).2.trans he)
  simp only [rawWord, hp, table, List.reverse_nil, buildRev, select, extend]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Spelling
