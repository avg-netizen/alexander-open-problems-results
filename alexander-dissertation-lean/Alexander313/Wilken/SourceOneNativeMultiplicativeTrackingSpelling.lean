import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingValues

/-!
# Original source-one finite tracking words depend on their ordinal value

Actual ordinary localization value-path invariance gives equal proper
prefix values at equal-valued original source-zero roots. Genuine raw mu
cover and complete table invariance then give equal computed tracking word
values, also on arbitrary admitted raw principal spellings. The original
value-one boundary has an empty proper prefix and its exact singleton word.
No equality of written paths, representative or tracking oracle is used.
This does not implement the additive-principal Definition3.20 recurrence.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Spelling

open Support Values Prefix
open Hereditary.FinePredecessor (stripLast)

theorem properPrefix_values_eq (c d : Nat)
    (hc : Localization.inputCheck 0 c = true) (hd : Localization.inputCheck 0 d = true)
    (he : interpretation 0 c = interpretation 0 d) :
    (properPrefix c).map (interpretation 0) = (properPrefix d).map (interpretation 0) := by
  have hp := Localization.Order.values_eq_of_value_eq 0 c d
    ((Localization.inputCheck_exact 0 c).mp hc) ((Localization.inputCheck_exact 0 d).mp hd) he
  have ht := congrArg (fun xs : List Ordinal.{0} => xs.tail.reverse.tail.reverse) hp
  simpa only [Localization.Order.values, Localization.value, properPrefix, stripLast,
    List.map_reverse, List.map_tail] using ht

theorem word_values_eq (c d : Nat)
    (hc : Localization.inputCheck 0 c = true) (hd : Localization.inputCheck 0 d = true)
    (he : interpretation 0 c = interpretation 0 d) :
    (word c).map (interpretation 0) = (word d).map (interpretation 0) := by
  have hp := properPrefix_values_eq c d hc hd he
  have hcr := properPrefix_raw c hc
  have hdr := properPrefix_raw d hd
  have ht := table_values (properPrefix c) (properPrefix d) hcr hdr hp
  rw [word, word]
  exact extend_values c d (table (properPrefix c)) (table (properPrefix d))
    (fun a ha => hcr a.1 (List.mem_reverse.mp (buildRev_code_mem (properPrefix c).reverse a ha)))
    (fun a ha => hdr a.1 (List.mem_reverse.mp (buildRev_code_mem (properPrefix d).reverse a ha)))
    (Localization.node_low 0 c ((Localization.inputCheck_exact 0 c).mp hc))
    (Localization.node_low 0 d ((Localization.inputCheck_exact 0 d).mp hd)) he ht

theorem rawWord_values_eq (c d : Nat)
    (hc : SourceLocalization.RootAdapter.inputCheck c = true)
    (hd : SourceLocalization.RootAdapter.inputCheck d = true)
    (he : interpretation 0 c = interpretation 0 d) :
    (rawWord c).map (interpretation 0) = (rawWord d).map (interpretation 0) := by
  have hrc := SourceLocalization.RootAdapter.rootInput c hc
  have hrd := SourceLocalization.RootAdapter.rootInput d hd
  have hroots : interpretation 0 (SourceLocalization.RootAdapter.rootCode c) =
      interpretation 0 (SourceLocalization.RootAdapter.rootCode d) :=
    (SourceLocalization.RootAdapter.rootCode_value c hc).trans
      (he.trans (SourceLocalization.RootAdapter.rootCode_value d hd).symm)
  have hp := properPrefix_values_eq _ _ hrc hrd hroots
  have hcr := properPrefix_raw _ hrc
  have hdr := properPrefix_raw _ hrd
  have ht := table_values _ _ hcr hdr hp
  rw [rawWord, rawWord]
  exact extend_values c d _ _
    (fun a ha => hcr a.1 (List.mem_reverse.mp
      (buildRev_code_mem (properPrefix (SourceLocalization.RootAdapter.rootCode c)).reverse a ha)))
    (fun a ha => hdr a.1 (List.mem_reverse.mp
      (buildRev_code_mem (properPrefix (SourceLocalization.RootAdapter.rootCode d)).reverse a ha)))
    ((SourceLocalization.RootAdapter.inputCheck_exact c).mp hc).1
    ((SourceLocalization.RootAdapter.inputCheck_exact d).mp hd).1 he ht

theorem properPrefix_at_one (c : Nat) (hc : Localization.inputCheck 0 c = true)
    (he : interpretation 0 c = 1) : properPrefix c = [] := by
  have hp := Localization.Order.base_selectedValues 0 c ((Localization.inputCheck_exact 0 c).mp hc)
    (by simpa only [Localization.value, finiteBase_zero] using he)
  have ht : (Localization.nativePath 0 c).tail = [] := List.eq_nil_of_map_eq_nil hp
  simp only [properPrefix, ht, stripLast, List.reverse_nil, List.tail_nil]

theorem word_at_one (c : Nat) (hc : Localization.inputCheck 0 c = true)
    (he : interpretation 0 c = 1) : word c = [c] := by
  simp only [word, properPrefix_at_one c hc he, table, List.reverse_nil, buildRev, select, extend]

theorem rawWord_at_one (c : Nat) (hc : SourceLocalization.RootAdapter.inputCheck c = true)
    (he : interpretation 0 c = 1) : rawWord c = [c] := by
  have hp := properPrefix_at_one (SourceLocalization.RootAdapter.rootCode c)
    (SourceLocalization.RootAdapter.rootInput c hc)
    ((SourceLocalization.RootAdapter.rootCode_value c hc).trans he)
  simp only [rawWord, hp, table, List.reverse_nil, buildRev, select, extend]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Spelling
