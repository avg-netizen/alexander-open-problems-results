import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingValues

/-!
# Stored original table words and their actual localization prefixes

Every record in the executing finite table is the concrete extension at
its own earlier written input prefix. The proved VALUE-prefix locality of
the actual original localization identifies that earlier prefix with the
proper localization prefix at the recorded node. The actual covered-table
invariance then identifies the stored word values with the independently
computed word at that node. Written node spellings remain separate.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.RecurrenceSupport

open SourceMultiplicativeTracking.Support SourceMultiplicativeTracking.Values
open SourceTrackingSequences.Support PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast stripLast_split stripLast_mem)

/-- Every stored word was computed using exactly the earlier written
input prefix, not an assumed recursive tracking assignment. -/
theorem buildRev_entry_prefix (q : Nat) (xs : List Nat) (e : Entry)
    (hm : e ∈ buildRev q xs) :
    ∃ before after : List Nat, xs.reverse = before ++ e.1 :: after ∧
      e.2 = extend q e.1 (table q before) := by
  revert hm
  induction xs generalizing e with
  | nil => intro hm; exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    intro hm
    change e ∈ (current, extend q current (buildRev q rest)) :: buildRev q rest at hm
    rcases List.mem_cons.mp hm with he | he
    · subst e
      refine ⟨rest.reverse, [], ?_, ?_⟩
      · simp only [List.reverse_cons]
      · simp only [table, List.reverse_reverse]
    · obtain ⟨before, after, hp, hw⟩ := ih e he
      refine ⟨before, after ++ [current], ?_, hw⟩
      simp only [List.reverse_cons, hp, List.append_assoc, List.cons_append]

theorem table_entry_prefix (q : Nat) (xs : List Nat) (e : Entry)
    (hm : e ∈ table q xs) :
    ∃ before after : List Nat, xs = before ++ e.1 :: after ∧
      e.2 = extend q e.1 (table q before) := by
  simpa only [List.reverse_reverse] using buildRev_entry_prefix q xs.reverse e hm

/-- Erasing the base and final entry in the actual VALUE-prefix theorem
gives the complete independently localized proper prefix. -/
theorem properPrefix_value_prefix (q root : Nat)
    (hi : SourceLocalization.inputCheck q root = true)
    (before : List Nat) (d : Nat) (suffix : List Nat)
    (he : SourceLocalization.nativePath q root =
      (SourceLocalization.baseRaw q :: before) ++ d :: suffix) :
    before.map (interpretation q) = (properPrefix q d).map (interpretation q) := by
  have hp := SourceLocalization.Properties.nativePath_value_prefix q root hi
    (SourceLocalization.baseRaw q :: before) d suffix he
  calc
    before.map (interpretation q) =
        ((((SourceLocalization.baseRaw q :: before) ++ [d]).map (interpretation q)).tail).reverse.tail.reverse := by
      simp only [List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.tail_cons, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.reverse_reverse]
    _ = (((SourceLocalization.nativePath q d).map (interpretation q)).tail).reverse.tail.reverse :=
      congrArg (fun xs : List Ordinal.{0} => xs.tail.reverse.tail.reverse) hp
    _ = (properPrefix q d).map (interpretation q) := by
      simp only [properPrefix, stripLast, List.map_reverse, List.map_tail]

theorem properPrefix_split_path (q root : Nat) (before after : List Nat) (d : Nat)
    (hp : properPrefix q root = before ++ d :: after) :
    ∃ suffix : List Nat, SourceLocalization.nativePath q root =
      (SourceLocalization.baseRaw q :: before) ++ d :: suffix := by
  obtain ⟨tail, hh⟩ := SourceLocalization.nativePath_head q root
  have hm : d ∈ properPrefix q root := by
    rw [hp]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ht : tail ≠ [] := by
    intro he
    simp only [properPrefix, hh, List.tail_cons, he, stripLast, List.reverse_nil,
      List.tail_nil, List.not_mem_nil] at hm
  obtain ⟨last, hl, _⟩ := stripLast_split tail ht
  have hb : stripLast tail = before ++ d :: after := by
    simpa only [properPrefix, hh, List.tail_cons] using hp
  refine ⟨after ++ [last], ?_⟩
  rw [hh, hl, hb]
  simp only [List.cons_append, List.append_assoc]

/-- A record's actual stored word has exactly the values of the real
independently computed localization word at its genuine original node. -/
theorem table_entry_word (q root : Nat)
    (hi : SourceLocalization.inputCheck q root = true) (e : Entry)
    (hm : e ∈ table q (properPrefix q root)) :
    e.2.map (interpretation q) = (word q e.1).map (interpretation q) := by
  obtain ⟨before, after, hp, hw⟩ := table_entry_prefix q (properPrefix q root) e hm
  obtain ⟨suffix, hs⟩ := properPrefix_split_path q root before after e.1 hp
  have hprefix := properPrefix_value_prefix q root hi before e.1 suffix hs
  have hepath : e.1 ∈ SourceLocalization.nativePath q root := by
    rw [hs]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have he : SourceLocalization.inputCheck q e.1 = true :=
    (SourceLocalization.inputCheck_exact q e.1).mpr
      (SourceLocalization.nativePath_nodes q root hi e.1 hepath)
  have hb : ∀ c ∈ before, Mu.inputCheck q c = true := by
    intro c hc
    apply properPrefix_roots q root hi c
    rw [hp]
    exact List.mem_append.mpr (Or.inl hc)
  have hd := properPrefix_roots q e.1 he
  have ht := table_values q before (properPrefix q e.1) hb hd hprefix
  have hlow := SourceLocalization.node_low q e.1
    ((SourceLocalization.inputCheck_exact q e.1).mp he)
  rw [hw, word]
  exact extend_values q e.1 e.1 (table q before) (table q (properPrefix q e.1))
    (fun a ha => hb a.1 (List.mem_reverse.mp (buildRev_code_mem q before.reverse a ha)))
    (fun a ha => hd a.1 (List.mem_reverse.mp
      (buildRev_code_mem q (properPrefix q e.1).reverse a ha)))
    hlow hlow rfl ht

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.RecurrenceSupport
