import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingValues

/-!
# Actual original source-one stored words at their localization endpoints

Each record of the literal finite covered table is the actual extension at
an earlier written input prefix. Genuine original check-zero VALUE-prefix
locality and the complete table's value invariance identify its stored word
with the independently localized word of its selected endpoint. No Native
base-one parser, assumed tracking assignment or written equality is used.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.RecurrenceSupport

open Support Values Prefix
open Hereditary.FinePredecessor (stripLast stripLast_split stripLast_mem)

theorem buildRev_entry_prefix (xs : List Nat) (e : Entry) (hm : e ∈ buildRev xs) :
    ∃ before after : List Nat, xs.reverse = before ++ e.1 :: after ∧
      e.2 = extend e.1 (table before) := by
  revert hm
  induction xs generalizing e with
  | nil => intro hm; exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    intro hm
    change e ∈ (current, extend current (buildRev rest)) :: buildRev rest at hm
    rcases List.mem_cons.mp hm with he | he
    · subst e
      refine ⟨rest.reverse, [], ?_, ?_⟩
      · simp only [List.reverse_cons]
      · simp only [table, List.reverse_reverse]
    · obtain ⟨before, after, hp, hw⟩ := ih e he
      refine ⟨before, after ++ [current], ?_, hw⟩
      simp only [List.reverse_cons, hp, List.append_assoc, List.cons_append]

theorem table_entry_prefix (xs : List Nat) (e : Entry) (hm : e ∈ table xs) :
    ∃ before after : List Nat, xs = before ++ e.1 :: after ∧
      e.2 = extend e.1 (table before) := by
  simpa only [List.reverse_reverse] using buildRev_entry_prefix xs.reverse e hm

theorem properPrefix_value_prefix (root : Nat) (hi : Localization.inputCheck 0 root = true)
    (before : List Nat) (d : Nat) (suffix : List Nat)
    (he : Localization.nativePath 0 root =
      (Localization.baseRaw 0 :: before) ++ d :: suffix) :
    before.map (interpretation 0) = (properPrefix d).map (interpretation 0) := by
  have hp := nativePath_value_prefix root hi (Localization.baseRaw 0 :: before) d suffix he
  change ((Localization.baseRaw 0 :: before) ++ [d]).map (interpretation 0) =
    (Localization.nativePath 0 d).map (interpretation 0) at hp
  calc
    before.map (interpretation 0) =
        ((((Localization.baseRaw 0 :: before) ++ [d]).map (interpretation 0)).tail).reverse.tail.reverse := by
      simp only [List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.tail_cons, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.reverse_reverse]
    _ = (((Localization.nativePath 0 d).map (interpretation 0)).tail).reverse.tail.reverse :=
      congrArg (fun xs : List Ordinal.{0} => xs.tail.reverse.tail.reverse) hp
    _ = (properPrefix d).map (interpretation 0) := by
      simp only [properPrefix, stripLast, List.map_reverse, List.map_tail]

theorem properPrefix_split_path (root : Nat) (before after : List Nat) (d : Nat)
    (hp : properPrefix root = before ++ d :: after) :
    ∃ suffix : List Nat, Localization.nativePath 0 root =
      (Localization.baseRaw 0 :: before) ++ d :: suffix := by
  obtain ⟨tail, hh⟩ := Localization.nativePath_head 0 root
  have hm : d ∈ properPrefix root := by
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

theorem table_entry_word (root : Nat) (hi : Localization.inputCheck 0 root = true)
    (e : Entry) (hm : e ∈ table (properPrefix root)) :
    e.2.map (interpretation 0) = (word e.1).map (interpretation 0) := by
  obtain ⟨before, after, hp, hw⟩ := table_entry_prefix (properPrefix root) e hm
  obtain ⟨suffix, hs⟩ := properPrefix_split_path root before after e.1 hp
  have hprefix := properPrefix_value_prefix root hi before e.1 suffix hs
  have hepath : e.1 ∈ Localization.nativePath 0 root := by
    rw [hs]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have he : Localization.inputCheck 0 e.1 = true :=
    (Localization.inputCheck_exact 0 e.1).mpr
      (Localization.nativePath_nodes 0 root hi e.1 hepath)
  have hb : ∀ c ∈ before, SourceTrackingRaw.Support.inputCheck c = true := by
    intro c hc
    apply properPrefix_raw root hi c
    rw [hp]
    exact List.mem_append.mpr (Or.inl hc)
  have hd := properPrefix_raw e.1 he
  have ht := table_values before (properPrefix e.1) hb hd hprefix
  have hlow := Localization.node_low 0 e.1 ((Localization.inputCheck_exact 0 e.1).mp he)
  rw [hw, word]
  exact extend_values e.1 e.1 (table before) (table (properPrefix e.1))
    (fun a ha => hb a.1 (List.mem_reverse.mp (buildRev_code_mem before.reverse a ha)))
    (fun a ha => hd a.1 (List.mem_reverse.mp
      (buildRev_code_mem (properPrefix e.1).reverse a ha))) hlow hlow rfl ht

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.RecurrenceSupport
