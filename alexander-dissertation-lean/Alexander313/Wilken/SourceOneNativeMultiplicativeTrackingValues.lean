import Alexander313.Wilken.SourceOneNativeMultiplicativeTracking
import Alexander313.Wilken.HereditaryLocalizationOrder

/-!
# Genuine original source-one covered table value invariance

The actual raw source-one mu and canonical cover tests are invariant under
equal original raw epsilon values. The literal first-passing selector and
every stored finite word therefore have equal value projections on two
originally admitted lists with equal value projections. This preserves the
executing table and keeps code spelling separate from ordinal equality.
Original localization prefix values are derived from the actual recurrence
and maximal-argument uniqueness. No Native base-one parser or supplied
value prefix, table or selection is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Values

open SourceTrackingRaw.Support (coverCheck coverCheck_exact)
open Support

noncomputable def entryValues (e : Entry) : Ordinal.{0} × List Ordinal.{0} :=
  (interpretation 0 e.1, e.2.map (interpretation 0))

theorem coverCheck_invariant (a b c d : Nat)
    (ha : SourceTrackingRaw.Support.inputCheck a = true)
    (hb : SourceTrackingRaw.Support.inputCheck b = true)
    (hc : lowCheckCode 0 c = true) (hd : lowCheckCode 0 d = true)
    (hab : interpretation 0 a = interpretation 0 b)
    (hcd : interpretation 0 c = interpretation 0 d) : coverCheck a c = coverCheck b d := by
  have hm := SourceTrackingRaw.Support.muValue_invariant a b ha hb hab
  have he : coverCheck a c = true ↔ coverCheck b d = true := by
    rw [coverCheck_exact, coverCheck_exact]
    simp only [ha, hb, hc, hd, true_and, hm, hcd]
  cases hleft : coverCheck a c <;> cases hright : coverCheck b d
  · rfl
  · have hx := he.mpr hright
    rw [hleft] at hx
    cases hx
  · have hx := he.mp hleft
    rw [hright] at hx
    cases hx
  · rfl

theorem select_values (c d : Nat) (es fs : List Entry)
    (hroots : ∀ e ∈ es, SourceTrackingRaw.Support.inputCheck e.1 = true)
    (froots : ∀ e ∈ fs, SourceTrackingRaw.Support.inputCheck e.1 = true)
    (hc : lowCheckCode 0 c = true) (hd : lowCheckCode 0 d = true)
    (hcd : interpretation 0 c = interpretation 0 d)
    (hvalues : es.map entryValues = fs.map entryValues) :
    (select c es).map entryValues = (select d fs).map entryValues := by
  revert hroots froots hvalues
  induction es generalizing fs with
  | nil =>
    intro hroots froots hvalues
    have hf : fs = [] := List.eq_nil_of_map_eq_nil hvalues.symm
    subst fs
    rfl
  | cons a es ih =>
    intro hroots froots hvalues
    cases fs with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hvalues
    | cons b fs =>
      have hh := List.cons.inj (by simpa only [List.map_cons] using hvalues)
      have hcov := coverCheck_invariant a.1 b.1 c d
        (hroots a List.mem_cons_self) (froots b List.mem_cons_self) hc hd
        (congrArg Prod.fst hh.1) hcd
      cases htest : coverCheck a.1 c with
      | true =>
        have htest' : coverCheck b.1 d = true := hcov.symm.trans htest
        simpa only [select, htest, htest', Bool.cond_true, Option.map_some,
          Option.some.injEq] using hh.1
      | false =>
        have htest' : coverCheck b.1 d = false := hcov.symm.trans htest
        simpa only [select, htest, htest', Bool.cond_false] using
          ih fs (fun e he => hroots e (List.mem_cons_of_mem _ he))
            (fun e he => froots e (List.mem_cons_of_mem _ he)) hh.2

theorem extend_values (c d : Nat) (es fs : List Entry)
    (hroots : ∀ e ∈ es, SourceTrackingRaw.Support.inputCheck e.1 = true)
    (froots : ∀ e ∈ fs, SourceTrackingRaw.Support.inputCheck e.1 = true)
    (hc : lowCheckCode 0 c = true) (hd : lowCheckCode 0 d = true)
    (hcd : interpretation 0 c = interpretation 0 d)
    (hvalues : es.map entryValues = fs.map entryValues) :
    (extend c es).map (interpretation 0) = (extend d fs).map (interpretation 0) := by
  have hs := select_values c d es fs hroots froots hc hd hcd hvalues
  cases he : select c es with
  | none =>
    cases hf : select d fs with
    | none => simp only [extend, he, hf, List.map_singleton, hcd]
    | some b => simp only [he, hf, Option.map_none, Option.map_some, Option.none_ne_some] at hs
  | some a =>
    cases hf : select d fs with
    | none => simp only [he, hf, Option.map_none, Option.map_some, Option.some_ne_none] at hs
    | some b =>
      have hv : entryValues a = entryValues b := by
        simpa only [he, hf, Option.map_some, Option.some.injEq] using hs
      have hw := congrArg Prod.snd hv
      simpa only [extend, he, hf, List.map_append, List.map_singleton, hcd] using
        congrArg (fun xs : List Ordinal.{0} => xs ++ [interpretation 0 d]) hw

theorem buildRev_values (xs ys : List Nat)
    (hroots : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck c = true)
    (froots : ∀ c ∈ ys, SourceTrackingRaw.Support.inputCheck c = true)
    (hvalues : xs.map (interpretation 0) = ys.map (interpretation 0)) :
    (buildRev xs).map entryValues = (buildRev ys).map entryValues := by
  revert hroots froots hvalues
  induction xs generalizing ys with
  | nil =>
    intro hroots froots hvalues
    have hy : ys = [] := List.eq_nil_of_map_eq_nil hvalues.symm
    subst ys
    rfl
  | cons c xs ih =>
    intro hroots froots hvalues
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hvalues
    | cons d ys =>
      have hh := List.cons.inj (by simpa only [List.map_cons] using hvalues)
      have ht := ih ys (fun a ha => hroots a (List.mem_cons_of_mem _ ha))
        (fun a ha => froots a (List.mem_cons_of_mem _ ha)) hh.2
      have he := extend_values c d (buildRev xs) (buildRev ys)
        (fun e hm => hroots e.1 (List.mem_cons_of_mem _ (buildRev_code_mem xs e hm)))
        (fun e hm => froots e.1 (List.mem_cons_of_mem _ (buildRev_code_mem ys e hm)))
        ((SourceTrackingRaw.Support.inputCheck_exact c).mp (hroots c List.mem_cons_self)).1
        ((SourceTrackingRaw.Support.inputCheck_exact d).mp (froots d List.mem_cons_self)).1 hh.1 ht
      have hentry : entryValues (c, extend c (buildRev xs)) =
          entryValues (d, extend d (buildRev ys)) := Prod.ext hh.1 he
      simpa only [buildRev, step, List.map_cons] using congrArg₂ List.cons hentry ht

theorem table_values (xs ys : List Nat)
    (hroots : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck c = true)
    (froots : ∀ c ∈ ys, SourceTrackingRaw.Support.inputCheck c = true)
    (hvalues : xs.map (interpretation 0) = ys.map (interpretation 0)) :
    (table xs).map entryValues = (table ys).map entryValues := by
  apply buildRev_values xs.reverse ys.reverse
    (fun c hc => hroots c (List.mem_reverse.mp hc))
    (fun c hc => froots c (List.mem_reverse.mp hc))
  simpa only [List.map_reverse] using congrArg List.reverse hvalues

theorem nativePath_value_prefix (root : Nat) (hi : Localization.inputCheck 0 root = true)
    («prefix» : List Nat) (d : Nat) (suffix : List Nat)
    (he : Localization.nativePath 0 root = «prefix» ++ d :: suffix) :
    («prefix» ++ [d]).map (Localization.value 0) =
      (Localization.nativePath 0 d).map (Localization.value 0) := by
  have hn := (Localization.inputCheck_exact 0 root).mp hi
  have hp := Localization.nativePath_source 0 root hi
  have hprefix := Localization.Refinements.sourcePath_prefix_valuePath hn hp «prefix» d suffix he
  have hdPath : d ∈ Localization.nativePath 0 root := by
    rw [he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hd := hp.nodes d hdPath
  have hdp := Localization.nativePath_source 0 d ((Localization.inputCheck_exact 0 d).mpr hd)
  obtain ⟨rootTail, hrootHead⟩ := Localization.nativePath_head 0 root
  have hprefixHead : ∃ tail : List Nat, «prefix» ++ [d] = Localization.baseRaw 0 :: tail := by
    cases «prefix» with
    | nil =>
      have hsame : Localization.baseRaw 0 :: rootTail = d :: suffix := by
        simpa only [List.nil_append] using hrootHead.symm.trans he
      rw [← (List.cons.inj hsame).1]
      exact ⟨[], rfl⟩
    | cons c «prefix» =>
      have hsame : Localization.baseRaw 0 :: rootTail = c :: («prefix» ++ d :: suffix) := by
        simpa only [List.cons_append] using hrootHead.symm.trans he
      rw [← (List.cons.inj hsame).1]
      exact ⟨«prefix» ++ [d], rfl⟩
  obtain ⟨tail, hprefixHead⟩ := hprefixHead
  obtain ⟨dTail, hdHead⟩ := Localization.nativePath_head 0 d
  rw [hprefixHead] at hprefix ⊢
  rw [hdHead] at hdp ⊢
  exact hprefix.values_unique (fun e hm => Localization.support_node 0 d e hd hm) _ _
    (Localization.Refinements.sourcePath_valuePath hdp) rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Values
