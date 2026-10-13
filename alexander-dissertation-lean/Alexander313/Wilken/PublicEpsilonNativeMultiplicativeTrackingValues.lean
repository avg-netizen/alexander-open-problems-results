import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTracking
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuValueInvariance

/-!
# Actual covered-table invariance under original root spelling

The actual mu cover predicate is invariant on admitted HIGH roots with
equal original values. Its complete finite first-passing selector and
stored-word table therefore have equal ordinal-value projections on two
admitted original HIGH lists with equal ordinal-value projections.
This compares actual executions, not a replacement semantic selector.
Only the displayed original admission premises are used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Values

open SourceTrackingSequences SourceTrackingSequences.Support
open SourceMultiplicativeTracking.Support PublicEpsilonUnboundedIota

noncomputable def entryValues (q : Nat) (e : Entry) : Ordinal.{0} × List Ordinal.{0} :=
  (interpretation q e.1, e.2.map (interpretation q))

theorem coverCheck_invariant (q a b c d : Nat)
    (ha : Mu.inputCheck q a = true) (hb : Mu.inputCheck q b = true)
    (hc : lowCheckCode q c = true) (hd : lowCheckCode q d = true)
    (hab : interpretation q a = interpretation q b)
    (hcd : interpretation q c = interpretation q d) :
    coverCheck q a c = coverCheck q b d := by
  have hm := Mu.ValueInvariance.sourceValue_eq q a b ha hb hab
  have he : coverCheck q a c = true ↔ coverCheck q b d = true := by
    rw [coverCheck_exact, coverCheck_exact]
    simp only [ha, hb, hc, hd, true_and, hm, hcd]
  cases hleft : coverCheck q a c <;> cases hright : coverCheck q b d
  · rfl
  · have hx := he.mpr hright
    rw [hleft] at hx
    cases hx
  · have hx := he.mp hleft
    rw [hright] at hx
    cases hx
  · rfl

/-- The actual finite selection has the same projected record on two
real checked dictionaries; no written record identity is inferred. -/
theorem select_values (q c d : Nat) (es fs : List Entry)
    (hroots : ∀ e ∈ es, Mu.inputCheck q e.1 = true)
    (froots : ∀ e ∈ fs, Mu.inputCheck q e.1 = true)
    (hc : lowCheckCode q c = true) (hd : lowCheckCode q d = true)
    (hcd : interpretation q c = interpretation q d)
    (hvalues : es.map (entryValues q) = fs.map (entryValues q)) :
    (select q c es).map (entryValues q) = (select q d fs).map (entryValues q) := by
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
      have hcov := coverCheck_invariant q a.1 b.1 c d
        (hroots a List.mem_cons_self) (froots b List.mem_cons_self) hc hd
        (congrArg Prod.fst hh.1) hcd
      cases htest : coverCheck q a.1 c with
      | true =>
        have htest' : coverCheck q b.1 d = true := hcov.symm.trans htest
        simpa only [select, htest, htest', Bool.cond_true, Option.map_some,
          Option.some.injEq] using hh.1
      | false =>
        have htest' : coverCheck q b.1 d = false := hcov.symm.trans htest
        simpa only [select, htest, htest', Bool.cond_false] using
          ih fs (fun e he => hroots e (List.mem_cons_of_mem _ he))
            (fun e he => froots e (List.mem_cons_of_mem _ he)) hh.2

theorem extend_values (q c d : Nat) (es fs : List Entry)
    (hroots : ∀ e ∈ es, Mu.inputCheck q e.1 = true)
    (froots : ∀ e ∈ fs, Mu.inputCheck q e.1 = true)
    (hc : lowCheckCode q c = true) (hd : lowCheckCode q d = true)
    (hcd : interpretation q c = interpretation q d)
    (hvalues : es.map (entryValues q) = fs.map (entryValues q)) :
    (extend q c es).map (interpretation q) = (extend q d fs).map (interpretation q) := by
  have hs := select_values q c d es fs hroots froots hc hd hcd hvalues
  cases he : select q c es with
  | none =>
    cases hf : select q d fs with
    | none => simp only [extend, he, hf, List.map_singleton, hcd]
    | some b => simp only [he, hf, Option.map_none, Option.map_some, Option.none_ne_some] at hs
  | some a =>
    cases hf : select q d fs with
    | none => simp only [he, hf, Option.map_none, Option.map_some, Option.some_ne_none] at hs
    | some b =>
      have hv : entryValues q a = entryValues q b := by
        simpa only [he, hf, Option.map_some, Option.some.injEq] using hs
      have hw := congrArg Prod.snd hv
      simpa only [extend, he, hf, List.map_append, List.map_singleton, hcd] using
        congrArg (fun xs : List Ordinal.{0} => xs ++ [interpretation q d]) hw

theorem buildRev_values (q : Nat) (xs ys : List Nat)
    (hroots : ∀ c ∈ xs, Mu.inputCheck q c = true)
    (froots : ∀ c ∈ ys, Mu.inputCheck q c = true)
    (hvalues : xs.map (interpretation q) = ys.map (interpretation q)) :
    (buildRev q xs).map (entryValues q) = (buildRev q ys).map (entryValues q) := by
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
      have he := extend_values q c d (buildRev q xs) (buildRev q ys)
        (fun e hm => hroots e.1 (List.mem_cons_of_mem _ (buildRev_code_mem q xs e hm)))
        (fun e hm => froots e.1 (List.mem_cons_of_mem _ (buildRev_code_mem q ys e hm)))
        (RootLowCollapse.root_low q c (hroots c List.mem_cons_self))
        (RootLowCollapse.root_low q d (froots d List.mem_cons_self)) hh.1 ht
      have hentry : entryValues q (c, extend q c (buildRev q xs)) =
          entryValues q (d, extend q d (buildRev q ys)) := Prod.ext hh.1 he
      simpa only [buildRev, step, List.map_cons] using congrArg₂ List.cons hentry ht

/-- All computed stored words and node values agree in two admitted
lists with equal original values; literal spellings remain separate. -/
theorem table_values (q : Nat) (xs ys : List Nat)
    (hroots : ∀ c ∈ xs, Mu.inputCheck q c = true)
    (froots : ∀ c ∈ ys, Mu.inputCheck q c = true)
    (hvalues : xs.map (interpretation q) = ys.map (interpretation q)) :
    (table q xs).map (entryValues q) = (table q ys).map (entryValues q) := by
  apply buildRev_values q xs.reverse ys.reverse
    (fun c hc => hroots c (List.mem_reverse.mp hc))
    (fun c hc => froots c (List.mem_reverse.mp hc))
  simpa only [List.map_reverse] using congrArg List.reverse hvalues

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking.Values
