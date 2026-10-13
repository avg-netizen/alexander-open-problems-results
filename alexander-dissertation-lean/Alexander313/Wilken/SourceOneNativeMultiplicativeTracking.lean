import Alexander313.Wilken.SourceOneNativeMultiplicativeTrackingSupport
import Alexander313.Wilken.SourceOneNativeLocalizationRootAdapter

/-!
# Genuine finite covered words above the original source-one base

The actual original localization proper prefix derives every RAW epsilon
and mu caller. Its finite covered table constructs genuine references;
the final original principal code is appended by the actual source-one
cover comparison. The source-one base endpoint is retained through the
empty-prefix branch. These are table and tracking invariants, not yet the
Definition3.19 recurrence at every selected endpoint. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking

open SourceTrackingRaw SourceTrackingRaw.Support (coverCheck coverCheck_exact)
open Support
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton lastCode_append_singleton
  stripLast_singleton stripLast_append_singleton)

theorem select_greatest (current : Nat) (es : List Entry) (e : Entry)
    (horder : (es.map (fun a => interpretation 0 a.1)).Pairwise (fun a b => b < a))
    (hs : select current es = some e) :
    ∀ a ∈ es, coverCheck a.1 current = true → interpretation 0 a.1 ≤ interpretation 0 e.1 := by
  revert horder hs
  induction es with
  | nil => intro _ hs; simp only [select, Option.none_ne_some] at hs
  | cons b es ih =>
    intro horder hs a ha hc
    have ht := (List.pairwise_cons.mp horder).2
    cases hb : coverCheck b.1 current with
    | true =>
      have he : b = e := by simpa only [select, hb, Bool.cond_true, Option.some.injEq] using hs
      subst e
      rcases List.mem_cons.mp ha with he | ha
      · simpa only [he] using (le_rfl : interpretation 0 b.1 ≤ interpretation 0 b.1)
      · exact ((List.pairwise_cons.mp horder).1 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)).le
    | false =>
      have hs' : select current es = some e := by simpa only [select, hb, Bool.cond_false] using hs
      rcases List.mem_cons.mp ha with he | ha
      · have hx : false = true := by simpa only [he, hb] using hc
        cases hx
      · exact ih ht hs' a ha hc

theorem lastCode_cons_nonempty (a : Nat) (xs : List Nat) (hne : xs ≠ []) :
    lastCode (a :: xs) = lastCode xs := by
  obtain ⟨b, bs, he⟩ := List.exists_cons_of_ne_nil ((List.reverse_ne_nil_iff).mpr hne)
  simp only [NativeContext.SourceTrackingSequences.lastCode, List.reverse_cons, he,
    List.cons_append, List.head?_cons]

theorem reference_append (current : Nat) (xs : List Nat) (hr : Reference xs)
    (hc : SourceTrackingRaw.Support.inputCheck current = true)
    (hstrict : ∀ a ∈ xs, interpretation 0 a < interpretation 0 current)
    (hcover : xs ≠ [] → interpretation 0 current ≤ SourceTrackingRaw.Support.muValue (lastCode xs)) :
    Reference (xs ++ [current]) := by
  revert hstrict hcover
  induction hr with
  | nil => intro _ _; exact Reference.one current hc
  | one a ha =>
    intro hstrict hcover
    apply Reference.cons a current [] ha (hstrict a List.mem_cons_self) ?_ (Reference.one current hc)
    simpa only [lastCode_singleton] using hcover (by simp)
  | cons a b xs ha hab hcov hr ih =>
    intro hstrict hcover
    have ht : Reference ((b :: xs) ++ [current]) := ih
      (fun c hm => hstrict c (List.mem_cons_of_mem _ hm))
      (fun hne => by
        have hh := hcover (by simp)
        rw [lastCode_cons_nonempty a (b :: xs) (by simp)] at hh
        exact hh)
    simpa only [List.cons_append] using Reference.cons a b (xs ++ [current]) ha hab hcov ht

theorem buildRev_reference (xs : List Nat)
    (hroots : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck c = true)
    (hstrict : (xs.map (interpretation 0)).Pairwise (fun a b => b < a)) :
    ∀ e ∈ buildRev xs, Reference e.2 := by
  revert hroots hstrict
  induction xs with
  | nil => intro _ _ e hm; exact False.elim (List.not_mem_nil hm)
  | cons current rest ih =>
    intro hroots hstrict e he
    have hc := hroots current List.mem_cons_self
    have htail := ih (fun c hm => hroots c (List.mem_cons_of_mem _ hm))
      (List.pairwise_cons.mp hstrict).2
    rcases List.mem_cons.mp he with he | he
    · subst e
      change Reference (extend current (buildRev rest))
      cases hs : select current (buildRev rest) with
      | none => simpa only [extend, hs] using Reference.one current hc
      | some a =>
        have ha := select_mem current (buildRev rest) a hs
        have hr := htail a ha
        have hend := (buildRev_last rest a ha).2
        have hcover := (coverCheck_exact a.1 current).mp (select_cover current _ a hs)
        have hless : ∀ c ∈ a.2, interpretation 0 c < interpretation 0 current := by
          intro c hm
          exact (List.pairwise_cons.mp hstrict).1 _
            (List.mem_map.mpr ⟨c, buildRev_word_mem rest a ha c hm, rfl⟩)
        have ht := reference_append current a.2 hr hc hless
          (fun _ => by simpa only [hend] using hcover.2.2)
        simpa only [extend, hs] using ht
    · exact htail e he

theorem table_reference (xs : List Nat)
    (hroots : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck c = true)
    (hstrict : (xs.reverse.map (interpretation 0)).Pairwise (fun a b => b < a)) :
    ∀ e ∈ table xs, Reference e.2 :=
  buildRev_reference xs.reverse (fun c hm => hroots c (List.mem_reverse.mp hm)) hstrict

theorem extend_tracking (current : Nat) (xs : List Nat)
    (hroots : ∀ c ∈ xs, SourceTrackingRaw.Support.inputCheck c = true)
    (hpath : (xs.reverse.map (interpretation 0)).Pairwise (fun a b => b < a))
    (hlow : lowCheckCode 0 current = true) (hpos : 0 < interpretation 0 current)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation 0 current))
    (hbase : 1 ≤ interpretation 0 current)
    (hlarge : xs ≠ [] → 1 < interpretation 0 current) : Tracking (extend current (table xs)) := by
  cases hs : select current (table xs) with
  | none =>
    have he : extend current (table xs) = [current] := by simp only [extend, hs]
    rw [he]
    refine ⟨by simp, Reference.nil, ?_, ?_, ?_, ?_⟩
    · simpa only [lastCode_singleton] using hlow
    · simpa only [lastCode_singleton] using hpos
    · simpa only [lastCode_singleton] using hprincipal
    · simpa only [stripLast_singleton, lastCode_singleton, if_pos rfl] using hbase
  | some a =>
    have ha := select_mem current (table xs) a hs
    have hr := table_reference xs hroots hpath a ha
    have hl := buildRev_last xs.reverse a ha
    have hscover := (coverCheck_exact a.1 current).mp (select_cover current _ a hs)
    have hne : xs ≠ [] := by
      intro he
      have hm := buildRev_code_mem xs.reverse a ha
      rw [he, List.reverse_nil] at hm
      exact List.not_mem_nil hm
    have he : extend current (table xs) = a.2 ++ [current] := by simp only [extend, hs]
    rw [he]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stripLast_append_singleton] using hr
    · simpa only [lastCode_append_singleton] using hlow
    · simpa only [lastCode_append_singleton] using hpos
    · simpa only [lastCode_append_singleton] using hprincipal
    · rw [stripLast_append_singleton, lastCode_append_singleton, if_neg hl.1, hl.2]
      exact ⟨hlarge hne, hscover.2.2⟩

def word (root : Nat) : List Nat := extend root (table (Prefix.properPrefix root))

theorem word_primrec : Primrec word :=
  extend_primrec.comp Primrec.id (table_primrec.comp Prefix.properPrefix_primrec)

theorem node_principal_spec (root : Nat) (hn : Localization.Node 0 root) :
    lowCheckCode 0 root = true ∧ 0 < interpretation 0 root ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 root) ∧ 1 ≤ interpretation 0 root := by
  have hl := Localization.node_low 0 root hn
  have hb := Localization.baseRaw_le 0 root hn
  obtain ⟨a, he, ht, hnormal⟩ := hn
  obtain ⟨n, ha⟩ := (check_iff_finite_admissible 0 (.theta 0 a)).mp ht
  have hp := Theta.theta_pos_principal 0 n 0 a ha
  have hv : finiteDenote 0 n (.theta 0 a) = interpretation 0 root := by
    rw [he, interpretation_code]
    exact (denote_eq_finite 0 n (.theta 0 a) ha.2).symm
  exact ⟨hl, hp.1.trans_eq hv, by simpa only [hv] using hp.2,
    by simpa only [Localization.baseRaw_value, finiteBase_zero, Localization.value] using hb⟩

theorem word_tracking (root : Nat) (hi : Localization.inputCheck 0 root = true) : Tracking (word root) := by
  have hs := node_principal_spec root ((Localization.inputCheck_exact 0 root).mp hi)
  exact extend_tracking root (Prefix.properPrefix root) (Prefix.properPrefix_raw root hi)
    (Prefix.properPrefix_reverse_strict root hi) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (Prefix.properPrefix_nonempty_root_large root hi)

theorem word_last (root : Nat) : lastCode (word root) = root := extend_last root _

theorem word_checked (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    SourceTrackingRaw.trackingCheck (word root) = true :=
  (SourceTrackingRaw.trackingCheck_exact _).mpr (word_tracking root hi)

def rawWord (current : Nat) : List Nat := extend current
  (table (Prefix.properPrefix (SourceLocalization.RootAdapter.rootCode current)))

theorem rawWord_primrec : Primrec rawWord :=
  extend_primrec.comp Primrec.id (table_primrec.comp
    (Prefix.properPrefix_primrec.comp SourceLocalization.RootAdapter.rootCode_primrec))

theorem rawWord_tracking (current : Nat)
    (hi : SourceLocalization.RootAdapter.inputCheck current = true) : Tracking (rawWord current) := by
  have hc := (SourceLocalization.RootAdapter.inputCheck_exact current).mp hi
  have hr := SourceLocalization.RootAdapter.rootInput current hi
  have hv := SourceLocalization.RootAdapter.rootCode_value current hi
  exact extend_tracking current (Prefix.properPrefix (SourceLocalization.RootAdapter.rootCode current))
    (Prefix.properPrefix_raw _ hr) (Prefix.properPrefix_reverse_strict _ hr)
    hc.1 (Order.one_le_iff_pos.mp hc.2.1) hc.2.2 hc.2.1
    (fun hne => (Prefix.properPrefix_nonempty_root_large _ hr hne).trans_eq hv)

theorem rawWord_last (current : Nat) : lastCode (rawWord current) = current := extend_last current _

theorem rawWord_checked (current : Nat)
    (hi : SourceLocalization.RootAdapter.inputCheck current = true) :
    SourceTrackingRaw.trackingCheck (rawWord current) = true :=
  (SourceTrackingRaw.trackingCheck_exact _).mpr (rawWord_tracking current hi)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking
