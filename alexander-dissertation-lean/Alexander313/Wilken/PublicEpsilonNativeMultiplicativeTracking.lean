import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingSupport
import Alexander313.Wilken.PublicEpsilonNativeLocalizationRootAdapter

/-!
# Genuine reference and tracking conditions for the finite covered table

Every proper localization entry is an actual HIGH epsilon root. Processing
these entries in their original strictly increasing order constructs real
reference words. The final original principal entry is appended using the
actual source mu cover at the selected earlier entry. Every caller and
inequality derives from the original finite path; no evaluation or tracking
soundness is supplied. The source3.19 recurrence and raw caller adapters
are recorded separately from these table invariants. Uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking

open SourceTrackingSequences SourceTrackingSequences.Support Support
open PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast stripLast_primrec)

def properPrefix (q root : Nat) : List Nat := stripLast (SourceLocalization.nativePath q root).tail

theorem properPrefix_primrec : Primrec₂ properPrefix :=
  (stripLast_primrec.comp (Primrec.list_tail.comp SourceLocalization.nativePath_primrec)).to₂

theorem properPrefix_roots (q root : Nat) (hi : SourceLocalization.inputCheck q root = true) :
    ∀ c ∈ properPrefix q root, Mu.inputCheck q c = true :=
  fun c hc => (SourceLocalization.Properties.nativePath_proper_prefix_spec q root hi c hc).1

theorem properPrefix_strict (q root : Nat) (hi : SourceLocalization.inputCheck q root = true) :
    ((properPrefix q root).map (interpretation q)).Pairwise (· < ·) := by
  obtain ⟨tail, he⟩ := SourceLocalization.nativePath_head q root
  have hp := SourceLocalization.nativePath_strict q root hi
  rw [he, List.map_cons] at hp
  have ht := (List.pairwise_cons.mp hp).2
  by_cases hn : tail = []
  · simp only [properPrefix, he, List.tail_cons, hn, stripLast, List.reverse_nil,
      List.tail_nil, List.map_nil, List.pairwise_nil]
  · obtain ⟨a, ha, _⟩ := Hereditary.FinePredecessor.stripLast_split tail hn
    rw [ha, List.map_append] at ht
    simpa only [properPrefix, he, List.tail_cons] using (List.pairwise_append.mp ht).1

theorem properPrefix_reverse_strict (q root : Nat) (hi : SourceLocalization.inputCheck q root = true) :
    ((properPrefix q root).reverse.map (interpretation q)).Pairwise (fun a b => b < a) := by
  rw [List.map_reverse]
  exact List.pairwise_reverse.mpr (properPrefix_strict q root hi)

/-- First passing in the genuine reverse order is the greatest covered
original localization value; all more recent actual records are excluded. -/
theorem select_greatest (q current : Nat) (es : List Entry) (e : Entry)
    (horder : (es.map (fun a => interpretation q a.1)).Pairwise (fun a b => b < a))
    (hs : select q current es = some e) :
    ∀ a ∈ es, coverCheck q a.1 current = true → interpretation q a.1 ≤ interpretation q e.1 := by
  revert horder hs
  induction es with
  | nil => intro _ hs; simp only [select, Option.none_ne_some] at hs
  | cons b es ih =>
    intro horder hs a ha hc
    have ht := (List.pairwise_cons.mp horder).2
    cases hb : coverCheck q b.1 current with
    | true =>
      have he : b = e := by simpa only [select, hb, Bool.cond_true, Option.some.injEq] using hs
      subst e
      rcases List.mem_cons.mp ha with he | ha
      · simpa only [he] using (le_rfl : interpretation q b.1 ≤ interpretation q b.1)
      · exact ((List.pairwise_cons.mp horder).1 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)).le
    | false =>
      have hs' : select q current es = some e := by
        simpa only [select, hb, Bool.cond_false] using hs
      rcases List.mem_cons.mp ha with he | ha
      · have hx : false = true := by simpa only [he, hb] using hc
        cases hx
      · exact ih ht hs' a ha hc

theorem lastCode_cons_nonempty (a : Nat) (xs : List Nat) (hne : xs ≠ []) :
    lastCode (a :: xs) = lastCode xs := by
  obtain ⟨b, bs, he⟩ := List.exists_cons_of_ne_nil ((List.reverse_ne_nil_iff).mpr hne)
  simp only [lastCode, List.reverse_cons, he, List.cons_append, List.head?_cons]

/-- Actual reference extension at the real last mu caller. -/
theorem reference_append (q current : Nat) (xs : List Nat) (hr : Reference q xs)
    (hc : Mu.inputCheck q current = true)
    (hstrict : ∀ a ∈ xs, interpretation q a < interpretation q current)
    (hcover : xs ≠ [] → interpretation q current ≤ Mu.sourceValue q (lastCode xs)) :
    Reference q (xs ++ [current]) := by
  revert hstrict hcover
  induction hr with
  | nil => intro _ _; exact Reference.one current hc
  | one a ha =>
    intro hstrict hcover
    apply Reference.cons a current [] ha (hstrict a List.mem_cons_self) ?_ (Reference.one current hc)
    simpa only [lastCode_singleton] using hcover (by simp)
  | cons a b xs ha hab hcov hr ih =>
    intro hstrict hcover
    have ht : Reference q ((b :: xs) ++ [current]) := ih
      (fun c hm => hstrict c (List.mem_cons_of_mem _ hm))
      (fun hne => by
        have hh := hcover (by simp)
        rw [lastCode_cons_nonempty a (b :: xs) (by simp)] at hh
        exact hh)
    simpa only [List.cons_append] using Reference.cons a b (xs ++ [current]) ha hab hcov ht

/-- At every actual proper prefix, stored words are genuine references. -/
theorem buildRev_reference (q : Nat) (xs : List Nat)
    (hroots : ∀ c ∈ xs, Mu.inputCheck q c = true)
    (hstrict : (xs.map (interpretation q)).Pairwise (fun a b => b < a)) :
    ∀ e ∈ buildRev q xs, Reference q e.2 := by
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
      change Reference q (extend q current (buildRev q rest))
      cases hs : select q current (buildRev q rest) with
      | none => simpa only [extend, hs] using Reference.one current hc
      | some a =>
        have ha := select_mem q current (buildRev q rest) a hs
        have hr := htail a ha
        have hend := (buildRev_last q rest a ha).2
        have hcover := (coverCheck_exact q a.1 current).mp (select_cover q current _ a hs)
        have hless : ∀ c ∈ a.2, interpretation q c < interpretation q current := by
          intro c hm
          exact (List.pairwise_cons.mp hstrict).1 _
            (List.mem_map.mpr ⟨c, buildRev_word_mem q rest a ha c hm, rfl⟩)
        have ht := reference_append q current a.2 hr hc hless
          (fun _ => by simpa only [hend] using hcover.2.2)
        simpa only [extend, hs] using ht
    · exact htail e he

theorem table_reference (q : Nat) (xs : List Nat)
    (hroots : ∀ c ∈ xs, Mu.inputCheck q c = true)
    (hstrict : (xs.reverse.map (interpretation q)).Pairwise (fun a b => b < a)) :
    ∀ e ∈ table q xs, Reference q e.2 :=
  buildRev_reference q xs.reverse
    (fun c hm => hroots c (List.mem_reverse.mp hm)) hstrict

/-- The selected real last mu computes the actual principal extension.
All table-word admission and strictness are derived, rather than supplied
as a tracking assignment. -/
theorem extend_tracking (q current : Nat) (xs : List Nat)
    (hroots : ∀ c ∈ xs, Mu.inputCheck q c = true)
    (hpath : (xs.reverse.map (interpretation q)).Pairwise (fun a b => b < a))
    (hlow : lowCheckCode q current = true) (hpos : 0 < interpretation q current)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation q current))
    (hbase : base q ≤ interpretation q current) :
    Tracking q (extend q current (table q xs)) := by
  cases hs : select q current (table q xs) with
  | none =>
    have he : extend q current (table q xs) = [current] := by simp only [extend, hs]
    rw [he]
    refine ⟨by simp, Reference.nil, ?_, ?_, ?_, ?_⟩
    · simpa only [lastCode_singleton] using hlow
    · simpa only [lastCode_singleton] using hpos
    · simpa only [lastCode_singleton] using hprincipal
    · simpa only [stripLast_singleton, lastCode_singleton, if_pos rfl] using hbase
  | some a =>
    have ha := select_mem q current (table q xs) a hs
    have hr := table_reference q xs hroots hpath a ha
    have hl := buildRev_last q xs.reverse a ha
    have hscover := (coverCheck_exact q a.1 current).mp (select_cover q current _ a hs)
    have hq := (HeightBoundary.input_spec q current hlow).2.1
    have hone : 1 < interpretation q current :=
      (Hereditary.EpsilonOffsets.epsilon_one_lt (SourceChi.epsilon_base q hq)).trans_le hbase
    have he : extend q current (table q xs) = a.2 ++ [current] := by simp only [extend, hs]
    rw [he]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stripLast_append_singleton] using hr
    · simpa only [lastCode_append_singleton] using hlow
    · simpa only [lastCode_append_singleton] using hpos
    · simpa only [lastCode_append_singleton] using hprincipal
    · rw [stripLast_append_singleton, lastCode_append_singleton, if_neg hl.1, hl.2]
      exact ⟨hone, hscover.2.2⟩

def word (q root : Nat) : List Nat := extend q root (table q (properPrefix q root))

theorem word_primrec : Primrec₂ word :=
  (extend_primrec.comp ((Primrec.fst.pair Primrec.snd).pair
    (table_primrec.comp Primrec.fst properPrefix_primrec))).to₂

/-- The actual original Node supplies all real final principal callers. -/
theorem node_principal_spec (q root : Nat) (hn : SourceLocalization.Node q root) :
    lowCheckCode q root = true ∧ 0 < interpretation q root ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q root) ∧ base q ≤ interpretation q root := by
  have hl := SourceLocalization.node_low q root hn
  obtain ⟨a, he, ht, hnormal⟩ := hn
  have hp := SourceChi.Powers.theta_principal q a ht
  have hb := (FixedPoint.checked_theta_range q 0 a ht).1
  refine ⟨hl, ?_, ?_, ?_⟩
  · simpa only [he, interpretation_code] using hp.1
  · simpa only [he, interpretation_code] using hp.2
  · simpa only [he, interpretation_code, omegaSequence_zero] using hb

theorem word_tracking (q root : Nat) (hi : SourceLocalization.inputCheck q root = true) :
    Tracking q (word q root) := by
  have hs := node_principal_spec q root ((SourceLocalization.inputCheck_exact q root).mp hi)
  exact extend_tracking q root (properPrefix q root) (properPrefix_roots q root hi)
    (properPrefix_reverse_strict q root hi) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

theorem word_last (q root : Nat) : lastCode (word q root) = root := extend_last q root _

/-- The actual raw caller's final code stays unchanged; only its real
localization dictionary is constructed by the proved same-value parser. -/
def rawWord (q current : Nat) : List Nat := extend q current
  (table q (properPrefix q (SourceLocalization.RootAdapter.rootCode q current)))

theorem rawWord_primrec : Primrec₂ rawWord := by
  have hr := SourceLocalization.RootAdapter.rootCode_primrec
  have hp := properPrefix_primrec.comp Primrec.fst hr
  have ht := table_primrec.comp Primrec.fst hp
  exact (extend_primrec.comp ((Primrec.fst.pair Primrec.snd).pair ht)).to₂

theorem rawWord_tracking (q current : Nat) (hi : SourceLocalization.RootAdapter.inputCheck q current = true) :
    Tracking q (rawWord q current) := by
  have hc := (SourceLocalization.RootAdapter.inputCheck_exact q current).mp hi
  have hr := SourceLocalization.RootAdapter.rootInput q current hi
  have hq := (HeightBoundary.input_spec q current hc.1).2.1
  exact extend_tracking q current (properPrefix q (SourceLocalization.RootAdapter.rootCode q current))
    (properPrefix_roots q _ hr) (properPrefix_reverse_strict q _ hr)
    hc.1 ((base_pos q hq).trans_le hc.2.1) hc.2.2 hc.2.1

theorem rawWord_last (q current : Nat) : lastCode (rawWord q current) = current := extend_last q current _

/-- The real finite tracking condition checker accepts the constructed
word on EVERY original raw principal caller in its exact domain. -/
theorem rawWord_checked (q current : Nat) (hi : SourceLocalization.RootAdapter.inputCheck q current = true) :
    SourceTrackingSequences.trackingCheck q (rawWord q current) = true :=
  (SourceTrackingSequences.trackingCheck_exact q _).mpr (rawWord_tracking q current hi)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceMultiplicativeTracking
