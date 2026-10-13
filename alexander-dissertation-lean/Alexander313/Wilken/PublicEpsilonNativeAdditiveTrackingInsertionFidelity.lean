import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertionFidelitySupport

/-!
# Actual tracking fidelity of the greatest insertion

The selected original prefix is a genuine reference. Every conditional
replacement starts at or above its written head. Raised replacements have
an independently derived original-source tracker; small replacements use
the real principal product and the actual selected final cover. Thus the
concrete greatest insertion constructs a valid original raw tracking word.
The honest factor<=headword FINAL premise and factor>1 are retained from
the joint Lemma3.21 induction. Full recursive additive assignment is next.
No output tracker, replacement, cover, endpoint or assignment oracle.
All source candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionFidelity

open PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast)
open SourceTrackingSequences (lastCode lastCode_mem lastCode_append_singleton)
open InsertionFidelitySupport

/-- The actual raised tracking conditions put its first value at or above
its true base. The genuine ordered return relation preserves that first
value in the original context. Small products likewise retain this bound. -/
theorem replacement_first_ge_head (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute q head factor) :
    interpretation q head ≤ interpretation q (Insertion.firstCode out) := by
  have hs := ConditionalReplacement.execute_spec q heads hh head factor hhead hf hm hb out ho
  rcases hs.2.2 with hr | ⟨hle, d, he, hv⟩
  · have hc := (ConditionalReplacement.raised_member_caller q heads hh head factor hhead hr.1 hb).2
    obtain ⟨word, hw, ht, he, hlen, hchecked⟩ :=
      Replacement.raisedReplacement_spec q head factor out hc hf hm hr.1 hr.2.1
    cases out with
    | nil => exact False.elim (hs.1 rfl)
    | cons d ds =>
      cases word with
      | nil =>
        have hz : ds.length + 1 = 0 := by simpa only [List.length_cons, List.length_nil] using hlen
        omega
      | cons a as =>
        have hfirst : interpretation q d = interpretation (ReplacementSupport.raisedBaseCode q head) a :=
          (List.cons.inj he).1
        change interpretation q head ≤ interpretation q d
        rw [hfirst, ← (ReplacementSupport.raisedBaseCode_spec q head hc).2.1]
        exact normal_tracking_first_ge_base _ a as ht
  · rw [he]
    change interpretation q head ≤ interpretation q d
    rw [hv]
    exact Ordinal.le_mul_left _ hm.1

/-- A raised written head cannot be final. The original proper reference
therefore supplies its genuine strict separation from every earlier head. -/
theorem raised_last_prefix_lt_head (q : Nat) (heads prefix : List Nat) (head factor : Nat)
    (after : List Nat) (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (he : heads = prefix ++ head :: after) (hne : prefix ≠ [])
    (hlt : interpretation q head < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads)) :
    interpretation q (lastCode prefix) < interpretation q head := by
  have hafter : after ≠ [] := by
    intro ha
    have hlast : lastCode heads = head := by rw [he, ha, lastCode_append_singleton]
    exact hlt.not_ge (by simpa only [hlast] using hb)
  have hr := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hh).2.1
  have he' : heads = (prefix ++ [head]) ++ after := by
    simpa only [List.append_assoc, List.singleton_append] using he
  rw [he', stripLast_append_nonempty (prefix ++ [head]) after hafter] at hr
  have hs := (reference_prefix q (prefix ++ [head]) _ hr).strict
  rw [List.map_append] at hs
  exact (List.pairwise_append.mp hs).2.2 _
    (List.mem_map.mpr ⟨lastCode prefix, lastCode_mem prefix hne, rfl⟩) _ (by simp)

/-- This is a consequence of an actual conditional replacement execution.
The original reference supplies all retained epsilon callers; the genuine
selected FIRST cover handles a small singleton without an independent
tracker at the original base. -/
theorem conditional_splice (q : Nat) (heads prefix : List Nat) (head factor : Nat)
    (after replacement : List Nat) (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (he : heads = prefix ++ head :: after) (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hfactor : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : replacement ∈ ConditionalReplacement.execute q head factor)
    (hcover : prefix ≠ [] → interpretation q (Insertion.firstCode replacement) ≤
      SourceTrackingRaw.Support.muValue q (lastCode prefix)) :
    SourceTrackingRaw.trackingCheck q (prefix ++ replacement) = true := by
  have hhead : head ∈ heads := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hp := ConditionalReplacement.tracking_member_principal q heads hh head hhead
  have hs := ConditionalReplacement.execute_spec q heads hh head factor hhead hf hm hb replacement ho
  have hfirst := replacement_first_ge_head q heads hh head factor hhead hf hm hb replacement ho
  rcases hs.2.2 with hr | ⟨hle, d, hword, hv⟩
  · by_cases hne : prefix = []
    · simpa only [hne, List.nil_append] using hr.2.2
    · have href := tracking_prefix_reference q heads prefix head after hh he
      have hstrict := raised_last_prefix_lt_head q heads prefix head factor after hh he hne hr.1 hb
      cases replacement with
      | nil => exact False.elim (hs.1 rfl)
      | cons first rest =>
        exact tracking_append_tracker q prefix first rest href hne hr.2.2
          (hstrict.trans_le hfirst) (hcover hne)
  · rw [hword]
    have hl : lowCheckCode q d = true := (hs.2.1 d (by rw [hword]; exact List.mem_cons_self)).1
    have hpos : 0 < interpretation q d := by
      rw [hv]; exact hp.2.1.trans_le (Ordinal.le_mul_left _ hm.1)
    have hadd : Ordinal.IsPrincipal (· + ·) (interpretation q d) := by
      rw [hv]
      exact Ordinal.isPrincipal_add_mul_of_isPrincipal_add _ (ne_of_gt hfactor) hm.2.1
    by_cases hne : prefix = []
    · have hbase : base q ≤ interpretation q head := by
        have hhh : SourceTrackingRaw.trackingCheck q (head :: after) = true := by
          simpa only [he, hne, List.nil_append] using hh
        exact tracking_first_ge_base q head after hhh
      simpa only [hne, List.nil_append] using
        SkTracking.Support.singleton_tracking q d hl hpos hadd
          (hbase.trans (by rw [hv]; exact Ordinal.le_mul_left _ hm.1))
    · have href := tracking_prefix_reference q heads prefix head after hh he
      have hd : 1 < interpretation q d := by
        rw [hv]; exact hfactor.trans_le (Ordinal.le_mul_right _ hp.2.1)
      exact tracking_append_singleton q prefix d href hne hl hpos hadd hd
        (by simpa only [hword, Insertion.firstCode, List.head?_cons, Option.getD_some] using hcover hne)

/-- Every actual greatest-insertion output is a real original RAW tracking
word. Only original headword/factor guards and the honest joint final bound
are inputs; actual finite rows, selection, prefix, cover and output tracker
are conclusions of the executing construction. -/
theorem execute_tracking (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hfactor : 1 < interpretation q factor)
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (ho : out ∈ Insertion.execute ((q, factor), heads)) :
    SourceTrackingRaw.trackingCheck q out = true := by
  obtain ⟨rows, hr, hheads, hout, hchecked, hbranch⟩ :=
    Insertion.execute_spec q factor heads out hh hf hm hb ho
  have hrel := InsertionSupport.executeRows_relation q factor heads rows hr
  rcases hbranch with ⟨first, rest, he, hword, hnone⟩ |
      ⟨before, current, after, hne, he, hword, hcover, hnone⟩
  · have hmrow := InsertionSupport.relation_members q factor hrel first (by rw [he]; simp)
    have hhorder : heads = first.1 :: rest.map Prod.fst := by
      rw [← hheads, he, List.map_cons]
    rw [hword]
    exact conditional_splice q heads [] first.1 factor (rest.map Prod.fst) first.2 hh
      hhorder hf hm hfactor hb hmrow.2 (fun hn => False.elim (hn rfl))
  · have hmrow := InsertionSupport.relation_members q factor hrel current (by rw [he]; simp)
    have hhorder : heads = before.map Prod.fst ++ current.1 :: after.map Prod.fst := by
      rw [← hheads, he, List.map_append, List.map_cons]
    rw [hword]
    exact conditional_splice q heads (before.map Prod.fst) current.1 factor
      (after.map Prod.fst) current.2 hh hhorder hf hm hfactor hb hmrow.2 (fun _ => hcover)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionFidelity
