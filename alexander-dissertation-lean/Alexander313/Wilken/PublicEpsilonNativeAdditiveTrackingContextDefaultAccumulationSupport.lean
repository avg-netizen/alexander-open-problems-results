import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingContextAccumulation

/-!
# Actual retained-head/reset updates without a preceding cover

Actual append or selected suffix insertion retains the original head.
Only observed NONE resets to a complete lower Assignment. Genuine OWN
return and whole branch covariance then construct every initialized next
Assignment, LF and admitted original spelling. No preceding boundary cover
or arbitrary initial suffix Assignment is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextDefaultAccumulationSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open ReplacementFidelity (SameEntry)
open Alexander313.Wilken.MultiplicativeNormalForm MultiplicativePrincipalArithmetic

private theorem relation_checked {q r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (SameEntry q r) xs ys) :
    ∀ d ∈ ys, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true := by
  induction hr with
  | nil => intro d hd; exact False.elim (List.not_mem_nil hd)
  | @cons c d xs ys he ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨he.1, he.2.1⟩
    · exact ih a ha

private theorem relation_of_values (q r : Nat) (xs ys : List Nat)
    (hv : ys.map (interpretation q) = xs.map (interpretation r))
    (ha : ∀ d ∈ ys, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) :
    List.Forall₂ (SameEntry q r) xs ys := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := by simpa only [List.map_nil, List.map_eq_nil_iff] using hv
    subst ys
    exact .nil
  | cons c cs ih =>
    cases ys with
    | nil => simp only [List.map_nil, List.map_cons, List.nil_ne_cons] at hv
    | cons d ds =>
      have he := List.cons.inj hv
      exact .cons ⟨(ha d List.mem_cons_self).1, (ha d List.mem_cons_self).2, he.1⟩
        (ih ds he.2 (fun a hm => ha a (List.mem_cons_of_mem _ hm)))

private theorem branches_checked (q factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (lastCode heads))
    (hc : ∀ d ∈ heads, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true)
    (ho : out ∈ Branches.execute ((q, factor), heads)) :
    ∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true := by
  rcases Branches.execute_branch q factor heads out ho with ⟨hflag, he⟩ | ⟨hflag, hi⟩
  · intro d hd
    rw [he] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hc d hd
    · simpa only [List.mem_singleton.mp hd] using hf
  · obtain ⟨rows, hr, hheads, hout, hchecked, hcases⟩ :=
      Insertion.execute_spec q factor heads out hh hf.1 hm hb hi
    rcases hcases with ⟨first, rest, hrows, he, hn⟩ |
      ⟨before, current, after, hne, hrows, he, hcover, hn⟩
    · intro d hd
      exact (hchecked first (by rw [hrows]; exact List.mem_cons_self)).2 d
        (by simpa only [he] using hd)
    · intro d hd
      rw [he] at hd
      rcases List.mem_append.mp hd with hd | hd
      · apply hc d
        rw [← hheads, hrows, List.map_append]
        exact List.mem_append_left _ hd
      · exact (hchecked current (by
          rw [hrows]
          exact List.mem_append_right _ List.mem_cons_self)).2 d hd

private theorem word_some_head (q : Nat) (first : InsertionSupport.Row) (rest : List InsertionSupport.Row)
    (selected : Insertion.Candidate) (hs : Insertion.choose q (first :: rest) = some selected) :
    ∃ after, Insertion.word q (first :: rest) = first.1 :: after := by
  cases rest with
  | nil => simp only [Insertion.choose_singleton, Option.none_ne_some] at hs
  | cons current later =>
    cases ht : Insertion.choose q (current :: later) with
    | some chosen =>
      exact ⟨Insertion.word q (current :: later),
        SmallInsertionIntervalOrderSupport.word_cons_some q first _ chosen ht⟩
    | none =>
      cases hc : Insertion.coverCheck q first.1 (Insertion.firstCode current.2) with
      | false =>
        simp only [Insertion.choose_pair, ht, hc, Bool.cond_false, Option.none_ne_some] at hs
      | true =>
        refine ⟨current.2, ?_⟩
        simp only [Insertion.word, Insertion.choose_pair, ht, hc, Bool.cond_true,
          List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.singleton_append]


/-- Real whole dispatcher observations derive retention or an actual
reset, without an assumed reset position or prior lower Assignment. -/
theorem uninitialized_update (q head greater factor : Nat) (after out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor)) (hone : 1 < interpretation q factor)
    (hgreater : IsMultiplicativePrincipal (interpretation q greater))
    (hhead : interpretation q head < interpretation q greater)
    (hsmall : interpretation q factor < interpretation q greater)
    (ho : out ∈ Branches.execute ((q, factor), head :: after)) :
    (∃ rest, out = head :: rest) ∨
      ∃ input heads,
        base (ReplacementSupport.raisedBaseCode q head) < interpretation (ReplacementSupport.raisedBaseCode q head) input ∧
        interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater ∧
        heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input ∧
        lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) = interpretation q factor ∧
        List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) heads out := by
  rcases Branches.execute_branch q factor (head :: after) out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · exact Or.inl ⟨after ++ [factor], by simpa only [List.cons_append] using he⟩
  · obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff (Insertion.word q)).mp hi
    have hrelation := InsertionSupport.executeRows_relation q factor (head :: after) rows hr
    obtain ⟨row, rest, hrow, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrelation
    cases hc : Insertion.choose q rows with
    | some chosen =>
      obtain ⟨tail, hword⟩ := word_some_head q row rest chosen (by simpa only [hrows] using hc)
      exact Or.inl ⟨tail, he.symm.trans (by simpa only [hrows, hrow.1] using hword)⟩
    | none =>
      have hcond : row.2 ∈ ConditionalReplacement.execute q head factor := by simpa only [hrow.1] using hrow.2
      have hout : out = row.2 := by
        simp only [← he, Insertion.word, hc, hrows, List.head?_cons, Option.getD_some]
      obtain ⟨input, heads, hv, hs, ha, hl, hrel⟩ :=
        ContextAccumulationSupport.reset_assignment_last q head factor row.2 hh hf.1 hm hone hcond
      exact Or.inr ⟨input, heads, hs, hv.trans_lt (hgreater.2.2 hhead hsmall), ha, hl,
        by simpa only [hout] using hrel⟩

/-- Actual initialized provenance constructs the next input, complete
Assignment, LF and whole admitted output relation using real covariance. -/
theorem initialized_update (q : Nat) (original : List Nat) (head greater input factor : Nat)
    (heads suffix out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q original = true) (hh : head ∈ stripLast original)
    (hgreater : IsMultiplicativePrincipal (interpretation q greater))
    (hgreaterBound : interpretation q greater ≤ interpretation q (lastCode original))
    (ho : heads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) input)
    (hstrict : base (ReplacementSupport.raisedBaseCode q head) < interpretation (ReplacementSupport.raisedBaseCode q head) input)
    (hinput : interpretation (ReplacementSupport.raisedBaseCode q head) input < interpretation q greater)
    (hrel : List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) heads suffix)
    (hf : lowCheckCode q factor = true ∧ Comparison.acceptedCode q factor = true)
    (hm : IsMultiplicativePrincipal (interpretation q factor)) (hone : 1 < interpretation q factor)
    (hsmall : interpretation q factor < interpretation q greater)
    (hcut : interpretation q factor ≤ lf (interpretation (ReplacementSupport.raisedBaseCode q head) input))
    (hu : out ∈ Branches.execute ((q, factor), suffix)) :
    ∃ next nextHeads,
      base (ReplacementSupport.raisedBaseCode q head) < interpretation (ReplacementSupport.raisedBaseCode q head) next ∧
      interpretation (ReplacementSupport.raisedBaseCode q head) next < interpretation q greater ∧
      nextHeads ∈ Assignment.execute (ReplacementSupport.raisedBaseCode q head) next ∧
      lf (interpretation (ReplacementSupport.raisedBaseCode q head) next) = interpretation q factor ∧
      List.Forall₂ (SameEntry q (ReplacementSupport.raisedBaseCode q head)) nextHeads out := by
  have hraw := ((SourceTrackingRaw.trackingCheck_conditions q original).mp hw).2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec q head hraw).2.1
  have he := ReplacementFidelity.raisedBase_eq_betaCode q head hraw
  have hproperNe : stripLast original ≠ [] := by intro hn; rw [hn] at hh; exact List.not_mem_nil hh
  have hown := hinput.le.trans_lt (hgreaterBound.trans_lt
    (EndpointSupport.tracking_final_lt_endpoints q original hw hproperNe head hh))
  have hall := (Assignment.execute_spec _ input heads ho).2.1.2.1
  have hsuffix := ContextAssignmentReturn.raw_tracking_return q (SourceTrackingRaw.Support.rootCode q head)
    hroot heads suffix (by simpa only [he] using Assignment.execute_tracking _ input heads ho)
    (by simpa only [he] using hrel) (by
      intro c hc
      simpa only [he] using (hall c hc).trans_lt hown)
  obtain ⟨otherFactor, hsearch⟩ := ReplacementSupport.raisedSearch_returns q head factor hraw hf.1
  have hs := ReplacementSupport.raisedSearch_spec q head factor otherFactor hraw hf.1 hsearch
  have hd : SameEntry q (ReplacementSupport.raisedBaseCode q head) otherFactor factor := ⟨hf.1, hf.2, hs.2.2.symm⟩
  have hm' : IsMultiplicativePrincipal (interpretation (ReplacementSupport.raisedBaseCode q head) otherFactor) := hs.2.2.symm ▸ hm
  have hone' : 1 < interpretation (ReplacementSupport.raisedBaseCode q head) otherFactor := hs.2.2.symm ▸ hone
  have hcut' : interpretation (ReplacementSupport.raisedBaseCode q head) otherFactor ≤
      lf (interpretation (ReplacementSupport.raisedBaseCode q head) input) := hs.2.2.symm ▸ hcut
  have hlast := hcut'.trans (Assignment.execute_last_bounds _ input heads ho).1
  obtain ⟨word, hword⟩ := Branches.execute_returns _ otherFactor heads
    (Assignment.execute_tracking _ input heads ho) hs.1 hm' hlast
  obtain ⟨next, nextHeads, hproduct, hl, ha, hv, hb, hn, hvalues, hlastFactor⟩ :=
    FactorUpdateExecution.product_update_returns _ input otherFactor heads word
      ho hs.1 hm' hone' hstrict hcut' hword
  have hnextSmall : interpretation (ReplacementSupport.raisedBaseCode q head) next < interpretation q greater := by
    rw [hv, hs.2.2]
    exact hgreater.2.2 hinput hsmall
  have hvalues' : out.map (interpretation q) = word.map (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
    simpa only [he] using ContextBranchValues.branches_values_eq q (SourceTrackingRaw.Support.rootCode q head)
      input otherFactor factor heads suffix word out hroot (by simpa only [he] using ho)
      (by simpa only [he] using hstrict) (by simpa only [he] using hown)
      (by simpa only [he] using hrel) (by simpa only [he] using hs.1)
      (by simpa only [he] using hd) (by simpa only [he] using hm')
      (by simpa only [he] using hlast) (by simpa only [he] using hword) hu
  have hlastValues := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq (interpretation q)
    (interpretation (ReplacementSupport.raisedBaseCode q head)) suffix heads
    ((SourceTrackingRaw.trackingCheck_conditions q suffix).mp hsuffix).1 (ContextRowValues.returned_values hrel)
  have hb' : interpretation q factor ≤ interpretation q (lastCode suffix) := by
    rw [hlastValues]
    simpa only [hs.2.2] using hlast
  exact ⟨next, nextHeads, hb, hnextSmall, hn, by simpa only [hs.2.2] using hlastFactor,
    relation_of_values _ _ nextHeads out (hvalues'.trans hvalues)
      (branches_checked q factor suffix out hsuffix hf hm hb' (relation_checked hrel) hu)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ContextDefaultAccumulationSupport
