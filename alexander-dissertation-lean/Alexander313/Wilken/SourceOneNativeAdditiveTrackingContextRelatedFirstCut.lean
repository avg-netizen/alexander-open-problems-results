import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextInitialization

/-!
# A genuine related reset suffix advances through the actual FIRST cut

An ordinary reset need not use the literal finite return spelling. Its real
entry relation to an independently executing lower Assignment still derives
the complete original RAW tracker and OWN interval. The next suffix branch
is reconstructed from actual whole execution. Covering its actual next
FIRST retains the literal preceding prefix, and contextual branch VALUES
derive the next admitted entry relation. No arbitrary old suffix is declared
an Assignment, and no accumulated update equation is assumed. Original
source zero is retained throughout. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextRelatedFirstCut

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceAdditiveTracking.InsertionFidelitySupport (stripLast_append_nonempty)

theorem relation_values {r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (Replacement.EntryMatches r) xs ys) :
    ys.map (interpretation 0) = xs.map (NativeContext.interpretation r) := by
  induction hr with
  | nil => rfl
  | cons he ht ih => simp only [List.map_cons, he.2, ih]

theorem relation_checked {r : Nat} {xs ys : List Nat}
    (hr : List.Forall₂ (Replacement.EntryMatches r) xs ys) :
    ∀ d ∈ ys, Theta.acceptedLowCode 0 d = true := by
  induction hr with
  | nil => intro d hd; exact False.elim (List.not_mem_nil hd)
  | @cons c d xs ys he ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he.1
    · exact ih a ha

private theorem relation_of_values (r : Nat) (xs ys : List Nat)
    (hv : ys.map (interpretation 0) = xs.map (NativeContext.interpretation r))
    (ha : ∀ d ∈ ys, Theta.acceptedLowCode 0 d = true) :
    List.Forall₂ (Replacement.EntryMatches r) xs ys := by
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
      exact .cons ⟨ha d List.mem_cons_self, he.1⟩
        (ih ds he.2 (fun a hm => ha a (List.mem_cons_of_mem _ hm)))

/-- Genuine lower execution and the actual original tracker FINAL derive
the complete RAW tracking property at any admitted related spelling. -/
theorem assignment_related_tracking (original : List Nat) (head input : Nat)
    (heads suffix : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true)
    (hh : head ∈ stripLast original)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode original))
    (hrel : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix) :
    SourceTrackingRaw.trackingCheck suffix = true ∧
      suffix.map (interpretation 0) = heads.map (NativeContext.interpretation
        (ReplacementSupport.raisedBaseCode head)) ∧
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input <
        Enclosure.sourceAlphaPlus (SourceTrackingRaw.Support.rootCode head) := by
  have hhead := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hne : stripLast original ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hown := hinput.trans_lt (EndpointSupport.tracking_final_lt_endpoints original hw hne head hh)
  have hall := (NativeContext.SourceAdditiveTracking.Assignment.execute_spec _ input heads ho).2.1.2.1
  have htrack := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input heads ho
  have ht : SourceTrackingRaw.trackingCheck suffix = true :=
    ContextAssignmentReturn.raw_tracking_return (SourceTrackingRaw.Support.rootCode head) hroot heads suffix
      (by simpa only [he] using htrack) (by simpa only [he] using hrel) (by
        intro c hc
        simpa only [he] using (hall c hc).trans_lt hown)
  exact ⟨ht, relation_values hrel, hown⟩

private theorem first_values {r : Nat} {xs ys : List Nat} (hne : xs ≠ [])
    (hv : xs.map (interpretation 0) = ys.map (NativeContext.interpretation r)) :
    interpretation 0 (Insertion.firstCode xs) =
      NativeContext.interpretation r (NativeContext.SourceAdditiveTracking.Insertion.firstCode ys) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a xs =>
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b ys =>
      simpa only [Insertion.firstCode, NativeContext.SourceAdditiveTracking.Insertion.firstCode,
        List.head?_cons, Option.getD_some] using (List.cons.inj hv).1

private theorem branches_checked (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : Theta.acceptedLowCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (hc : ∀ d ∈ heads, Theta.acceptedLowCode 0 d = true)
    (ho : out ∈ Branches.execute (factor, heads)) :
    ∀ d ∈ out, Theta.acceptedLowCode 0 d = true := by
  rcases Branches.execute_branch factor heads out ho with ⟨hflag, he⟩ | ⟨hflag, hi⟩
  · intro d hd
    rw [he] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hc d hd
    · simpa only [List.mem_singleton.mp hd] using hf
  · obtain ⟨rows, hr, hheads, hout, hchecked, hcases⟩ :=
      Insertion.execute_spec factor heads out hh ((Theta.acceptedLowCode_iff 0 factor).mp hf).1 hm hb hi
    rcases hcases with ⟨first, rest, hrows, he, hn⟩ |
      ⟨before, current, after, hne, hrows, he, hcover, hn⟩
    · intro d hd
      exact (hchecked first (by rw [hrows]; exact List.mem_cons_self)).2 d (by simpa only [he] using hd)
    · intro d hd
      rw [he] at hd
      rcases List.mem_append.mp hd with hd | hd
      · apply hc d
        rw [← hheads, hrows, List.map_append]
        exact List.mem_append_left _ hd
      · exact (hchecked current (by
          rw [hrows]
          exact List.mem_append_right _ List.mem_cons_self)).2 d hd

/-- The actual next lower branch supplies its FIRST cover. Every original
suffix caller and its next entry relation follow from actual execution;
the suffix's current spelling is not required to be literal returnWord. -/
theorem contextual_update_first_cut (original : List Nat)
    (head input factor otherFactor : Nat) (before heads suffix word out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode original))
    (hrel : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix)
    (hne : before ≠ [])
    (hfull : SourceTrackingRaw.trackingCheck (before ++ suffix) = true)
    (hbefore : interpretation 0 (lastCode before) ≤ interpretation 0 head)
    (hf : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) otherFactor = true)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) otherFactor factor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor))
    (hfactor : 1 < NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor)
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor ≤
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) (lastCode heads))
    (hcover : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)
      (NativeContext.SourceAdditiveTracking.Insertion.firstCode word) ≤
        SourceTrackingRaw.Support.muValue (lastCode before))
    (ht : word ∈ NativeContext.SourceAdditiveTracking.Branches.execute
      ((ReplacementSupport.raisedBaseCode head, otherFactor), heads))
    (hu : out ∈ Branches.execute (factor, before ++ suffix)) :
    ∃ nextSuffix, out = before ++ nextSuffix ∧
      nextSuffix ∈ Branches.execute (factor, suffix) ∧
      List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) word nextSuffix := by
  have hs := assignment_related_tracking original head input heads suffix hw hh ho hinput hrel
  have hhead := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hbase := (ReplacementSupport.raisedBaseCode_spec head hhead).2.1
  have hsuffixNe := ((SourceTrackingRaw.trackingCheck_exact suffix).mp hs.1).1
  have hraw : SourceTrackingRaw.Support.inputCheck (lastCode before) = true := by
    apply ((SourceTrackingRaw.trackingCheck_exact _).mp hfull).2.1.nodes
    rw [stripLast_append_nonempty before suffix hsuffixNe]
    exact List.mem_append_left _ (lastCode_mem before hne)
  obtain ⟨first, rest, hheads⟩ := List.exists_cons_of_ne_nil
    (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty _ input heads ho)
  have hr := hrel
  rw [hheads] at hr
  obtain ⟨other, otherRest, hfirst, htail, hsuffix⟩ := List.forall₂_cons_left_iff.mp hr
  have hfirstStrict := NativeContext.SourceAdditiveTracking.AssignmentFirst.execute_first_gt_base
    _ input first rest (by simpa only [hheads] using ho) hstrict
  have hfront : interpretation 0 (lastCode before) < interpretation 0 other := by
    rw [hfirst.2]
    exact (by simpa only [hbase] using hbefore).trans_lt hfirstStrict
  obtain ⟨nextSuffix, hn, hcut⟩ := ContextSuffixFirstCut.branches_suffix_execution factor
    before other otherRest out hne (by simpa only [hsuffix] using hfull)
    (by simpa only [hsuffix] using hs.1) hfront (by simpa only [hsuffix] using hu)
  have hn' : nextSuffix ∈ Branches.execute (factor, suffix) := by simpa only [hsuffix] using hn
  have hv : nextSuffix.map (interpretation 0) =
      word.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
    simpa only [he] using ContextBranchValues.branches_values_eq
      (SourceTrackingRaw.Support.rootCode head) input factor otherFactor suffix heads nextSuffix word hroot
      (by simpa only [he] using ho) (by simpa only [he] using hstrict)
      (by simpa only [he] using hs.2.2) (by simpa only [he] using hrel)
      (by simpa only [he] using hf) (by simpa only [he] using hd)
      (by simpa only [he] using hm) (by simpa only [he] using hb) hn'
      (by simpa only [he] using ht)
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation 0) (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head))
    suffix heads hsuffixNe hs.2.1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor) := by
    rw [hd.2]; exact hm
  have hb' : interpretation 0 factor ≤ interpretation 0 (lastCode suffix) := by
    rw [hd.2, hlast]; exact hb
  have htrack := Branches.execute_tracking factor suffix nextSuffix hs.1
    ((Theta.acceptedLowCode_iff 0 factor).mp hd.1).1 hm'
    (by simpa only [hd.2] using hfactor) hb' hn'
  have hspec := (SourceTrackingRaw.trackingCheck_exact nextSuffix).mp htrack
  have hfirstmem : Insertion.firstCode nextSuffix ∈ nextSuffix := by
    cases hnext : nextSuffix with
    | nil => exact False.elim (hspec.1 hnext)
    | cons c cs =>
      simp only [Insertion.firstCode, hnext, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  have hpass : Insertion.coverCheck (lastCode before) (Insertion.firstCode nextSuffix) = true := by
    apply (Insertion.coverCheck_exact _ _).mpr
    refine ⟨hraw, (hspec.source_domain _ hfirstmem).1, ?_⟩
    rw [first_values hspec.1 hv]
    exact hcover
  exact ⟨nextSuffix, hcut hpass, hn', relation_of_values _ word nextSuffix hv
    (branches_checked factor suffix nextSuffix hs.1 hd.1 hm' hb' (relation_checked hrel) hn')⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextRelatedFirstCut
