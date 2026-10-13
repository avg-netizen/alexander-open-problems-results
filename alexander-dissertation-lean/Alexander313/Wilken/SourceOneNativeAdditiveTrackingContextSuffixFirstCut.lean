import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextBranchesCut

/-!
# A covered actual suffix FIRST suffices to retain the source cut

The actual right-priority choice already retains an earlier cut when its
suffix selects a later transition. Otherwise that suffix is its genuine
first replacement, and covering its computed FIRST supplies exactly the
missing boundary test. Thus no bound of the entire suffix by the preceding
mu is needed. Actual finite row execution constructs the independent suffix
procedure before this FIRST test is used. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextSuffixFirstCut

open InsertionSupport (Row Matches)
open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceAdditiveTracking.InsertionFidelitySupport (stripLast_append_nonempty)
open Hereditary.SourceAdditiveTrackingWordBounds (lastCode_append_nonempty)

private theorem suffix_cover_choose (before : List Row) (previous current : Row)
    (after : List Row)
    (hc : Insertion.coverCheck previous.1
      (Insertion.firstCode (Insertion.word (current :: after))) = true) :
    ∃ selected, Insertion.choose (before ++ previous :: current :: after) = some selected := by
  induction before with
  | nil =>
    cases hs : Insertion.choose (current :: after) with
    | some selected =>
      exact ⟨(selected.1 + 1, selected.2), by
        simpa only [List.nil_append] using CoverPrefixSupport.choose_cons_some previous _ selected hs⟩
    | none =>
      have hp : Insertion.coverCheck previous.1 (Insertion.firstCode current.2) = true := by
        simpa only [Insertion.word, hs, List.head?_cons, Option.getD_some] using hc
      exact ⟨(1, current.2), by
        simp only [List.nil_append, Insertion.choose_pair, hs, hp, Bool.cond_true]⟩
  | cons row before ih =>
    obtain ⟨selected, hs⟩ := ih
    exact ⟨(selected.1 + 1, selected.2), by
      simpa only [List.cons_append] using CoverPrefixSupport.choose_cons_some row _ selected hs⟩

theorem word_covered_suffix (before : List Row) (previous current : Row)
    (after : List Row)
    (hc : Insertion.coverCheck previous.1
      (Insertion.firstCode (Insertion.word (current :: after))) = true) :
    Insertion.word (before ++ previous :: current :: after) =
      (before.map Prod.fst ++ [previous.1]) ++ Insertion.word (current :: after) := by
  induction before with
  | nil =>
    cases hs : Insertion.choose (current :: after) with
    | some selected =>
      simpa only [List.map_nil, List.nil_append, List.singleton_append] using
        CoverPrefixSupport.word_cons_some previous _ selected hs
    | none =>
      have hp : Insertion.coverCheck previous.1 (Insertion.firstCode current.2) = true := by
        simpa only [Insertion.word, hs, List.head?_cons, Option.getD_some] using hc
      simpa only [List.map_nil, List.nil_append] using
        ContextInsertionCutSupport.word_passing_cut [] previous current after hp
  | cons row before ih =>
    obtain ⟨selected, hs⟩ := suffix_cover_choose before previous current after hc
    simpa only [List.cons_append, List.map_cons,
      CoverPrefixSupport.word_cons_some row _ selected hs] using
        congrArg (List.cons row.1) ih

/-- Actual whole execution derives the independently executing suffix.
Its genuine computed FIRST cover then implies literal prefix retention. -/
theorem insertion_suffix_execution (factor : Nat) (before : List Nat)
    (first : Nat) (after out : List Nat) (hne : before ≠ [])
    (ho : out ∈ Insertion.execute (factor, before ++ first :: after)) :
    ∃ suffix, suffix ∈ Insertion.execute (factor, first :: after) ∧
      (Insertion.coverCheck (lastCode before) (Insertion.firstCode suffix) = true →
        out = before ++ suffix) := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff Insertion.word).mp ho
  obtain ⟨prefix, rest, hrows, hp, hrest⟩ := ContextInsertionCutSupport.executeRows_split
    factor before (first :: after) rows hr
  have hprefixNe : prefix ≠ [] := by
    intro he
    exact hne (by simpa only [he, List.map_nil] using hp.symm)
  have hrestHeads := InsertionSupport.relation_heads factor
    (InsertionSupport.executeRows_relation factor (first :: after) rest hrest)
  have hrestNe : rest ≠ [] := by
    intro he
    simp only [he, List.map_nil, List.nil_ne_cons] at hrestHeads
  obtain ⟨previous, hprefix, hlast⟩ := stripLast_split prefix hprefixNe
  obtain ⟨current, later, htail⟩ := List.exists_cons_of_ne_nil hrestNe
  have hbefore : before = (stripLast prefix).map Prod.fst ++ [previous.1] := by
    calc
      before = prefix.map Prod.fst := hp.symm
      _ = (stripLast prefix ++ [previous]).map Prod.fst := congrArg (List.map Prod.fst) hprefix
      _ = (stripLast prefix).map Prod.fst ++ [previous.1] := by
        rw [List.map_append, List.map_singleton]
  have hprevious : lastCode before = previous.1 := by
    rw [hbefore, lastCode_append_singleton]
  refine ⟨Insertion.word rest, Part.mem_map Insertion.word hrest, ?_⟩
  intro hc
  have hcover : Insertion.coverCheck previous.1
      (Insertion.firstCode (Insertion.word (current :: later))) = true := by
    simpa only [hprevious, htail] using hc
  calc
    out = Insertion.word rows := hout.symm
    _ = Insertion.word (prefix ++ rest) := congrArg Insertion.word hrows
    _ = Insertion.word ((stripLast prefix ++ [previous]) ++ rest) :=
      congrArg (fun xs => Insertion.word (xs ++ rest)) hprefix
    _ = Insertion.word (stripLast prefix ++ previous :: current :: later) := by
      rw [htail, List.append_assoc, List.singleton_append]
    _ = ((stripLast prefix).map Prod.fst ++ [previous.1]) ++
        Insertion.word (current :: later) := word_covered_suffix _ previous current later hcover
    _ = before ++ Insertion.word rest := by rw [← hbefore, ← htail]

theorem branches_suffix_execution (factor : Nat) (before : List Nat)
    (first : Nat) (after out : List Nat) (hne : before ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (before ++ first :: after) = true)
    (ht : SourceTrackingRaw.trackingCheck (first :: after) = true)
    (hfront : interpretation 0 (lastCode before) < interpretation 0 first)
    (ho : out ∈ Branches.execute (factor, before ++ first :: after)) :
    ∃ suffix, suffix ∈ Branches.execute (factor, first :: after) ∧
      (Insertion.coverCheck (lastCode before) (Insertion.firstCode suffix) = true →
        out = before ++ suffix) := by
  have hflag := ContextBranchesCut.appendCheck_at_cut factor before first after hne hh ht hfront
  rcases Branches.execute_branch factor (before ++ first :: after) out ho with
    ⟨ha, he⟩ | ⟨ha, hi⟩
  · have hsflag : BranchesSupport.appendCheck factor (first :: after) = true := hflag.symm.trans ha
    refine ⟨(first :: after) ++ [factor], ?_, fun _ => ?_⟩
    · simpa only [Branches.execute, hsflag, Bool.cond_true] using
        Part.mem_some ((first :: after) ++ [factor])
    · simpa only [List.append_assoc] using he
  · have hsflag : BranchesSupport.appendCheck factor (first :: after) = false := hflag.symm.trans ha
    obtain ⟨suffix, hs, hcut⟩ := insertion_suffix_execution factor before first after out hne hi
    exact ⟨suffix, by simpa only [Branches.execute, hsflag, Bool.cond_false] using hs, hcut⟩

private theorem suffix_first_values {r : Nat} {xs ys : List Nat} (hne : xs ≠ [])
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

/-- The actual next lower word supplies only its FIRST cover. Both branch
programs execute independently; suffix reconstruction and real contextual
mu/VALUES covariance derive the complete unchanged original prefix law. -/
theorem returned_contextual_update_first_cut (original : List Nat)
    (head input factor otherFactor : Nat) (before heads word out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode original))
    (hne : before ≠ [])
    (hfull : SourceTrackingRaw.trackingCheck (before ++ Replacement.returnWord head heads) = true)
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
    (hu : out ∈ Branches.execute (factor, before ++ Replacement.returnWord head heads)) :
    out.map (interpretation 0) = before.map (interpretation 0) ++
      word.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
  have hhead := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hbase := (ReplacementSupport.raisedBaseCode_spec head hhead).2.1
  have hreturn := ContextAssignmentReturn.assignment_return original head input heads hw hh ho hinput
  have hreturnedNe := ((SourceTrackingRaw.trackingCheck_exact _).mp hreturn.1).1
  have hraw : SourceTrackingRaw.Support.inputCheck (lastCode before) = true := by
    apply ((SourceTrackingRaw.trackingCheck_exact _).mp hfull).2.1.nodes
    rw [stripLast_append_nonempty before _ hreturnedNe]
    exact List.mem_append_left _ (lastCode_mem before hne)
  obtain ⟨first, rest, hheads⟩ := List.exists_cons_of_ne_nil
    (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty _ input heads ho)
  have hr := hreturn.2.1
  rw [hheads] at hr
  obtain ⟨other, otherRest, hfirst, htail, hreturned⟩ := List.forall₂_cons_left_iff.mp hr
  have hfirstStrict := NativeContext.SourceAdditiveTracking.AssignmentFirst.execute_first_gt_base
    _ input first rest (by simpa only [hheads] using ho) hstrict
  have hfront : interpretation 0 (lastCode before) < interpretation 0 other := by
    rw [hfirst.2]
    exact (by simpa only [hbase] using hbefore).trans_lt hfirstStrict
  obtain ⟨suffix, hsuffix, hcut⟩ := branches_suffix_execution factor before other otherRest out hne
    (by simpa only [hreturned] using hfull) (by simpa only [hreturned] using hreturn.1)
    hfront (by simpa only [hreturned] using hu)
  have hs : suffix ∈ Branches.execute (factor, Replacement.returnWord head heads) := by
    simpa only [hreturned] using hsuffix
  have hv := ContextBranchValues.returned_branches_values_eq original head input factor otherFactor
    heads suffix word hw hh ho hstrict hinput hf hd hm hb hs ht
  have hlast := Hereditary.SourceAdditiveTrackingWordBounds.lastCode_values_eq
    (interpretation 0) (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head))
    (Replacement.returnWord head heads) heads hreturnedNe hreturn.2.2.1
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor) := by
    rw [hd.2]; exact hm
  have hb' : interpretation 0 factor ≤ interpretation 0 (lastCode (Replacement.returnWord head heads)) := by
    rw [hd.2, hlast]; exact hb
  have htracker := Branches.execute_tracking factor (Replacement.returnWord head heads) suffix
    hreturn.1 ((Theta.acceptedLowCode_iff 0 factor).mp hd.1).1 hm'
    (by simpa only [hd.2] using hfactor) hb' hs
  have hspec := (SourceTrackingRaw.trackingCheck_exact suffix).mp htracker
  have hfirstmem : Insertion.firstCode suffix ∈ suffix := by
    cases he : suffix with
    | nil => exact False.elim (hspec.1 he)
    | cons c cs =>
      simp only [Insertion.firstCode, he, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  have hpass : Insertion.coverCheck (lastCode before) (Insertion.firstCode suffix) = true := by
    apply (Insertion.coverCheck_exact _ _).mpr
    refine ⟨hraw, (hspec.source_domain _ hfirstmem).1, ?_⟩
    rw [suffix_first_values hspec.1 hv]
    exact hcover
  simp only [hcut hpass, List.map_append, hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextSuffixFirstCut
