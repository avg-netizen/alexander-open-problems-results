import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextInitializedUpdate
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingLocalization

/-!
# Actual retained-head steps either retain the head or initialize a reset

The arbitrary old suffix is not a lower Assignment. Actual append retains
its first head; actual insertion with a selected transition also retains
that literal head. Only an observed NONE choice produces a genuine lower
Assignment at head times the real factor. The fixed greater raised row
derives its FIRST cover, so every alternative retains the original cut.
The reset's actual last MNF factor is derived by absorption or descending
canonical append. Whole checked tracking supplies every suffix caller.
No assigned initial suffix, selected index or reset observation is given.
Source-only uncompiled candidates in the original check-zero dictionary.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextUninitializedUpdate

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast stripLast_split)
open Alexander313.Wilken.MultiplicativeNormalForm

private theorem reference_tail (a : Nat) (xs : List Nat)
    (hr : SourceTrackingRaw.Reference (a :: xs)) : SourceTrackingRaw.Reference xs := by
  cases hr with
  | one a ha => exact .nil
  | cons a b xs ha hab hc ht => exact ht

theorem reference_suffix (before suffix : List Nat)
    (hr : SourceTrackingRaw.Reference (before ++ suffix)) : SourceTrackingRaw.Reference suffix := by
  revert hr
  induction before with
  | nil => intro hr; exact hr
  | cons a before ih => intro hr; exact ih (reference_tail a (before ++ suffix) hr)

theorem tracking_suffix (before suffix : List Nat) (hne : suffix ≠ [])
    (hh : SourceTrackingRaw.trackingCheck (before ++ suffix) = true) :
    SourceTrackingRaw.trackingCheck suffix = true := by
  have hs := (SourceTrackingRaw.trackingCheck_exact _).mp hh
  have hp := InsertionFidelity.stripLast_append_nonempty before suffix hne
  have hl := InsertionFidelity.lastCode_append_nonempty before suffix hne
  have href : SourceTrackingRaw.Reference (stripLast suffix) :=
    reference_suffix before _ (by simpa only [hp] using hs.2.1)
  apply (SourceTrackingRaw.trackingCheck_exact suffix).mpr
  refine ⟨hne, href, ?_, ?_, ?_, ?_⟩
  · simpa only [hl] using hs.2.2.1
  · simpa only [hl] using hs.2.2.2.1
  · simpa only [hl] using hs.2.2.2.2.1
  · by_cases hn : stripLast suffix = []
    · rw [if_pos hn]
      exact Order.one_le_iff_pos.mpr (by simpa only [hl] using hs.2.2.2.1)
    · have hwhole : stripLast (before ++ suffix) ≠ [] := by
        rw [hp]
        intro he
        exact hn (List.append_eq_nil_iff.mp he).2
      have hb := hs.2.2.2.2.2
      rw [if_neg hwhole, hl, hp, InsertionFidelity.lastCode_append_nonempty before _ hn] at hb
      simpa only [if_neg hn] using hb

private theorem cut_cover_head (before : List Nat) (head : Nat) (after : List Nat)
    (hne : before ≠ []) (hh : SourceTrackingRaw.trackingCheck (before ++ head :: after) = true) :
    Insertion.coverCheck (lastCode before) head = true := by
  obtain ⟨previous, he, hreverse⟩ := stripLast_split before hne
  have hl : lastCode before = previous := by rw [he, lastCode_append_singleton]
  have hadj := LocalizationProperties.tracking_adjacent (before ++ head :: after)
    (stripLast before) previous head after hh (by
      simpa only [List.append_assoc, List.singleton_append] using
        congrArg (fun xs : List Nat => xs ++ head :: after) he)
  have href : SourceTrackingRaw.Reference before := by simpa only [← he] using hadj.1
  have hraw : SourceTrackingRaw.Support.inputCheck (lastCode before) = true :=
    href.nodes _ (lastCode_mem before hne)
  exact (Insertion.coverCheck_exact _ _).mpr
    ⟨hraw, ((SourceLocalization.RootAdapter.inputCheck_exact head).mp hadj.2.1).1,
      by simpa only [hl] using hadj.2.2⟩

private theorem word_some_head (first : InsertionSupport.Row) (rest : List InsertionSupport.Row)
    (selected : Insertion.Candidate) (hs : Insertion.choose (first :: rest) = some selected) :
    ∃ after, Insertion.word (first :: rest) = first.1 :: after := by
  cases rest with
  | nil => simp only [Insertion.choose_singleton, Option.none_ne_some] at hs
  | cons current later =>
    cases ht : Insertion.choose (current :: later) with
    | some chosen =>
      exact ⟨Insertion.word (current :: later), CoverPrefixSupport.word_cons_some first _ chosen ht⟩
    | none =>
      cases hc : Insertion.coverCheck first.1 (Insertion.firstCode current.2) with
      | false =>
        simp only [Insertion.choose_pair, ht, hc, Bool.cond_false, Option.none_ne_some] at hs
      | true =>
        refine ⟨current.2, ?_⟩
        simp only [Insertion.word, Insertion.choose_pair, ht, hc, Bool.cond_true,
          List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.singleton_append]

private theorem reset_last_factor (head factor : Ordinal.{0})
    (hh : Ordinal.omega0 ^ head = head)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal factor)
    (hone : 1 < factor) : lf (head * factor) = factor := by
  have hhead := NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative head hh
  have hp := EpsilonOffsets.epsilon_pos_principal hh
  have hlarge := EpsilonOffsets.epsilon_one_lt hh
  by_cases ht : head < factor
  · have he : head * factor = factor := by
      apply le_antisymm
      · apply (Ordinal.mul_le_iff_of_isSuccLimit
          (Ordinal.isSuccLimit_of_isPrincipal_add hone hm.2.1)).mpr
        intro a ha
        exact (hm.2.2 ht ha).le
      · exact Ordinal.le_mul_right factor hp.1
    rw [he]
    exact lf_multiplicative hm
  · exact (AppendFactor.prefix_last hlarge hp.2 hm hone
      (by rw [lf_multiplicative hhead]; exact le_of_not_gt ht)).2.1

/-- Every actual update of an arbitrary retained-head suffix derives one
of two honest states: the head is literally retained, or a real reset
Assignment and its computed LF initialize subsequent descending updates. -/
theorem uninitialized_update (original : List Nat) (head greater factor : Nat)
    (before after ys out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hne : before ≠ [])
    (hfull : SourceTrackingRaw.trackingCheck (before ++ head :: after) = true)
    (hfront : interpretation 0 (lastCode before) < interpretation 0 head)
    (hf : Theta.acceptedLowCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode (before ++ head :: after)))
    (hg : lowCheckCode 0 greater = true)
    (hmg : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hsmall : interpretation 0 factor < interpretation 0 greater)
    (hy : ys ∈ Replacement.raisedReplacement head greater)
    (hcover : Insertion.coverCheck (lastCode before) (Insertion.firstCode ys) = true)
    (ho : out ∈ Branches.execute (factor, before ++ head :: after)) :
    ∃ suffix, out = before ++ suffix ∧
      ((∃ nextAfter, suffix = head :: nextAfter) ∨
        ∃ input heads,
          NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input =
            interpretation 0 head * interpretation 0 factor ∧
          NativeContext.base (ReplacementSupport.raisedBaseCode head) <
            NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ∧
          NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input < interpretation 0 greater ∧
          heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
            (ReplacementSupport.raisedBaseCode head) input ∧
          lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) = interpretation 0 factor ∧
          List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix) := by
  have hraw := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hfLow := ((Theta.acceptedLowCode_iff 0 factor).mp hf).1
  have hsuffix := tracking_suffix before (head :: after) (List.cons_ne_nil _ _) hfull
  obtain ⟨suffix, hs, hcut⟩ := ContextSuffixFirstCut.branches_suffix_execution factor before
    head after out hne hfull hsuffix hfront ho
  have hc := cut_cover_head before head after hne hfull
  rcases Branches.execute_branch factor (head :: after) suffix hs with ⟨hflag, he⟩ | ⟨hflag, hi⟩
  · have hshead : suffix = head :: (after ++ [factor]) := by
      simpa only [List.cons_append] using he
    have hpass : Insertion.coverCheck (lastCode before) (Insertion.firstCode suffix) = true := by
      simpa only [hshead, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
    exact ⟨suffix, hcut hpass, Or.inl ⟨after ++ [factor], hshead⟩⟩
  · obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff Insertion.word).mp hi
    have hrelation := InsertionSupport.executeRows_relation factor (head :: after) rows hr
    obtain ⟨row, rest, hrow, hrest, hrows⟩ := List.forall₂_cons_left_iff.mp hrelation
    cases hchoice : Insertion.choose rows with
    | some selected =>
      obtain ⟨nextAfter, hwhead⟩ := word_some_head row rest selected
        (by simpa only [hrows] using hchoice)
      have hwhead' : Insertion.word rows = head :: nextAfter := by
        simpa only [hrows, hrow.1] using hwhead
      have hshead : suffix = head :: nextAfter := he.symm.trans hwhead'
      have hpass : Insertion.coverCheck (lastCode before) (Insertion.firstCode suffix) = true := by
        simpa only [hshead, Insertion.firstCode, List.head?_cons, Option.getD_some] using hc
      exact ⟨suffix, hcut hpass, Or.inl ⟨nextAfter, hshead⟩⟩
    | none =>
      have hcond : row.2 ∈ ConditionalReplacement.execute head factor := by
        simpa only [hrow.1] using hrow.2
      have hsrow : suffix = row.2 := by
        simp only [← he, Insertion.word, hchoice, hrows, List.head?_cons, Option.getD_some]
      have hpass : Insertion.coverCheck (lastCode before) (Insertion.firstCode suffix) = true := by
        rw [hsrow]
        exact ContextResetOrder.cover_conditional_reset head factor greater (lastCode before)
          row.2 ys hraw hfLow hg hm hmg hone hhead hsmall hcond hy hcover
      obtain ⟨input, heads, hl, hv, ht, ha, hrel⟩ :=
        ContextInitialization.conditional_assignment head factor row.2 hraw hfLow hm hone hcond
      have hlast : lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) =
          interpretation 0 factor := by
        rw [hv]
        exact reset_last_factor _ _ ((SourceTrackingRaw.Support.inputCheck_exact head).mp hraw).2.2 hm hone
      refine ⟨suffix, hcut hpass, Or.inr ⟨input, heads, hv, ht, hv.trans_lt (hmg.2.2 hhead hsmall),
        ha, hlast, ?_⟩⟩
      simpa only [hsrow] using hrel

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextUninitializedUpdate
