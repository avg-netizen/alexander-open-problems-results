import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextAccumulation
import Alexander313.Wilken.MultiplicativeLastFactorProduct

/-!
# Genuine retained-head and reset updates without a preceding cut

An actual default comparison starts at the original first proper head.
Append or SOME retains that literal head; NONE constructs a genuine lower
Assignment at the head-factor product. Once initialized, real contextual
branch covariance and the actual product producer construct every next
Assignment and admitted original spelling. No preceding mu cover is
needed, and no arbitrary old suffix is declared an Assignment.
Source-only uncompiled candidates in literal original source zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextDefaultAccumulationSupport

open NativeContext.SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)
open Alexander313.Wilken.MultiplicativeNormalForm

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

/-- The real whole dispatcher retains its head or supplies the first
actual lower Assignment. No observed reset choice is supplied. -/
theorem uninitialized_update (head greater factor : Nat) (after out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : Theta.acceptedLowCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hgreater : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hsmall : interpretation 0 factor < interpretation 0 greater)
    (ho : out ∈ Branches.execute (factor, head :: after)) :
    (∃ rest, out = head :: rest) ∨
      ∃ input heads,
        NativeContext.base (ReplacementSupport.raisedBaseCode head) <
          NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ∧
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input < interpretation 0 greater ∧
        heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
          (ReplacementSupport.raisedBaseCode head) input ∧
        lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) = interpretation 0 factor ∧
        List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads out := by
  rcases Branches.execute_branch factor (head :: after) out ho with ⟨ha, he⟩ | ⟨ha, hi⟩
  · exact Or.inl ⟨after ++ [factor], by simpa only [List.cons_append] using he⟩
  · obtain ⟨rows, hr, he⟩ := (Part.mem_map_iff Insertion.word).mp hi
    have hrelation := InsertionSupport.executeRows_relation factor (head :: after) rows hr
    obtain ⟨row, rest, hrow, ht, hrows⟩ := List.forall₂_cons_left_iff.mp hrelation
    cases hc : Insertion.choose rows with
    | some chosen =>
      obtain ⟨tail, hword⟩ := word_some_head row rest chosen (by simpa only [hrows] using hc)
      exact Or.inl ⟨tail, he.symm.trans (by simpa only [hrows, hrow.1] using hword)⟩
    | none =>
      have hcond : row.2 ∈ ConditionalReplacement.execute head factor := by simpa only [hrow.1] using hrow.2
      have hout : out = row.2 := by
        simp only [← he, Insertion.word, hc, hrows, List.head?_cons, Option.getD_some]
      obtain ⟨input, heads, hl, hv, hs, ho, hrel⟩ := ContextInitialization.conditional_assignment
        head factor row.2 hh ((Theta.acceptedLowCode_iff 0 factor).mp hf).1 hm hone hcond
      have hp := EpsilonOffsets.epsilon_pos_principal ((SourceTrackingRaw.Support.inputCheck_exact head).mp hh).2.2
      have hlast : lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) =
          interpretation 0 factor := by
        rw [hv]
        exact LastFactorProduct.lf_principal_mul _ _ hp.1 hp.2 hm hone
      exact Or.inr ⟨input, heads, hs, hv.trans_lt (hgreater.2.2 hhead hsmall), ho, hlast,
        by simpa only [hout] using hrel⟩

/-- Actual initialized whole-word provenance constructs the next product
and Assignment. The real original branch supplies every admitted output. -/
theorem initialized_update (original : List Nat) (head greater input factor : Nat)
    (heads suffix out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hgreater : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hgreaterBound : interpretation 0 greater ≤ interpretation 0 (lastCode original))
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input < interpretation 0 greater)
    (hrel : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix)
    (hf : Theta.acceptedLowCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hsmall : interpretation 0 factor < interpretation 0 greater)
    (hcut : interpretation 0 factor ≤ lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input))
    (hu : out ∈ Branches.execute (factor, suffix)) :
    ∃ next nextHeads,
      NativeContext.base (ReplacementSupport.raisedBaseCode head) <
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next ∧
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next < interpretation 0 greater ∧
      nextHeads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (ReplacementSupport.raisedBaseCode head) next ∧
      lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next) = interpretation 0 factor ∧
      List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) nextHeads out := by
  have hraw := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hsuffix := ContextRelatedFirstCut.assignment_related_tracking original head input heads suffix
    hw hh ho (hinput.le.trans hgreaterBound) hrel
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hraw).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hraw
  have hfLow := ((Theta.acceptedLowCode_iff 0 factor).mp hf).1
  obtain ⟨otherFactor, hsearch⟩ := ReplacementSupport.raisedSearch_returns head factor hraw hfLow
  have hs := ReplacementSupport.raisedSearch_spec head factor otherFactor hfLow hsearch
  have hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) otherFactor factor := ⟨hf, hs.2.2.symm⟩
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor) := hs.2.2.symm ▸ hm
  have hone' : 1 < NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor := hs.2.2.symm ▸ hone
  have hcut' : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor ≤
      lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) := hs.2.2.symm ▸ hcut
  have hlast := hcut'.trans (NativeContext.SourceAdditiveTracking.Assignment.execute_last_bounds _ input heads ho).1
  obtain ⟨word, hword⟩ := NativeContext.SourceAdditiveTracking.Branches.execute_returns _ otherFactor heads
    (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input heads ho) hs.1 hm' hlast
  obtain ⟨next, nextHeads, hproduct, hl, ha, hv, hb, hn, hvalues, hlastFactor⟩ :=
    NativeContext.SourceAdditiveTracking.FactorUpdateExecution.product_update_returns _ input otherFactor heads word
      ho hs.1 hm' hone' hstrict hcut' hword
  have hnextSmall : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next < interpretation 0 greater := by
    rw [hv, hs.2.2]
    exact hgreater.2.2 hinput hsmall
  have hvalues' : out.map (interpretation 0) = word.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
    simpa only [he] using ContextBranchValues.branches_values_eq (SourceTrackingRaw.Support.rootCode head)
      input factor otherFactor suffix heads out word hroot (by simpa only [he] using ho)
      (by simpa only [he] using hstrict) (by simpa only [he] using hsuffix.2.2)
      (by simpa only [he] using hrel) (by simpa only [he] using hs.1)
      (by simpa only [he] using hd) (by simpa only [he] using hm')
      (by simpa only [he] using hlast) hu (by simpa only [he] using hword)
  have hlastValues := SourceAdditiveTrackingWordBounds.lastCode_values_eq (interpretation 0)
    (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) suffix heads
    ((SourceTrackingRaw.trackingCheck_exact suffix).mp hsuffix.1).1 hsuffix.2.1
  have hb' : interpretation 0 factor ≤ interpretation 0 (lastCode suffix) := by
    rw [hlastValues]
    simpa only [hs.2.2] using hlast
  refine ⟨next, nextHeads, hb, hnextSmall, hn, by simpa only [hs.2.2] using hlastFactor, ?_⟩
  exact relation_of_values _ nextHeads out (hvalues'.trans hvalues)
    (branches_checked factor suffix out hsuffix.1 hf hm hb' (ContextRelatedFirstCut.relation_checked hrel) hu)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextDefaultAccumulationSupport
