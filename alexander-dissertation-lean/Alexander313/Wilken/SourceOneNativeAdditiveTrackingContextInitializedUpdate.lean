import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextResetOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFactorUpdateExecution

/-!
# A real initialized suffix advances without a supplied next assignment

The actual descending factor constructs its lower code by genuine search.
The independently executing current Assignment and its printed branch
construct the actual next product and complete next Assignment, including
its last MNF factor. Genuine M closure bounds the whole next input below
the fixed greater factor. Full-P-left/M-right order compares the next word
with the fixed raised replacement, deriving the needed FIRST cover.
The admitted related-suffix cut then retains the literal original prefix
and supplies a complete next entry relation. No next code, next Assignment,
whole-product mu cover or arbitrary initial suffix is provided. The current
genuine suffix provenance and actual descending LF bound remain explicit.
Source-only uncompiled candidates on literal original source zero.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextInitializedUpdate

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

private theorem first_le_of_lex (r : Nat) (xs ys : List Nat)
    (hx : xs ≠ []) (hy : ys ≠ [])
    (hlex : List.Lex (· < ·) (xs.map (NativeContext.interpretation r)) (ys.map (interpretation 0))) :
    NativeContext.interpretation r (NativeContext.SourceAdditiveTracking.Insertion.firstCode xs) ≤
      interpretation 0 (Insertion.firstCode ys) := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons a as =>
    cases ys with
    | nil => exact False.elim (hy rfl)
    | cons b bs =>
      simp only [NativeContext.SourceAdditiveTracking.Insertion.firstCode,
        Insertion.firstCode, List.head?_cons, Option.getD_some]
      exact List.head_le_of_lt hlex

/-- Any genuinely executing lower Assignment below the fixed raised M
input has a FIRST no larger than the actual greater returned row FIRST. -/
theorem assignment_first_le_raised (head greater input : Nat) (word ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hg : lowCheckCode 0 greater = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (ho : word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hlt : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input <
      interpretation 0 greater)
    (hy : ys ∈ Replacement.raisedReplacement head greater) :
    NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)
      (NativeContext.SourceAdditiveTracking.Insertion.firstCode word) ≤
        interpretation 0 (Insertion.firstCode ys) := by
  obtain ⟨rightWord, hr, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head greater ys hh hg hm hhead hy
  obtain ⟨right, hs, hword⟩ := (Part.mem_map_iff _).mp hr
  have hi := ReplacementSupport.raisedSearch_multiplicative head greater right hh hg hm hhead hs
  have hs' := ReplacementSupport.raisedSearch_spec head greater right hg hs
  have har : rightWord ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) right := by
    rw [← hword]
    exact NativeContext.SourceAdditiveTracking.Assignment.execute_multiplicative _ right hi
  have hlex := NativeContext.SourceAdditiveTracking.AssignmentCoverPrefix.execute_right_multiplicative_lex
    _ input right word rightWord hi (by rw [hs'.2.2]; exact hlt) ho har
  have hny : ys ≠ [] := by
    intro hn
    have hn' := hlen
    rw [hn, List.length_nil] at hn'
    exact ((NativeContext.SourceTrackingSequences.trackingCheck_exact _ rightWord).mp ht).1
      (List.length_eq_zero_iff.mp hn'.symm)
  exact first_le_of_lex _ word ys
    (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty _ input word ho)
    hny (by simpa only [← hv] using hlex)

/-- Genuine current suffix provenance, a descending factor and actual
whole execution derive the next complete initialized suffix and LF column.
The selected greater FIRST supplies its cover by derived M-right order. -/
theorem initialized_update (original : List Nat) (head greater input factor : Nat)
    (before heads suffix ys out : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (hg : lowCheckCode 0 greater = true)
    (hmg : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 greater))
    (hhead : interpretation 0 head < interpretation 0 greater)
    (hgreater : interpretation 0 greater ≤ interpretation 0 (lastCode original))
    (hy : ys ∈ Replacement.raisedReplacement head greater)
    (hcover : Insertion.coverCheck (lastCode before) (Insertion.firstCode ys) = true)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input <
      interpretation 0 greater)
    (hrel : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) heads suffix)
    (hne : before ≠ [])
    (hfull : SourceTrackingRaw.trackingCheck (before ++ suffix) = true)
    (hbefore : interpretation 0 (lastCode before) ≤ interpretation 0 head)
    (hf : Theta.acceptedLowCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hone : 1 < interpretation 0 factor)
    (hsmall : interpretation 0 factor < interpretation 0 greater)
    (hcut : interpretation 0 factor ≤ lf (NativeContext.interpretation
      (ReplacementSupport.raisedBaseCode head) input))
    (hu : out ∈ Branches.execute (factor, before ++ suffix)) :
    ∃ next nextHeads nextSuffix,
      out = before ++ nextSuffix ∧
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next =
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input * interpretation 0 factor ∧
      NativeContext.base (ReplacementSupport.raisedBaseCode head) <
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next ∧
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next < interpretation 0 greater ∧
      nextHeads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
        (ReplacementSupport.raisedBaseCode head) next ∧
      lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next) = interpretation 0 factor ∧
      List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) nextHeads nextSuffix := by
  have hraw := ((SourceTrackingRaw.trackingCheck_exact original).mp hw).2.1.nodes head hh
  have hfLow := ((Theta.acceptedLowCode_iff 0 factor).mp hf).1
  obtain ⟨otherFactor, hsearch⟩ := ReplacementSupport.raisedSearch_returns head factor hraw hfLow
  have hs := ReplacementSupport.raisedSearch_spec head factor otherFactor hfLow hsearch
  have hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) otherFactor factor :=
    ⟨hf, hs.2.2.symm⟩
  have hm' : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor) := by
    rw [hs.2.2]; exact hm
  have hone' : 1 < NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor := by
    rw [hs.2.2]; exact hone
  have hcut' : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor ≤
      lf (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input) := by
    rw [hs.2.2]; exact hcut
  have hlast := hcut'.trans
    (NativeContext.SourceAdditiveTracking.Assignment.execute_last_bounds _ input heads ho).1
  obtain ⟨updateWord, hupdate⟩ := NativeContext.SourceAdditiveTracking.Branches.execute_returns
    _ otherFactor heads (NativeContext.SourceAdditiveTracking.Assignment.execute_tracking _ input heads ho)
    hs.1 hm' hlast
  obtain ⟨next, nextHeads, hproduct, hnextLow, hnextAccepted, hvalue, hnextStrict,
    hnext, hvalues, hlastFactor⟩ :=
    NativeContext.SourceAdditiveTracking.FactorUpdateExecution.product_update_returns
      _ input otherFactor heads updateWord ho hs.1 hm' hone' hstrict hcut' hupdate
  have hnextSmall : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) next <
      interpretation 0 greater := by
    rw [hvalue, hs.2.2]
    exact hmg.2.2 hinput hsmall
  have hfirst := assignment_first_le_raised head greater next nextHeads ys hraw hg hmg hhead
    hnext hnextSmall hy
  have hfirstUpdate := NativeContext.SourceAdditiveTracking.AssignmentValueSupport.firstCode_values_eq
    (ReplacementSupport.raisedBaseCode head) updateWord nextHeads hvalues
  have hnextCover : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)
      (NativeContext.SourceAdditiveTracking.Insertion.firstCode updateWord) ≤
        SourceTrackingRaw.Support.muValue (lastCode before) := by
    rw [hfirstUpdate]
    exact hfirst.trans ((Insertion.coverCheck_exact _ _).mp hcover).2.2
  obtain ⟨nextSuffix, hout, hbranch, hnextRel⟩ := ContextRelatedFirstCut.contextual_update_first_cut
    original head input factor otherFactor before heads suffix updateWord out hw hh ho hstrict
    (hinput.le.trans hgreater) hrel hne hfull hbefore hs.1 hd hm' hone' hlast hnextCover hupdate hu
  have hrel' : List.Forall₂ (Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head)) nextHeads nextSuffix :=
    relation_of_values _ nextHeads nextSuffix
      ((ContextRelatedFirstCut.relation_values hnextRel).trans hvalues)
      (ContextRelatedFirstCut.relation_checked hnextRel)
  exact ⟨next, nextHeads, nextSuffix, hout, by simpa only [hs.2.2] using hvalue,
    hnextStrict, hnextSmall, hnext, by simpa only [hs.2.2] using hlastFactor, hrel'⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextInitializedUpdate
