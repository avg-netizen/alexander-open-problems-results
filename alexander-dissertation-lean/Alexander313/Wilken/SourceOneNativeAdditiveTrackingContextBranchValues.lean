import Alexander313.Wilken.SourceOneNativeAdditiveTrackingContextSelectionValues

/-!
# Actual original-zero append-or-insert value covariance

The real complete lower assignment derives strict FIRST when needed and
its original finite return supplies the exact admitted head relation. The
actual OWN contextual mu gives append identity and all proper insertion
cover flags. Both independently executing source dispatchers consequently
have the same chronological VALUES. The original tracker FINAL derives all
OWN and finite callers. No full assignment composition or cut invariant
is supplied or concluded. Source-only uncompiled; check-zero remains literal.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextBranchValues

open NativeContext.SourceTrackingSequences (lastCode)
open Hereditary.FinePredecessor (stripLast)

theorem branches_values_eq (root input factor otherFactor : Nat)
    (heads otherHeads word otherWord : List Nat) (ha : Mu.inputCheck root = true)
    (ho : otherHeads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute (alphaCode root) input)
    (hstrict : NativeContext.base (alphaCode root) < NativeContext.interpretation (alphaCode root) input)
    (hown : NativeContext.interpretation (alphaCode root) input < Enclosure.sourceAlphaPlus root)
    (hrel : List.Forall₂ (Replacement.EntryMatches (alphaCode root)) otherHeads heads)
    (hf : NativeContext.lowCheckCode (alphaCode root) otherFactor = true)
    (hd : Replacement.EntryMatches (alphaCode root) otherFactor factor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (alphaCode root) otherFactor))
    (hb : NativeContext.interpretation (alphaCode root) otherFactor ≤
      NativeContext.interpretation (alphaCode root) (lastCode otherHeads))
    (hs : word ∈ Branches.execute (factor, heads))
    (ht : otherWord ∈ NativeContext.SourceAdditiveTracking.Branches.execute
      (((alphaCode root), otherFactor), otherHeads)) :
    word.map (interpretation 0) = otherWord.map (NativeContext.interpretation (alphaCode root)) := by
  have hc := ContextAppendCheck.assignment_appendCheck_eq root input otherFactor factor
    otherHeads heads ha ho hstrict hown hrel hf hd
  cases he : NativeContext.SourceAdditiveTracking.BranchesSupport.appendCheck
      (alphaCode root) otherFactor otherHeads with
  | true =>
    have hsflag : BranchesSupport.appendCheck factor heads = true := hc.trans he
    have hword : word = heads ++ [factor] := by
      simpa only [Branches.execute, hsflag, Bool.cond_true, Part.mem_some_iff] using hs
    have hotherWord : otherWord = otherHeads ++ [otherFactor] := by
      simpa only [NativeContext.SourceAdditiveTracking.Branches.execute, he,
        Bool.cond_true, Part.mem_some_iff] using ht
    have hv : heads.map (interpretation 0) = otherHeads.map (NativeContext.interpretation (alphaCode root)) := by
      induction hrel with
      | nil => rfl
      | cons hd ht ih => simp only [List.map_cons, hd.2, ih]
    simp only [hword, hotherWord, List.map_append, List.map_singleton, hv, hd.2]
  | false =>
    have hsflag : BranchesSupport.appendCheck factor heads = false := hc.trans he
    have hs' : word ∈ Insertion.execute (factor, heads) := by
      simpa only [Branches.execute, hsflag, Bool.cond_false] using hs
    have ht' : otherWord ∈ NativeContext.SourceAdditiveTracking.Insertion.execute
        (((alphaCode root), otherFactor), otherHeads) := by
      simpa only [NativeContext.SourceAdditiveTracking.Branches.execute, he, Bool.cond_false] using ht
    exact ContextSelectionValues.insertion_values_eq root input factor otherFactor
      heads otherHeads word otherWord ha ho hown hrel hf hd hm hb hs' ht'

/-- Every OWN interval and head relation follows from the original checked
tracker and the actual lower execution bounded by its written FINAL. -/
theorem returned_branches_values_eq (original : List Nat) (head input factor otherFactor : Nat)
    (heads word otherWord : List Nat)
    (hw : SourceTrackingRaw.trackingCheck original = true) (hh : head ∈ stripLast original)
    (ho : heads ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (ReplacementSupport.raisedBaseCode head) input)
    (hstrict : NativeContext.base (ReplacementSupport.raisedBaseCode head) <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input)
    (hinput : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) input ≤
      interpretation 0 (lastCode original))
    (hf : NativeContext.lowCheckCode (ReplacementSupport.raisedBaseCode head) otherFactor = true)
    (hd : Replacement.EntryMatches (ReplacementSupport.raisedBaseCode head) otherFactor factor)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor))
    (hb : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) otherFactor ≤
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) (lastCode heads))
    (hs : word ∈ Branches.execute (factor, Replacement.returnWord head heads))
    (ht : otherWord ∈ NativeContext.SourceAdditiveTracking.Branches.execute
      (((ReplacementSupport.raisedBaseCode head), otherFactor), heads)) :
    word.map (interpretation 0) =
      otherWord.map (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
  have ht' := (SourceTrackingRaw.trackingCheck_exact original).mp hw
  have hhead := ht'.2.1.nodes head hh
  have hroot := (SourceTrackingRaw.Support.rootCode_spec head hhead).2.1
  have he := ReplacementFidelity.raisedBase_eq_alphaCode head hhead
  have hne : stripLast original ≠ [] := by
    intro hn
    rw [hn] at hh
    exact List.not_mem_nil hh
  have hend := EndpointSupport.tracking_final_lt_endpoints original hw hne head hh
  have hown := hinput.trans_lt hend
  have hreturn := ContextAssignmentReturn.assignment_return original head input heads hw hh ho hinput
  simpa only [he] using branches_values_eq (SourceTrackingRaw.Support.rootCode head)
    input factor otherFactor (Replacement.returnWord head heads) heads word otherWord hroot
    (by simpa only [he] using ho) (by simpa only [he] using hstrict)
    (by simpa only [he] using hown) (by simpa only [he] using hreturn.2.1)
    (by simpa only [he] using hf) (by simpa only [he] using hd)
    (by simpa only [he] using hm) (by simpa only [he] using hb) hs
    (by simpa only [he] using ht)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ContextBranchValues
