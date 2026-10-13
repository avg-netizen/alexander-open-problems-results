import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingMultiplicativePublicPrefix
import Alexander313.Wilken.HereditaryMuCoveredRelativePublicFidelity
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.MultiplicativeNormalForm

/-!
# Actual public M FINAL and independent penultimate execution

The genuine M leaf preserves its original final code. Canonical LOW return
therefore gives literal public FINAL beta, including the actual boundary
singleton. If the proper output prefix is nonempty, its computed penultimate
code is a genuine public-mu caller, the whole beta is covered there, and the
complete stripLast output independently executes the SAME relative public
procedure at that penultimate code with strictly shorter length. All these
callers and executions are derived from actual memberships; no prefix or
mu-cover witness is supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.MultiplicativePublicPenultimate

open PublicEpsilonUnboundedIota
open SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open GlobalAdditiveTracking.RelativeCertificate (lastCode_map)

/-- Every actually executing covered public M word ends literally in its
original canonical input, without identifying the last of a nonM word. -/
theorem execute_public_last (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta)) :
    lastCode out = beta := by
  obtain ⟨hi, hcases⟩ := (MuCoveredRelativeAssignment.execute_clauses gamma beta out).mp ho
  rcases hcases with ⟨hb, hout⟩ | ⟨hb, raw, word, hr, hw, hout⟩
  · simpa only [hout, lastCode_singleton]
  · have hs := SkNextSearch.Support.search_spec gamma beta raw hr
    have hc := (Assignment.inputCheck_exact gamma raw).mp (Assignment.execute_spec gamma raw word hw).1
    have hrawM : SourceMultiplicativePrincipal.inputCheck gamma raw = true :=
      (SourceMultiplicativePrincipal.inputCheck_exact gamma raw).mpr
        ⟨hc.1, hc.2.1, by rw [hs.2.2.2]; exact hm⟩
    have hlast := (MultiplicativePrefix.execute_multiplicative_prefix gamma raw word hrawM hw).1
    have hp := UniformPublicReturn.publicCode_spec gamma raw
      ((UniformPublicReturn.inputCheck_exact gamma raw).mpr hs.1)
    have hcode : UniformPublicReturn.publicCode gamma raw = beta :=
      Canonical.check_value_injective _ _ hp.1 hs.2.2.1 (hp.2.trans hs.2.2.2)
    rw [hout, MuCoveredRelativeAssignment.publicWord,
      lastCode_map _ word (Assignment.execute_nonempty gamma raw word hw), hlast, hcode]

/-- Whole strictness follows from the actual unchanged M final and true
proper-prefix interval, including its last entry. -/
theorem execute_public_strict (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta)) :
    (out.map unionInterpretation).Pairwise (· < ·) := by
  obtain ⟨hi, hcases⟩ := (MuCoveredRelativeAssignment.execute_clauses gamma beta out).mp ho
  rcases hcases with ⟨hb, hout⟩ | ⟨hb, raw, word, hr, hw, hout⟩
  · simp only [hout, List.map_singleton, List.pairwise_singleton]
  · have hs := SkNextSearch.Support.search_spec gamma beta raw hr
    have hc := (Assignment.inputCheck_exact gamma raw).mp (Assignment.execute_spec gamma raw word hw).1
    have hrawM := (SourceMultiplicativePrincipal.inputCheck_exact gamma raw).mpr
      ⟨hc.1, hc.2.1, by rw [hs.2.2.2]; exact hm⟩
    have hl := (MultiplicativePrefix.execute_multiplicative_prefix gamma raw word hrawM hw).1
    have ht := (SourceTrackingRaw.trackingCheck_conditions gamma word).mp
      (Assignment.execute_tracking gamma raw word hw)
    obtain ⟨last, he, hh⟩ := stripLast_split word ht.1
    have hlast : last = raw := by
      calc
        last = lastCode word := by rw [he, lastCode_append_singleton]
        _ = raw := hl
    have hvalues := (MuCoveredRelativeAssignment.publicWord_spec gamma raw word hw).2.2
    rw [hout, hvalues, he, List.map_append, List.map_singleton]
    apply List.pairwise_append.mpr
    refine ⟨ht.2.1.strict, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hy, hlast]
    exact (ProperPrefix.execute_prefix_interval gamma raw word hw d hd).2.2.2

/-- A real nonempty proper prefix supplies the actual independent public
penultimate execution, strict component shortening and genuine whole-input
mu cover at the independently admitted penultimate node. -/
theorem execute_public_penultimate (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hne : stripLast out ≠ []) :
    stripLast out ∈ MuCoveredRelativeAssignment.execute gamma (lastCode (stripLast out)) ∧
      (stripLast out).length < out.length ∧
        MuPublicDictionary.Support.inputCheck (lastCode (stripLast out)) = true ∧
          unionInterpretation (lastCode (stripLast out)) < unionInterpretation beta ∧
            unionInterpretation beta ≤ SkPublicRecurrence.muValue (lastCode (stripLast out)) ∧
              Alexander313.Wilken.MultiplicativeNormalForm.lf (unionInterpretation (lastCode (stripLast out))) =
                unionInterpretation (lastCode (stripLast out)) ∧ lastCode out = beta := by
  have ht := CoveredPublicMu.execute_tracking gamma beta out ho
  have hlast := execute_public_last gamma beta out ho hm
  obtain ⟨last, hout, hmem⟩ := stripLast_split out ht.1
  obtain ⟨d, hprefix, hdmem⟩ := stripLast_split (stripLast out) hne
  have hd : lastCode (stripLast out) = d := by rw [hprefix, lastCode_append_singleton]
  have hshape : out = stripLast (stripLast out) ++ d :: [last] := by
    simpa only [List.append_assoc, List.singleton_append] using
      hout.trans (congrArg (fun xs : List Nat => xs ++ [last]) hprefix)
  have hp := MultiplicativePublicPrefix.execute_public_proper_prefix gamma beta out
    (stripLast (stripLast out)) [last] d ho hm hshape (List.cons_ne_nil _ _)
  have hnode := ht.2.2.1.nodes _ (lastCode_mem _ hne)
  have hcover : unionInterpretation beta ≤ SkPublicRecurrence.muValue (lastCode (stripLast out)) := by
    have hc : 1 < unionInterpretation (lastCode out) ∧
        unionInterpretation (lastCode out) ≤ SkPublicRecurrence.muValue (lastCode (stripLast out)) := by
      simpa only [if_neg hne] using ht.2.2.2.2.2
    simpa only [hlast] using hc.2
  have hlastWitness : last = beta := by
    calc
      last = lastCode out := by rw [hout, lastCode_append_singleton]
      _ = beta := hlast
  have houtBeta : out = stripLast out ++ [beta] := by simpa only [hlastWitness] using hout
  have hs := execute_public_strict gamma beta out ho hm
  rw [houtBeta, List.map_append, List.map_singleton] at hs
  have hlt := (List.pairwise_append.mp hs).2.2 _
    (List.mem_map.mpr ⟨lastCode (stripLast out), lastCode_mem _ hne, rfl⟩) _ List.mem_cons_self
  have heps := (MuPublicDictionary.Support.inputCheck_image _).mp hnode
  have hM := SourceMultiplicativePrincipal.epsilon_multiplicative _ heps.2.1
  refine ⟨?_, ?_, hnode, hlt, hcover,
    Alexander313.Wilken.MultiplicativeNormalForm.lf_multiplicative hM, hlast⟩
  · rw [hd, hprefix]; exact hp.1
  · rw [hprefix]; exact hp.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.MultiplicativePublicPenultimate
