import Alexander313.Wilken.SourceOneNativeAdditiveTrackingMultiplicativePublicPrefix
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.MultiplicativeNormalForm

/-!
# Genuine penultimate source-one M caller and shorter component

An actual M execution retains its literal public input as FINAL. Original
proper-prefix strictness and canonical return derive whole strictness.
The actual nonempty proper prefix then supplies a genuine proper public
mu caller at its penultimate node, whole-input cover, computed LF equal
to that node, and an independently executing strictly shorter component.
No general P input-to-FINAL identity or penultimate caller is assumed.
Source-only uncompiled candidates in the original source-zero dictionary.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativePenultimate

open GlobalAdditiveTracking
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton lastCode_mem)
open GlobalAdditiveTracking.RelativeCertificate (lastCode_map)

/-- Literal canonical FINAL is the independently executing public M input. -/
theorem execute_public_last (beta : Nat) (out : List Nat)
    (ho : out ∈ SourceOneRelativeAssignment.execute beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta)) :
    lastCode out = beta := by
  obtain ⟨hi, hcases⟩ := (SourceOneRelativeAssignment.execute_clauses beta out).mp ho
  rcases hcases with ⟨hb, he⟩ | ⟨hb, he⟩
  · simpa only [he] using NativeContext.SourceTrackingSequences.lastCode_singleton beta
  · obtain ⟨hchecked, hv, word, hw, hout, hvalues⟩ :=
      SourceOneRelativeAssignment.execute_ordinary_source beta out ho hb
    have hc := (Assignment.inputCheck_exact _).mp (Assignment.execute_spec _ word hw).1
    have hmraw := (SourceMultiplicativePrincipal.inputCheck_exact _).mpr
      ⟨hc.1, hc.2.1, by rw [hv]; exact hm⟩
    have hl := (MultiplicativePrefix.execute_multiplicative_prefix _ word hmraw hw).1
    have hp := SourceTrackingRaw.Support.publicCode_spec _ hc.1
    have hfinal := Canonical.check_value_injective _ _ hp.1
      ((SourceOneRelativeAssignment.inputCheck_exact beta).mp hi).1 (hp.2.trans hv)
    rw [hout, Return.sourceOneWord, lastCode_map _ word (Assignment.execute_nonempty _ word hw), hl, hfinal]

/-- Whole strictness is derived from the true original M path, including
the actual final entry, rather than from a general tracking assumption. -/
theorem execute_public_strict (beta : Nat) (out : List Nat)
    (ho : out ∈ SourceOneRelativeAssignment.execute beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta)) :
    (out.map unionInterpretation).Pairwise (· < ·) := by
  obtain ⟨hi, hcases⟩ := (SourceOneRelativeAssignment.execute_clauses beta out).mp ho
  rcases hcases with ⟨hb, he⟩ | ⟨hb, he⟩
  · simp only [he, List.map_singleton, List.pairwise_singleton]
  · obtain ⟨hchecked, hv, word, hw, hout, hvalues⟩ :=
      SourceOneRelativeAssignment.execute_ordinary_source beta out ho hb
    have hc := (Assignment.inputCheck_exact _).mp (Assignment.execute_spec _ word hw).1
    have hmraw := (SourceMultiplicativePrincipal.inputCheck_exact _).mpr
      ⟨hc.1, hc.2.1, by rw [hv]; exact hm⟩
    have hl := (MultiplicativePrefix.execute_multiplicative_prefix _ word hmraw hw).1
    have ht := (SourceTrackingRaw.trackingCheck_exact word).mp (Assignment.execute_tracking _ word hw)
    obtain ⟨last, he, hh⟩ := stripLast_split word ht.1
    have hlast : last = GlobalAdditiveTracking.Source.sourceOneCode beta := by
      calc
        last = lastCode word := by rw [he, lastCode_append_singleton]
        _ = _ := hl
    rw [hvalues, he, List.map_append, List.map_singleton]
    apply List.pairwise_append.mpr
    refine ⟨ht.2.1.strict, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hy, hlast]
    exact (ProperPrefix.execute_prefix_interval _ word hw d hd).2.2.2

/-- The actual nonempty proper M prefix constructs its penultimate caller,
whole-input mu cover, LF identity and genuinely shorter independent prefix. -/
theorem execute_penultimate (beta : Nat) (out : List Nat)
    (ho : out ∈ SourceOneRelativeAssignment.execute beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hp : stripLast out ≠ []) :
    ∃ before d, out = before ++ d :: [beta] ∧
      MuPublicDictionary.Support.inputCheck d = true ∧
      unionInterpretation d < unionInterpretation beta ∧
      unionInterpretation beta ≤ SkPublicRecurrence.muValue d ∧
      Alexander313.Wilken.MultiplicativeNormalForm.lf (unionInterpretation d) = unionInterpretation d ∧
      before ++ [d] ∈ SourceOneRelativeAssignment.execute d ∧ (before ++ [d]).length < out.length := by
  have ht := SourceOneRelativeAssignment.execute_tracking beta out ho
  have hl := execute_public_last beta out ho hm
  obtain ⟨last, hout, hh⟩ := stripLast_split out ht.1
  have hlast : last = beta := by
    calc
      last = lastCode out := by rw [hout, lastCode_append_singleton]
      _ = beta := hl
  have hout' : out = stripLast out ++ [beta] := by simpa only [hlast] using hout
  obtain ⟨d, hprefix, hdlast⟩ := stripLast_split (stripLast out) hp
  let before := stripLast (stripLast out)
  have hd : d ∈ stripLast out := by
    rw [hprefix]
    exact List.mem_append_right _ List.mem_cons_self
  have hnode := ht.2.2.1.nodes d hd
  have hcut : out = before ++ d :: [beta] := by
    rw [hout', hprefix]
    simp only [before, List.append_assoc, List.singleton_append]
  have hmu := ht.2.2.2.2.2
  rw [if_neg hp, hl] at hmu
  have hprev : lastCode (stripLast out) = d := by rw [hprefix, lastCode_append_singleton]
  have hcover : unionInterpretation beta ≤ SkPublicRecurrence.muValue d := by
    simpa only [hprev] using hmu.2
  have hs := execute_public_strict beta out ho hm
  rw [hout', List.map_append, List.map_singleton] at hs
  have hlt := (List.pairwise_append.mp hs).2.2 _
    (List.mem_map.mpr ⟨d, hd, rfl⟩) _ List.mem_cons_self
  have heps := (MuPublicDictionary.Support.inputCheck_image d).mp hnode
  have hM := NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _ heps.2.1
  have hshort := MultiplicativePublicPrefix.execute_public_proper_prefix beta out before [beta] d
    ho hm hcut (List.cons_ne_nil _ _)
  exact ⟨before, d, hcut, hnode, hlt, hcover,
    Alexander313.Wilken.MultiplicativeNormalForm.lf_multiplicative hM, hshort.1, hshort.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativePenultimate
