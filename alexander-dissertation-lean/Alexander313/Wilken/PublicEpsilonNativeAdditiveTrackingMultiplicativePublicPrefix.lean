import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingMultiplicativePrefix
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance
import Alexander313.Wilken.HereditaryMuCoveredRelativeAssignment
import Alexander313.Wilken.PublicEpsilonNativeSkPublicValueInvariance

/-!
# Literal public executions at every actual native M prefix

The actual M table derives independently executing complete assignments at
all written prefix endpoints. Genuine uniform LOW returns and full value
invariance identify their canonical public words literally. The actual
mu-covered public procedure therefore independently executes every observed
prefix of an M output; a proper prefix is strictly shorter. Its boundary
singleton is handled through the real executing clause. Neither a source
spelling equation, prefix execution nor length bound is supplied. Source-only
uncompiled candidates in genuine native epsilon contexts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.MultiplicativePublicPrefix

open GlobalAdditiveTracking
open MuCoveredRelativeAssignment (publicWord publicWord_spec)
open PublicEpsilonUnboundedIota

private theorem returned_values_eq (q : Nat) (xs ys : List Nat)
    (hx : ∀ c ∈ xs, lowCheckCode q c = true)
    (hy : ∀ c ∈ ys, lowCheckCode q c = true)
    (hv : xs.map (interpretation q) = ys.map (interpretation q)) :
    publicWord q xs = publicWord q ys := by
  have hs : ∀ word : List Nat, (∀ c ∈ word, lowCheckCode q c = true) →
      (∀ c ∈ publicWord q word, Canonical.check c = true) ∧
        (publicWord q word).map unionInterpretation = word.map (interpretation q) := by
    intro word hw
    have hp := fun d hd => UniformPublicReturn.publicCode_spec q d
      ((UniformPublicReturn.inputCheck_exact q d).mpr (hw d hd))
    constructor
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact (hp d hd).1
    · rw [publicWord, List.map_map]
      exact List.map_congr_left (fun d hd => (hp d hd).2)
  exact SkPublicValueInvariance.canonical_words_eq _ _ (hs xs hx).1 (hs ys hy).1
    ((hs xs hx).2.trans (hv.trans (hs ys hy).2.symm))

/-- Every actual M assignment covered at the actual public base executes
its canonical word through the real relative procedure. -/
theorem execute_returned_word (q raw : Nat) (word : List Nat)
    (hq : GlobalMuDictionary.Support.inputCheck q = true)
    (hm : SourceMultiplicativePrincipal.inputCheck q raw = true)
    (ho : word ∈ Assignment.execute q raw)
    (hcover : interpretation q raw ≤ GlobalTrackingSequences.muValue q) :
    publicWord q word ∈ MuCoveredRelativeAssignment.execute q (UniformPublicReturn.publicCode q raw) := by
  have hc := (SourceMultiplicativePrincipal.inputCheck_exact q raw).mp hm
  have hp := UniformPublicReturn.publicCode_spec q raw
    ((UniformPublicReturn.inputCheck_exact q raw).mpr hc.1)
  have hb : unionInterpretation (UniformPublicReturn.publicCode q raw) <
      globalBoundary (unionInterpretation q) 0 := by
    rw [hp.2]
    exact checked_low_bound q raw hc.1
  have hi := (MuCoveredRelativeAssignment.Support.inputCheck_exact q _).mpr
    ⟨hq, hp.1, by rw [hp.2]; exact hc.2.2.1,
      by rw [hp.2]; exact hc.2.2.2.1,
      by simpa only [hp.2, base] using hc.2.1, by rw [hp.2]; exact hcover⟩
  have hordinary : MuCoveredRelativeAssignment.Support.boundaryCheck q
      (UniformPublicReturn.publicCode q raw) = false := by
    cases he : MuCoveredRelativeAssignment.Support.boundaryCheck q
        (UniformPublicReturn.publicCode q raw) with
    | false => rfl
    | true =>
      have hv := (MuCoveredRelativeAssignment.Support.boundaryCheck_exact q _ hi).mp he
      exact False.elim (hb.ne hv.2)
  obtain ⟨out, hout⟩ := MuCoveredRelativeAssignment.execute_returns q _ hi
  obtain ⟨otherRaw, other, hlow, hnormal, hv, hother, htrack, he, hvalues⟩ :=
    MuCoveredRelativeAssignment.execute_ordinary_source q _ out hout hordinary
  have hwordValues := Assignment.ValueInvariance.execute_values_eq q raw otherRaw word other
    ho hother (hp.2.symm.trans hv.symm)
  have hsame : publicWord q word = out := by
    rw [he]
    exact returned_values_eq q word other
      (Return.native_word_low q word (Assignment.execute_tracking q raw word ho))
      (Return.native_word_low q other htrack) hwordValues
  exact hsame.symm ▸ hout

/-- Actual raw M execution derives the real public execution at any
observed written prefix endpoint, with its whole mu caller derived. -/
theorem execute_original_prefix (q raw : Nat) (word before after : List Nat) (d : Nat)
    (hq : GlobalMuDictionary.Support.inputCheck q = true)
    (hm : SourceMultiplicativePrincipal.inputCheck q raw = true)
    (ho : word ∈ Assignment.execute q raw)
    (hcover : interpretation q raw ≤ GlobalTrackingSequences.muValue q)
    (he : word = before ++ d :: after) :
    publicWord q (before ++ [d]) ∈ MuCoveredRelativeAssignment.execute q
      (UniformPublicReturn.publicCode q d) := by
  obtain ⟨hd, prefixOut, hp, hv⟩ :=
    (MultiplicativePrefix.execute_multiplicative_prefix q raw word hm ho).2 before d after he
  have hl := Return.native_word_low q word (Assignment.execute_tracking q raw word ho)
  have hprefixLow : ∀ c ∈ before ++ [d], lowCheckCode q c = true := by
    intro c hc
    apply hl c
    rw [he]
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · rw [List.mem_singleton.mp hc]
      exact List.mem_append_right _ List.mem_cons_self
  have hdMem : d ∈ word := by rw [he]; exact List.mem_append_right _ List.mem_cons_self
  have hdCover := ((Assignment.execute_spec q raw word ho).2.1.2.1 d hdMem).trans hcover
  have hsame := returned_values_eq q prefixOut (before ++ [d])
    (Return.native_word_low q prefixOut (Assignment.execute_tracking q d prefixOut hp)) hprefixLow hv
  exact hsame ▸ execute_returned_word q d prefixOut hq hd hp hdCover

/-- Every observed cut of an actual mu-covered public M word independently
executes the same public procedure at its literal canonical endpoint. -/
theorem execute_public_prefix (gamma beta : Nat) (out before after : List Nat) (d : Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (he : out = before ++ d :: after) :
    before ++ [d] ∈ MuCoveredRelativeAssignment.execute gamma d := by
  obtain ⟨hi, hcases⟩ := (MuCoveredRelativeAssignment.execute_clauses gamma beta out).mp ho
  rcases hcases with ⟨hb, hout⟩ | ⟨hb, raw, word, hr, hw, hout⟩
  · have hshape : [] ++ [beta] = before ++ d :: after := by simpa only [hout] using he
    rcases MultiplicativePrefix.append_singleton_position [] before after beta d hshape with
      ⟨hbefore, hd, hafter⟩ | ⟨tail, htail⟩
    · simpa only [hbefore, hd, List.nil_append, hout] using ho
    · simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at htail
  · have hinput := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp hi
    have hsource := SkNextSearch.Support.search_spec gamma beta raw hr
    have hc := (Assignment.inputCheck_exact gamma raw).mp (Assignment.execute_spec gamma raw word hw).1
    have hrawM : SourceMultiplicativePrincipal.inputCheck gamma raw = true :=
      (SourceMultiplicativePrincipal.inputCheck_exact gamma raw).mpr
        ⟨hc.1, hc.2.1, by rw [hsource.2.2.2]; exact hm⟩
    have hcover : interpretation gamma raw ≤ GlobalTrackingSequences.muValue gamma := by
      rw [hsource.2.2.2]; exact hinput.2.2.2.2.2
    have hmap : word.map (UniformPublicReturn.publicCode gamma) = before ++ d :: after := by
      simpa only [hout, publicWord] using he
    obtain ⟨rawBefore, rawRest, hsplit, hbefore, hrest⟩ := List.map_eq_append_iff.mp hmap
    obtain ⟨rawD, rawAfter, htail, hd, hafter⟩ := List.map_eq_cons_iff.mp hrest
    have hrawShape : word = rawBefore ++ rawD :: rawAfter := hsplit.trans (by rw [htail])
    have hp := execute_original_prefix gamma raw word rawBefore rawAfter rawD hinput.1 hrawM hw hcover hrawShape
    simpa only [publicWord, List.map_append, List.map_singleton, hbefore, hd] using hp

/-- A genuine proper node prefix strictly shortens the actual public M component. -/
theorem execute_public_proper_prefix (gamma beta : Nat) (out before after : List Nat) (d : Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (he : out = before ++ d :: after) (hne : after ≠ []) :
    before ++ [d] ∈ MuCoveredRelativeAssignment.execute gamma d ∧ (before ++ [d]).length < out.length := by
  refine ⟨execute_public_prefix gamma beta out before after d ho hm he, ?_⟩
  have hpos := List.length_pos_iff.mpr hne
  simp only [he, List.length_append, List.length_cons, List.length_singleton]
  omega

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.MultiplicativePublicPrefix
