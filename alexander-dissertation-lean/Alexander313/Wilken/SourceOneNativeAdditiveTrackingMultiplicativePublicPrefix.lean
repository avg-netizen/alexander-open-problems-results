import Alexander313.Wilken.SourceOneNativeAdditiveTrackingMultiplicativePrefix
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentValueInvariance
import Alexander313.Wilken.HereditarySourceOneRelativeAssignment
import Alexander313.Wilken.PublicEpsilonNativeSkPublicValueInvariance

/-!
# Literal canonical public executions at every actual source-one M prefix

The actual original M table supplies independent executions at all written
prefix endpoints. Genuine source-zero LOW returns and complete value-word
invariance identify their independently computed canonical public outputs.
Every observed public prefix ending at a node therefore executes the real
source-one relative assignment, and a proper prefix is strictly shorter.
The initial grammar boundary singleton is handled by its actual clause.
No Native base-one parser, written source identity or prefix-execution oracle
is supplied. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativePublicPrefix

open GlobalAdditiveTracking
open SourceTrackingRaw.Support (publicCode publicCode_spec original_bound)
open NativeContext.PublicEpsilonUnboundedIota

private theorem returned_values_eq (xs ys : List Nat)
    (hx : ∀ c ∈ xs, lowCheckCode 0 c = true)
    (hy : ∀ c ∈ ys, lowCheckCode 0 c = true)
    (hv : xs.map (interpretation 0) = ys.map (interpretation 0)) :
    Return.sourceOneWord xs = Return.sourceOneWord ys := by
  have hs : ∀ word : List Nat, (∀ c ∈ word, lowCheckCode 0 c = true) →
      (∀ c ∈ Return.sourceOneWord word, Canonical.check c = true) ∧
        (Return.sourceOneWord word).map unionInterpretation = word.map (interpretation 0) := by
    intro word hw
    constructor
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact (publicCode_spec d (hw d hd)).1
    · rw [Return.sourceOneWord, List.map_map]
      exact List.map_congr_left (fun d hd => (publicCode_spec d (hw d hd)).2)
  exact SkPublicValueInvariance.canonical_words_eq _ _ (hs xs hx).1 (hs ys hy).1
    ((hs xs hx).2.trans (hv.trans (hs ys hy).2.symm))

/-- The real public procedure executes the canonical return of any actual
original M assignment, even when its input returns in a different spelling. -/
theorem execute_returned_word (raw : Nat) (word : List Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck raw = true)
    (ho : word ∈ Assignment.execute raw) :
    Return.sourceOneWord word ∈ SourceOneRelativeAssignment.execute (publicCode raw) := by
  have hc := (SourceMultiplicativePrincipal.inputCheck_exact raw).mp hm
  have hp := publicCode_spec raw hc.1
  have hb : unionInterpretation (publicCode raw) < finiteBase 1 := by
    rw [hp.2]
    exact original_bound raw hc.1
  have hi : SourceOneRelativeAssignment.inputCheck (publicCode raw) = true :=
    (SourceOneRelativeAssignment.inputCheck_exact _).mpr ⟨hp.1,
      by rw [hp.2]; exact hc.2.2.1,
      by rw [hp.2]; exact hc.2.2.2.1, hb.le⟩
  have hordinary : SourceOneRelativeAssignment.boundaryCheck (publicCode raw) = false := by
    cases he : SourceOneRelativeAssignment.boundaryCheck (publicCode raw) with
    | false => rfl
    | true =>
      have hv := (SourceOneRelativeAssignment.boundaryCheck_exact _ hi).mp he
      exact False.elim (hb.ne hv)
  obtain ⟨out, hout⟩ := SourceOneRelativeAssignment.execute_returns _ hi
  obtain ⟨hchecked, hv, other, hother, he, hvalues⟩ :=
    SourceOneRelativeAssignment.execute_ordinary_source _ out hout hordinary
  have hwordValues := Assignment.ValueInvariance.execute_values_eq raw
    (GlobalAdditiveTracking.Source.sourceOneCode (publicCode raw)) word other ho hother
    (hp.2.symm.trans hv.symm)
  have hsame : Return.sourceOneWord word = out := by
    rw [he]
    exact returned_values_eq word other
      (Return.source_one_word_low word (Assignment.execute_tracking raw word ho))
      (Return.source_one_word_low other (Assignment.execute_tracking _ other hother)) hwordValues
  exact hsame.symm ▸ hout

/-- Every actual original M prefix has a literal canonical public execution,
not merely a value-equivalent supplied word. -/
theorem execute_original_prefix (raw : Nat) (word before after : List Nat) (d : Nat)
    (hm : SourceMultiplicativePrincipal.inputCheck raw = true)
    (ho : word ∈ Assignment.execute raw) (he : word = before ++ d :: after) :
    Return.sourceOneWord (before ++ [d]) ∈ SourceOneRelativeAssignment.execute (publicCode d) := by
  obtain ⟨hd, prefixOut, hp, hv⟩ :=
    (MultiplicativePrefix.execute_multiplicative_prefix raw word hm ho).2 before d after he
  have hl := Return.source_one_word_low word (Assignment.execute_tracking raw word ho)
  have hprefixLow : ∀ c ∈ before ++ [d], lowCheckCode 0 c = true := by
    intro c hc
    apply hl c
    rw [he]
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · rw [List.mem_singleton.mp hc]
      exact List.mem_append_right _ List.mem_cons_self
  have hsame := returned_values_eq prefixOut (before ++ [d])
    (Return.source_one_word_low prefixOut (Assignment.execute_tracking d prefixOut hp)) hprefixLow hv
  exact hsame ▸ execute_returned_word d prefixOut hd hp

/-- Any observed cut of the actually executing public M word is itself the
independent public assignment at its literal endpoint. All source witnesses
and intermediate M callers are conclusions of the original execution. -/
theorem execute_public_prefix (beta : Nat) (out before after : List Nat) (d : Nat)
    (ho : out ∈ SourceOneRelativeAssignment.execute beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (he : out = before ++ d :: after) :
    before ++ [d] ∈ SourceOneRelativeAssignment.execute d := by
  obtain ⟨hi, hcases⟩ := (SourceOneRelativeAssignment.execute_clauses beta out).mp ho
  rcases hcases with ⟨hb, hout⟩ | ⟨hb, hout⟩
  · have hshape : [] ++ [beta] = before ++ d :: after := by simpa only [hout] using he
    rcases MultiplicativePrefix.append_singleton_position [] before after beta d hshape with
      ⟨hbefore, hd, hafter⟩ | ⟨tail, htail⟩
    · simpa only [hbefore, hd, List.nil_append, hout] using ho
    · simp only [List.nil_eq_append_iff, List.cons_ne_nil, and_false] at htail
  · obtain ⟨hchecked, hv, word, hw, hword, hvalues⟩ :=
      SourceOneRelativeAssignment.execute_ordinary_source beta out ho hb
    have hc := (Assignment.inputCheck_exact _).mp (Assignment.execute_spec _ word hw).1
    have hrawM : SourceMultiplicativePrincipal.inputCheck
        (GlobalAdditiveTracking.Source.sourceOneCode beta) = true :=
      (SourceMultiplicativePrincipal.inputCheck_exact _).mpr
        ⟨hc.1, hc.2.1, by rw [hv]; exact hm⟩
    have hmap : word.map publicCode = before ++ d :: after := by
      simpa only [hword, Return.sourceOneWord] using he
    obtain ⟨rawBefore, rawRest, hsplit, hbefore, hrest⟩ := List.map_eq_append_iff.mp hmap
    obtain ⟨rawD, rawAfter, htail, hd, hafter⟩ := List.map_eq_cons_iff.mp hrest
    have hrawShape : word = rawBefore ++ rawD :: rawAfter := hsplit.trans (by rw [htail])
    have hp := execute_original_prefix _ word rawBefore rawAfter rawD hrawM hw hrawShape
    simpa only [Return.sourceOneWord, List.map_append, List.map_singleton, hbefore, hd] using hp

/-- A genuine proper node prefix strictly shortens the actual public component. -/
theorem execute_public_proper_prefix (beta : Nat) (out before after : List Nat) (d : Nat)
    (ho : out ∈ SourceOneRelativeAssignment.execute beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (he : out = before ++ d :: after) (hne : after ≠ []) :
    before ++ [d] ∈ SourceOneRelativeAssignment.execute d ∧ (before ++ [d]).length < out.length := by
  refine ⟨execute_public_prefix beta out before after d ho hm he, ?_⟩
  have hpos := List.length_pos_iff.mpr hne
  simp only [he, List.length_append, List.length_cons, List.length_singleton]
  omega

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.MultiplicativePublicPrefix
