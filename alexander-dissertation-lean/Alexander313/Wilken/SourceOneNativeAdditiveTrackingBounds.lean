import Alexander313.Wilken.SourceAdditiveTrackingWordBoundsSupport
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertion

/-!
# Actual replacement and insertion bounds for Proposition 3.21

Every genuine conditional replacement ends at or above the removed M
factor. Its whole emitted word is bounded by the original prefix value
times that factor. These facts pass through the actual greatest-cover
insertion, including the default branch and all retained original heads.
Only the honest recursive hypotheses are used: a checked headword, every
head value below the prefix input, and factor <= the headword final value.
The full assignment must derive those hypotheses by joint induction.
No final=input assumption, supplied replacement or output oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Bounds

open NativeContext.SourceTrackingSequences
open Hereditary.SourceAdditiveTrackingWordBounds

theorem conditional_bounds (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head factor : Nat)
    (hhead : head ∈ heads) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix) (hbound : interpretation 0 head ≤ prefix)
    (out : List Nat) (ho : out ∈ ConditionalReplacement.execute head factor) :
    out ≠ [] ∧ interpretation 0 factor ≤ interpretation 0 (lastCode out) ∧
      ∀ d ∈ out, interpretation 0 d ≤ prefix * interpretation 0 factor := by
  have hs := ConditionalReplacement.execute_spec heads hh head factor hhead hf hm hb out ho
  refine ⟨hs.1, ?_⟩
  rcases hs.2.2.2.2 with hraised | hsmall
  · have hr := (ConditionalReplacement.raised_member_caller heads hh head factor
      hhead hraised.1 hb).2
    obtain ⟨word, hw, he, ht, hv, hlen, hc⟩ :=
      Replacement.raisedReplacement_spec head factor out hr hf hm hraised.1 hraised.2
    have hsword := ReplacementSupport.raisedWord_spec head factor word hr hf hm hraised.1 hw
    have hlast : interpretation 0 (lastCode out) = interpretation 0 factor :=
      (lastCode_values_eq _ _ out word hs.1 hv).trans hsword.2.1
    refine ⟨hlast.ge, ?_⟩
    intro d hd
    exact (hc d hd).2.trans (Ordinal.le_mul_right _ hp)
  · obtain ⟨d, he, hv⟩ := hsmall.2
    subst out
    refine ⟨?_, ?_⟩
    · rw [lastCode_singleton, hv]
      exact Ordinal.le_mul_right _
        (ConditionalReplacement.tracking_member_principal heads hh head hhead).2.1
    · intro c hc
      rw [List.mem_singleton.mp hc, hv]
      exact mul_le_mul_left hbound _

/-- Actual execution supplies the table, its row memberships, the selected
replacement and the retained original prefix. The bounds therefore hold
for every real output rather than an independently specified splice. -/
theorem execute_bounds (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (prefix : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation 0 head ≤ prefix)
    (ho : out ∈ Insertion.execute (factor, heads)) :
    out ≠ [] ∧ interpretation 0 factor ≤ interpretation 0 (lastCode out) ∧
      ∀ d ∈ out, interpretation 0 d ≤ prefix * interpretation 0 factor := by
  obtain ⟨rows, hr, hout⟩ := (Part.mem_map_iff _).mp ho
  have hrel := InsertionSupport.executeRows_relation factor heads rows hr
  have hheads := InsertionSupport.relation_heads factor hrel
  have hrow : ∀ row ∈ rows, row.2 ≠ [] ∧
      interpretation 0 factor ≤ interpretation 0 (lastCode row.2) ∧
        ∀ d ∈ row.2, interpretation 0 d ≤ prefix * interpretation 0 factor := by
    intro row hmrow
    have hs := InsertionSupport.relation_members factor hrel row hmrow
    exact conditional_bounds heads hh row.1 factor hs.1 hf hm hb prefix hp
      (hbound row.1 hs.1) row.2 hs.2
  cases hchoose : Insertion.choose rows with
  | none =>
    cases rows with
    | nil =>
      have hne := ((SourceTrackingRaw.trackingCheck_exact heads).mp hh).1
      exact False.elim (hne (by simpa only [List.map_nil] using hheads.symm))
    | cons first rest =>
      have he := (Insertion.word_default first rest hchoose).1
      have hout : out = first.2 := hout.symm.trans he
      rw [hout]
      exact hrow first List.mem_cons_self
  | some selected =>
    obtain ⟨before, current, after, hne, hrows, hword, hcover, hnone⟩ :=
      Insertion.word_selected rows selected.1 selected.2 hchoose
    have hc : current ∈ rows := by
      rw [hrows]
      exact List.mem_append_right _ List.mem_cons_self
    have hs := hrow current hc
    have hout : out = before.map Prod.fst ++ current.2 := hout.symm.trans hword
    rw [hout]
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact hs.1 (List.append_eq_nil_iff.mp hz).2
    · rw [lastCode_append_nonempty _ _ hs.1]
      exact hs.2.1
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨row, hrowmem, he⟩ := List.mem_map.mp hd
        have hrmem : row ∈ rows := by
          rw [hrows]
          exact List.mem_append_left _ hrowmem
        have hmhead := (InsertionSupport.relation_members factor hrel row hrmem).1
        rw [← he]
        exact (hbound row.1 hmhead).trans (Ordinal.le_mul_left prefix hm.1)
      · exact hs.2.2 d hd

/-- Instantiating the genuine executed prefix identity yields exactly the
last-value lower/upper bounds required by Proposition 3.21, together with
the stronger all-entry upper bound needed by the recursive proof. -/
theorem execute_last_bounds (factor : Nat) (heads out : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode heads))
    (prefix input : Ordinal.{0}) (hp : 0 < prefix)
    (hbound : ∀ head ∈ heads, interpretation 0 head ≤ prefix)
    (hinput : input = prefix * interpretation 0 factor)
    (ho : out ∈ Insertion.execute (factor, heads)) :
    out ≠ [] ∧ interpretation 0 factor ≤ interpretation 0 (lastCode out) ∧
      interpretation 0 (lastCode out) ≤ input ∧
        ∀ d ∈ out, interpretation 0 d ≤ input := by
  have hs := execute_bounds factor heads out hh hf hm hb prefix hp hbound ho
  rw [hinput]
  exact ⟨hs.1, hs.2.1, hs.2.2 _ (lastCode_mem out hs.1), hs.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Bounds
