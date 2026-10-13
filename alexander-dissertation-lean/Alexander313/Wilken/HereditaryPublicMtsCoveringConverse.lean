import Alexander313.Wilken.HereditaryPublicMtsCoveringConverseSupport

/-!
# Genuine coverings force the independently computed FIRST cut

Every actual stored word entry belongs to the actual localization. A true
public edge from the original root bounds FIRST directly. At a later
entry, its actual position and strict edge derive HIGH admission and its
true OWN-context mu column before transporting FIRST. Covering induction
therefore proves the converse, and actual mts execution is a covering
exactly on its independently computed FIRST cut. The separate outside-cut
reach question and semantic singleton-boundary connection remain open.
Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringConverse

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open FirstSupport
open CoveringSupport (Covering)
open Covering (Marked)

/-- Along an actual localization edge, the previous FIRST cut propagates
forward after the genuine native HIGH and OWN-context callers are derived. -/
theorem passing_successor_marked (gamma beta d previous current : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hp : previous ∈ gamma :: (localization gamma d).tail)
    (hc : current ∈ (localization gamma d).tail)
    (hm : previous = gamma ∨ Marked gamma previous)
    (hedge : PublicTrackingSequences.adjacencyCheck previous current = true) :
    Marked gamma current := by
  have hc' : current ∈ ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
      (UniformPublicReturn.publicCode gamma) := by
    simpa only [localization, List.map_tail] using hc
  obtain ⟨next, hn, hnc⟩ := List.mem_map.mp hc'
  have hinput := (nativeRoot_spec gamma beta d hi hd).1
  have hnnode := SourceLocalization.nativePath_nodes gamma _ hinput next (List.mem_of_mem_tail hn)
  refine ⟨next, hnnode, hnc, ?_⟩
  rcases hm with hroot | hmarked
  · have hedge' : PublicTrackingSequences.adjacencyCheck gamma
        (UniformPublicReturn.publicCode gamma next) = true := by
      simpa only [hroot, hnc] using hedge
    exact root_edge_first_bound gamma next hnnode hedge'
  · rcases List.mem_cons.mp hp with hroot | hp
    · have hedge' : PublicTrackingSequences.adjacencyCheck gamma
          (UniformPublicReturn.publicCode gamma next) = true := by
        simpa only [hroot, hnc] using hedge
      exact root_edge_first_bound gamma next hnnode hedge'
    · have hp' : previous ∈ ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
          (UniformPublicReturn.publicCode gamma) := by
        simpa only [localization, List.map_tail] using hp
      obtain ⟨prior, ha, hap⟩ := List.mem_map.mp hp'
      have hanode := SourceLocalization.nativePath_nodes gamma _ hinput prior (List.mem_of_mem_tail ha)
      have hs := (Support.eligible_exact previous current).mp hedge
      have hstrict : interpretation gamma prior < interpretation gamma next := by
        rw [← (node_public_spec gamma prior hanode).2,
          ← (node_public_spec gamma next hnnode).2, hap, hnc]
        exact hs.2.2.1
      have hbound := localization_bounded gamma beta d hi hd next (List.mem_of_mem_tail hn)
      have hhigh := Covering.tail_high gamma (nativeRoot gamma d) prior hinput ha
        ((hstrict.trans_le hbound).trans_eq (nativeRoot_spec gamma beta d hi hd).2.symm)
      have hcut := (localization_bounded gamma beta d hi hd prior (List.mem_of_mem_tail ha)).trans_lt
        ((inputCheck_exact gamma beta).mp hi).2.2.2.2.2
      have he := public_edge_first_eq gamma prior next ((inputCheck_exact gamma beta).mp hi).1
        hhigh hnnode hcut (by simpa only [hap, hnc] using hedge)
      have hb := Covering.marked_first gamma prior hanode (hap.symm ▸ hmarked)
      exact he.symm.le.trans hb

/-- A covering supported by the genuine localization starts at the root
or ends at a marked FIRST. Its HIGH and context premises are conclusions. -/
theorem covering_marked (gamma beta d current : Nat) (codes : List Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hc : Covering gamma current codes)
    (hmem : ∀ c ∈ codes, c ∈ gamma :: (localization gamma d).tail) :
    current = gamma ∨ Marked gamma current := by
  revert hmem
  induction hc with
  | root hr =>
    intro hmem
    exact Or.inl rfl
  | append previous current codes hp hedge ih =>
    intro hmem
    have hprevious : ∀ c ∈ codes, c ∈ gamma :: (localization gamma d).tail := by
      intro c hc
      exact hmem c (List.mem_append.mpr (Or.inl hc))
    have hm := ih hprevious
    have hpMem := hprevious previous (CoveringConverseSupport.covering_current_mem hp)
    have hcMem := hmem current (List.mem_append.mpr (Or.inr List.mem_cons_self))
    rcases List.mem_cons.mp hcMem with hroot | htail
    · exact Or.inl hroot
    · exact Or.inr (passing_successor_marked gamma beta d previous current hi hd hpMem htail hm hedge)

theorem search_word_covering_first (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (hc : Covering gamma beta (Support.word gamma (localization gamma d).tail)) :
    firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma := by
  have hm := covering_marked gamma beta d beta _ hi hd hc
    (CoveringConverseSupport.word_members gamma (localization gamma d).tail)
  have hne : beta ≠ gamma := by
    intro he
    exact hlt.ne (congrArg unionInterpretation he).symm
  have hm := hm.resolve_left hne
  have hn := (SourceLocalization.inputCheck_exact gamma _).mp
    (nativeRoot_spec gamma beta d hi hd).1
  have hp := node_public_spec gamma (nativeRoot gamma d) hn
  have hcode : UniformPublicReturn.publicCode gamma (nativeRoot gamma d) = beta :=
    Canonical.check_value_injective _ _ hp.1 ((inputCheck_exact gamma beta).mp hi).2.1
      (hp.2.trans (nativeRoot_spec gamma beta d hi hd).2)
  exact Covering.marked_first gamma (nativeRoot gamma d) hn (hcode.symm ▸ hm)

/-- This iff is about actual covering of the actual numerical word. It
does not replace a covering by arbitrary graph reachability. -/
theorem search_word_covering_iff_first (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta (Support.word gamma (localization gamma d).tail) ↔
      firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma :=
  ⟨search_word_covering_first gamma beta d hi hd hlt,
    Covering.search_word_covering gamma beta d hi hd hlt⟩

/-- Any actual execution and actual search derive the same stored word,
so the exact covering criterion applies to the emitted numerical word. -/
theorem execute_covering_iff_first (gamma beta d : Nat) (out : List Nat)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ho : out ∈ execute gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta out ↔
      firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma := by
  have hi := (execute_spec gamma beta out ho).1
  have hw : Support.word gamma (localization gamma d).tail ∈ execute gamma beta := by
    simpa only [execute, hi, Bool.cond_true] using
      Part.mem_map (fun e => Support.word gamma (localization gamma e).tail) hd
  have he := Part.mem_unique ho hw
  rw [he]
  exact search_word_covering_iff_first gamma beta d hi hd hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringConverse
