import Alexander313.Wilken.HereditaryPublicMtsCoveringLocalization

/-!
# Actual stored subqueries and the first predecessor's order bound

Canonical localization at the base is a literal singleton. Every stored
row is the independently executing query at its own public endpoint, by
the actual path-prefix theorem. Chronological strictness and the first
passing selection put that row no later than any passing competitor.
These facts use no numerical cost array or minimum-cover oracle. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.MinimumSupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)

theorem localization_strict (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta) :
    ((localization gamma d).map unionInterpretation).Pairwise (· < ·) := by
  have hv : (localization gamma d).map unionInterpretation =
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).map (SourceLocalization.value gamma) :=
    Localization.publicPath_values gamma _ (nativeRoot_spec gamma beta d hi hd).1
  exact hv.symm ▸ SourceLocalization.nativePath_strict gamma _ (nativeRoot_spec gamma beta d hi hd).1

theorem localization_base (gamma d : Nat) (hi : inputCheck gamma gamma = true)
    (hd : d ∈ SkNextSearch.Support.search gamma gamma) : localization gamma d = [gamma] := by
  have hr := nativeRoot_spec gamma gamma d hi hd
  have hv := SourceLocalization.ValueInvariance.nativePath_base_values gamma _ hr.1 hr.2
  apply SkPublicValueInvariance.canonical_words_eq _ _ (localization_checked gamma gamma d hi hd)
    (fun c hc => by
      rw [List.mem_singleton.mp hc]
      exact ((MuPublicDictionary.Support.inputCheck_image gamma).mp ((inputCheck_exact gamma gamma).mp hi).1).1)
  simpa only [List.map_singleton] using (localization_values gamma gamma d hi hd).trans hv

theorem execute_base (gamma : Nat) (out : List Nat) (ho : out ∈ execute gamma gamma) :
    out = [gamma] := by
  obtain ⟨hi, d, hd, hw⟩ := execute_spec gamma gamma out ho
  simpa only [localization_base gamma d hi hd, List.tail_cons, List.tail_nil,
    Support.word_nil] using hw

theorem base_execution (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    [gamma] ∈ execute gamma gamma := by
  have hp := (MuPublicDictionary.Support.inputCheck_image gamma).mp hg
  have hprincipal := EpsilonOffsets.epsilon_pos_principal hp.2.1
  have hi := ReachSupport.covering_caller gamma gamma [gamma] (Covering.root hg)
    hp.1 hprincipal.1 hprincipal.2
  obtain ⟨out, ho⟩ := execute_returns gamma gamma hi
  simpa only [execute_base gamma out ho] using ho

/-- The real independently executing stored subquery is derived from its
literal earlier native localization prefix, including the original root. -/
theorem entry_execution (gamma beta d : Nat) (entry : Support.Entry)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hm : entry ∈ Support.table gamma (localization gamma d).tail) :
    entry.2 ∈ execute gamma entry.1 := by
  rcases Support.table_entry_word gamma (localization gamma d).tail entry hm with
    he | ⟨before, after, hs, hw⟩
  · subst entry
    exact base_execution gamma ((inputCheck_exact gamma beta).mp hi).1
  · have hmap : ((SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail).map
        (UniformPublicReturn.publicCode gamma) = before ++ entry.1 :: after := by
      simpa only [localization, List.map_tail] using hs
    obtain ⟨nativeBefore, rest, htail, hbefore, hrest⟩ := List.map_eq_append_iff.mp hmap
    obtain ⟨current, nativeAfter, hrest', hcurrent, hafter⟩ := List.map_eq_cons_iff.mp hrest
    have htail' : (SourceLocalization.nativePath gamma (nativeRoot gamma d)).tail =
        nativeBefore ++ current :: nativeAfter := by rw [htail, hrest']
    obtain ⟨tail, ht⟩ := SourceLocalization.nativePath_head gamma (nativeRoot gamma d)
    have hfull : SourceLocalization.nativePath gamma (nativeRoot gamma d) =
        (SourceLocalization.baseRaw gamma :: nativeBefore) ++ current :: nativeAfter := by
      have he : tail = nativeBefore ++ current :: nativeAfter := by
        simpa only [ht, List.tail_cons] using htail'
      simp only [ht, he, List.cons_append]
    have ho := Localization.execute_at_prefix gamma beta d hi hd
      (SourceLocalization.baseRaw gamma :: nativeBefore) current nativeAfter hfull
    rw [hw]
    simpa only [List.cons_append, List.map_cons, List.map_append, List.map_singleton,
      Covering.base_public gamma beta hi, hbefore, hcurrent, List.tail_cons] using ho

/-- The first actually passing row has no larger value than any other
actually passing row in the same strictly chronological table. -/
theorem select_le_passing (target : Nat) (rows : List Support.Entry)
    (selected candidate : Support.Entry)
    (hs : Support.select target rows = some selected)
    (hm : candidate ∈ rows)
    (hp : PublicTrackingSequences.adjacencyCheck candidate.1 target = true)
    (ht : ((rows.map Prod.fst).map unionInterpretation).Pairwise (· < ·)) :
    unionInterpretation selected.1 ≤ unionInterpretation candidate.1 := by
  obtain ⟨before, after, he, hfailed, hpass⟩ := Support.select_first target rows selected hs
  rw [he] at hm ht
  simp only [List.map_append, List.map_cons] at ht
  rcases List.mem_append.mp hm with hm | hm
  · have hf := hfailed candidate hm
    exact False.elim (Bool.true_eq_false_eq_False (hp.symm.trans hf))
  · rcases List.mem_cons.mp hm with heq | hm
    · simpa only [heq] using
        (le_rfl : unionInterpretation selected.1 ≤ unionInterpretation selected.1)
    · have htail : (unionInterpretation selected.1 ::
          (after.map Prod.fst).map unionInterpretation).Pairwise (· < ·) := by
        simpa only [List.map_append, List.map_cons] using (List.pairwise_append.mp ht).2.1
      exact ((List.pairwise_cons.mp htail).1 _
        (List.mem_map.mpr ⟨candidate.1, List.mem_map.mpr ⟨candidate, hm, rfl⟩, rfl⟩)).le

theorem localization_split (gamma beta d : Nat) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    ∃ before, localization gamma d = (gamma :: before) ++ [beta] ∧
      (localization gamma d).tail = before ++ [beta] := by
  obtain ⟨before, he⟩ := Covering.localization_tail_last gamma beta d hi hd hlt
  obtain ⟨tail, ht⟩ := localization_head gamma beta d hi hd
  have hs : tail = before ++ [beta] := by simpa only [ht, List.tail_cons] using he
  exact ⟨before, by simpa only [ht, hs, List.cons_append], he⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.MinimumSupport
