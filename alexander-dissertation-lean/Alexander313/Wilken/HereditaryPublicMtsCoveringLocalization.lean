import Alexander313.Wilken.HereditaryPublicMtsCoveringLocalizationSupport
import Alexander313.Wilken.HereditaryPublicMtsLocalization

/-!
# Every genuine public covering is a subsequence of actual localization

Actual terminating searches construct all intermediate HIGH roots at the
literal original epsilon. Their true incoming-context mu edges nest real
incoming successor endpoints. The native first-crossing theorem therefore
puts every covering value in the target's independently computed path.
Strict chronological values give a subsequence; canonical value injection
also identifies the literal public codes. No path membership, endpoint
identity, reachability witness, or assigned localization is supplied.
Source-only uncompiled candidates. Minimum and lexicographic optimality of
the least-table covering remain separate.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringLocalization

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)
open CoveringLocalizationSupport

theorem covering_checked {gamma beta : Nat} {codes : List Nat}
    (hc : Covering gamma beta codes) : ∀ c ∈ codes, Canonical.check c = true := by
  induction hc with
  | root hg =>
    intro c hm
    rw [List.mem_singleton.mp hm]
    exact ((MuPublicDictionary.Support.inputCheck_image gamma).mp hg).1
  | append previous beta codes hp hedge ih =>
    intro c hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ih c hm
    · rw [List.mem_singleton.mp hm]
      exact ((Support.eligible_exact previous beta).mp hedge).2.1

/-- The intermediate caller and endpoint interval are derived from the
independent covering itself before actual localization membership is used. -/
theorem covering_member_value (gamma beta d : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (c : Nat) (hm : c ∈ codes) :
    unionInterpretation c ∈ (localization gamma d).map unionInterpretation := by
  by_cases hgamma : c = gamma
  · subst c
    obtain ⟨tail, he⟩ := localization_head gamma beta d hi hd
    rw [he, List.map_cons]
    exact List.mem_cons_self
  by_cases hbeta : c = beta
  · subst c
    obtain ⟨before, he⟩ := Covering.localization_tail_last gamma beta d hi hd hlt
    apply List.mem_map_of_mem
    apply List.mem_of_mem_tail
    rw [he]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨prefix, tail, hprefix, hs⟩ := covering_member_suffix hc c hm
  have hproper : MuPublicDictionary.Support.inputCheck c = true := by
    cases hs with
    | nil => exact False.elim (hbeta rfl)
    | cons previous next beta tail hedge htail =>
      exact ((Support.eligible_exact previous next).mp hedge).1
  have hstrict : unionInterpretation gamma < unionInterpretation c :=
    (ReachBound.covering_root_or_lt hprefix).resolve_left hgamma
  have hr := covered_epsilon_data gamma c prefix hprefix hproper hstrict
  have hn := representative_spec gamma c hr.1
  have htarget := nativeRoot_spec gamma beta d hi hd
  have hbound : SourceLocalization.value gamma (representative gamma c) ≤
      SourceLocalization.value gamma (nativeRoot gamma d) := by
    change interpretation gamma (representative gamma c) ≤ interpretation gamma (nativeRoot gamma d)
    rw [hn.2.1, htarget.2]
    exact covering_le_current hc c hm
  have hbase : base gamma < SourceLocalization.value gamma (representative gamma c) := by
    change unionInterpretation gamma < interpretation gamma (representative gamma c)
    rw [hn.2.1]
    exact hstrict
  have hend : SourceLocalization.value gamma (nativeRoot gamma d) <
      Enclosure.sourceAlphaPlus gamma (representative gamma c) := by
    change interpretation gamma (nativeRoot gamma d) < _
    rw [htarget.2]
    exact steps_lt_native_endpoint hs hprefix hproper hstrict
  have hmem := SourceAdditiveTracking.LocalizationSupport.nativePath_interval_mem gamma
    (nativeRoot gamma d) (representative gamma c) htarget.1 hn.1 hbase hbound hend
  have hvalues : (localization gamma d).map unionInterpretation =
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).map (SourceLocalization.value gamma) :=
    Localization.publicPath_values gamma _ htarget.1
  rw [hvalues]
  simpa only [SourceLocalization.value, hn.2.1] using hmem

/-- Source 3.26 on the represented original epsilon domain: every genuine
covering's chronological values are a subsequence of actual localization. -/
theorem covering_values_sublist (gamma beta d : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    (codes.map unionInterpretation).Sublist ((localization gamma d).map unionInterpretation) := by
  have htarget := nativeRoot_spec gamma beta d hi hd
  have hvalues : (localization gamma d).map unionInterpretation =
      (SourceLocalization.nativePath gamma (nativeRoot gamma d)).map (SourceLocalization.value gamma) :=
    Localization.publicPath_values gamma _ htarget.1
  apply SourceAdditiveTracking.LocalizationSupport.strict_sublist_of_subset
    _ _ (covering_strict hc)
    (hvalues.symm ▸ SourceLocalization.nativePath_strict gamma _ htarget.1)
  intro value hv
  obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hv
  exact covering_member_value gamma beta d codes hc hi hd hlt c hm

/-- Canonical public syntax strengthens the ordinal subsequence to the
literal numerical public covering, without written native path equality. -/
theorem covering_sublist (gamma beta d : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes) (hi : inputCheck gamma beta = true)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    codes.Sublist (localization gamma d) := by
  obtain ⟨chosen, hsub, hvalues⟩ := List.sublist_map_iff.mp
    (covering_values_sublist gamma beta d codes hc hi hd hlt)
  have hcanon : ∀ c ∈ chosen, Canonical.check c = true := by
    intro c hm
    exact localization_checked gamma beta d hi hd c (hsub.subset hm)
  have he : codes = chosen := SkPublicValueInvariance.canonical_words_eq codes chosen
    (covering_checked hc) hcanon hvalues
  exact he.symm ▸ hsub

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringLocalization
