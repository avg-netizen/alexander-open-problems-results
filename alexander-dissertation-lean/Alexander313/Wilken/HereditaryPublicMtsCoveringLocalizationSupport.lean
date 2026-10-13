import Alexander313.Wilken.HereditaryPublicMtsReach
import Alexander313.Wilken.HereditaryPublicMtsCoveringRecognitionSupport
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingLocalizationSupport

/-!
# Actual incoming-context endpoints along arbitrary genuine coverings

Each representative is chosen from a real terminating OWN-domain search.
Proper covering entries derive HIGH and their actual incoming-context mu
column. The original same-context successor theorem then nests their real
incoming endpoints, so every remaining covering target stays below them.
No incoming/original endpoint equality or localization membership is used.
Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringLocalizationSupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)
open CoveringRecognitionSupport (Steps)

/-- This proof-only representative is selected from an actual terminating
search when its genuine guard holds. It is not an executing recoder. -/
def representative (gamma beta : Nat) : Nat :=
  if hi : inputCheck gamma beta = true then
    nativeRoot gamma (Classical.choose (search_returns gamma beta hi))
  else SourceLocalization.baseRaw gamma

theorem representative_spec (gamma beta : Nat) (hi : inputCheck gamma beta = true) :
    SourceLocalization.Node gamma (representative gamma beta) ∧
      interpretation gamma (representative gamma beta) = unionInterpretation beta ∧
        UniformPublicReturn.publicCode gamma (representative gamma beta) = beta := by
  have hd := Classical.choose_spec (search_returns gamma beta hi)
  have hs := nativeRoot_spec gamma beta _ hi hd
  have hp := ReachSupport.parsed_publicCode gamma beta _ hi hd
  simpa only [representative, dif_pos hi] using
    And.intro ((SourceLocalization.inputCheck_exact gamma _).mp hs.1) (And.intro hs.2 hp)

theorem representative_high (gamma beta : Nat) (hi : inputCheck gamma beta = true)
    (hlt : unionInterpretation gamma < unionInterpretation beta)
    (he : Ordinal.omega0 ^ unionInterpretation beta = unionInterpretation beta) :
    Mu.inputCheck gamma (representative gamma beta) = true := by
  have hd := Classical.choose_spec (search_returns gamma beta hi)
  simpa only [representative, dif_pos hi] using
    EvaluationReferenceHeight.parsed_high gamma beta _ hi hd hlt he

/-- Genuine covering supplies the original OWN cut before actual public
mu is identified with the constructed incoming-context HIGH root. -/
theorem covered_epsilon_data (gamma beta : Nat) (codes : List Nat)
    (hc : Covering gamma beta codes)
    (hb : MuPublicDictionary.Support.inputCheck beta = true)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    inputCheck gamma beta = true ∧ Mu.inputCheck gamma (representative gamma beta) = true ∧
      interpretation gamma (representative gamma beta) = unionInterpretation beta ∧
        Mu.sourceValue gamma (representative gamma beta) = SkPublicRecurrence.muValue beta := by
  have hp := (MuPublicDictionary.Support.inputCheck_image beta).mp hb
  have hprincipal := EpsilonOffsets.epsilon_pos_principal hp.2.1
  have hi := ReachSupport.covering_caller gamma beta codes hc hp.1 hprincipal.1 hprincipal.2
  have hr := representative_spec gamma beta hi
  have hh := representative_high gamma beta hi hlt hp.2.1
  have hm := ContextSupport.high_public_mu gamma _ (ReachBound.covering_root_input hc) hh
    (hr.2.1.trans_lt (ReachBound.covering_lt_own hc))
  rw [hr.2.2] at hm
  exact ⟨hi, hh, hr.2.1, hm.2.symm⟩

theorem covering_le_current {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) :
    ∀ c ∈ codes, unionInterpretation c ≤ unionInterpretation current := by
  induction hc with
  | root hg =>
    intro c hm
    rw [List.mem_singleton.mp hm]
  | append previous current codes hp hedge ih =>
    intro c hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (ih c hm).trans ((Support.eligible_exact previous current).mp hedge).2.2.1.le
    · rw [List.mem_singleton.mp hm]

theorem covering_strict {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes) : (codes.map unionInterpretation).Pairwise (· < ·) := by
  induction hc with
  | root hg => simp only [List.map_singleton, List.pairwise_singleton]
  | append previous current codes hp hedge ih =>
    rw [List.map_append, List.map_singleton]
    apply List.pairwise_append.mpr
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_singleton.mp hb]
    exact (covering_le_current hp c hc).trans_lt
      ((Support.eligible_exact previous current).mp hedge).2.2.1

/-- Every literal member has a real covering prefix and a genuine
remaining edge sequence, rather than an asserted localization position. -/
theorem covering_member_suffix {gamma beta : Nat} {codes : List Nat}
    (hc : Covering gamma beta codes) (c : Nat) (hm : c ∈ codes) :
    ∃ prefix tail, Covering gamma c prefix ∧ Steps c tail beta := by
  revert hm
  induction hc with
  | root hg =>
    intro hm
    have he : c = gamma := List.mem_singleton.mp hm
    subst c
    exact ⟨[gamma], [], .root hg, .nil gamma⟩
  | append previous beta codes hp hedge ih =>
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨prefix, tail, hprefix, hs⟩ := ih hm
      exact ⟨prefix, tail ++ [beta], hprefix, hs.append_one beta hedge⟩
    · have he : c = beta := List.mem_singleton.mp hm
      subst c
      exact ⟨codes ++ [beta], [], .append previous beta codes hp hedge, .nil beta⟩

/-- All later targets remain below the actual incoming-context successor
of a proper intermediate entry. Genuine native endpoint nesting supplies
the induction; no equality to its selected-original endpoint is assumed. -/
theorem steps_lt_native_endpoint {gamma previous beta : Nat} {tail prefix : List Nat}
    (hs : Steps previous tail beta)
    (hc : Covering gamma previous prefix)
    (hp : MuPublicDictionary.Support.inputCheck previous = true)
    (hlt : unionInterpretation gamma < unionInterpretation previous) :
    unionInterpretation beta < Enclosure.sourceAlphaPlus gamma (representative gamma previous) := by
  revert hc hp hlt
  induction hs generalizing prefix with
  | nil previous =>
    intro hc hp hlt
    have hr := covered_epsilon_data gamma previous prefix hc hp hlt
    have hb := Enclosure.root_lt_enclosure gamma _ hr.2.1
    rw [Enclosure.delta_enclosure_value gamma _ hr.2.1] at hb
    exact hr.2.2.1.symm.trans_lt hb
  | cons previous next beta tail hedge htail ih =>
    intro hc hp hlt
    have hr := covered_epsilon_data gamma previous prefix hc hp hlt
    have he := (Support.eligible_exact previous next).mp hedge
    have hnext : unionInterpretation next <
        Enclosure.sourceAlphaPlus gamma (representative gamma previous) :=
      (he.2.2.2.trans_eq hr.2.2.2.symm).trans_lt
        (SourceAdditiveTracking.EndpointSupport.mu_lt_endpoint gamma _ hr.2.1)
    have hcover := Covering.append previous next prefix hc hedge
    have hstrict := hlt.trans he.2.2.1
    cases htail with
    | nil => exact hnext
    | cons next following beta rest hfollowing hrest =>
      have hproper := ((Support.eligible_exact next following).mp hfollowing).1
      have hn := covered_epsilon_data gamma next _ hcover hproper hstrict
      have hnest := SourceAdditiveTracking.EndpointSupport.endpoint_nested gamma
        (representative gamma previous) (representative gamma next) hr.2.1 hn.2.1
        (by rw [hr.2.2.1, hn.2.2.1]; exact he.2.2.1)
        (hn.2.2.1.trans_lt hnext)
      exact (ih hcover hproper hstrict).trans hnest

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringLocalizationSupport
