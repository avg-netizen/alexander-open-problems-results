import Alexander313.Wilken.HereditaryMuCoveredRelativePublicFidelitySupport

/-!
# The actual covered relative assignment derives its public certificate

Actual full source execution bounds every written entry by its input.
The independent extended-mu input bound therefore licenses genuine public
mu fidelity for each RAW epsilon prefix node. Its original source reference
and final cover transport to the independently defined proper public
Tracking predicate. The real upper-boundary branch is a literal singleton.
No input tracker, supplied representative, source interval or public mu
equality is assumed in the final executing theorem. Uncompiled source only.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.CoveredPublicMu

open Support
open Hereditary.FinePredecessor (stripLast stripLast_mem)
open SourceTrackingSequences (lastCode lastCode_mem)
open GlobalAdditiveTracking.RelativeCertificate (stripLast_map lastCode_map)

theorem reference_tail (gamma a : Nat) (xs : List Nat)
    (hr : SourceTrackingRaw.Reference gamma (a :: xs)) : SourceTrackingRaw.Reference gamma xs := by
  refine ⟨fun c hc => hr.nodes c (List.mem_cons_of_mem _ hc), ?_⟩
  cases xs with
  | nil => exact .nil
  | cons b xs =>
    have ht := hr.2
    change SourceTrackingSequences.Reference gamma
      (SourceTrackingRaw.Support.rootCode gamma a :: SourceTrackingRaw.Support.rootCode gamma b ::
        SourceTrackingRaw.Support.rootWord gamma xs) at ht
    cases ht with
    | cons a b xs ha hab hcover ht => exact ht

theorem covered_reference (gamma : Nat) (xs : List Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (hr : SourceTrackingRaw.Reference gamma xs)
    (hbound : ∀ c ∈ xs, interpretation gamma c ≤ GlobalTrackingSequences.muValue gamma) :
    PublicTrackingSequences.Reference (xs.map (UniformPublicReturn.publicCode gamma)) := by
  revert hr hbound
  induction xs with
  | nil => intro hr hb; exact .nil
  | cons a xs ih =>
    intro hr hbound
    have ha := hr.nodes a List.mem_cons_self
    have hm := raw_public_mu gamma a hg ha (hbound a List.mem_cons_self)
    cases xs with
    | nil => exact .one _ hm.1
    | cons b xs =>
      have hb := hr.nodes b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hva := (UniformPublicReturn.publicCode_spec gamma a
        ((UniformPublicReturn.inputCheck_exact gamma a).mpr
          ((SourceTrackingRaw.Support.inputCheck_exact gamma a).mp ha).1)).2
      have hvb := (UniformPublicReturn.publicCode_spec gamma b
        ((UniformPublicReturn.inputCheck_exact gamma b).mpr
          ((SourceTrackingRaw.Support.inputCheck_exact gamma b).mp hb).1)).2
      have hab : interpretation gamma a < interpretation gamma b :=
        (List.pairwise_cons.mp (show
          (interpretation gamma a :: (b :: xs).map (interpretation gamma)).Pairwise (· < ·)
          from by simpa only [List.map_cons] using hr.strict)).1 _
            (List.mem_map.mpr ⟨b, List.mem_cons_self, rfl⟩)
      refine .cons _ _ _ hm.1 ?_ ?_
        (ih (reference_tail gamma a (b :: xs) hr)
          (fun c hc => hbound c (List.mem_cons_of_mem _ hc)))
      · simpa only [hva, hvb] using hab
      · simpa only [SkPublicRecurrence.muValue, hm.2, hvb] using hr.cover

/-- Every source tracking cover uses the independently queried public mu,
with its actual contextual caller derived from the original entry bound. -/
theorem covered_tracking (gamma : Nat) (word : List Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (hw : SourceTrackingRaw.trackingCheck gamma word = true)
    (hbound : ∀ c ∈ word, interpretation gamma c ≤ GlobalTrackingSequences.muValue gamma) :
    PublicTrackingSequences.Tracking (word.map (UniformPublicReturn.publicCode gamma)) := by
  have ht := (SourceTrackingRaw.trackingCheck_conditions gamma word).mp hw
  have hl := GlobalAdditiveTracking.Return.native_word_low gamma word hw
  have hp (c : Nat) (hc : c ∈ word) := UniformPublicReturn.publicCode_spec gamma c
    ((UniformPublicReturn.inputCheck_exact gamma c).mpr (hl c hc))
  have hn : word.map (UniformPublicReturn.publicCode gamma) ≠ [] :=
    fun h => ht.1 (List.map_eq_nil_iff.mp h)
  have hf := hp (lastCode word) (lastCode_mem word ht.1)
  have hlast := lastCode_map (UniformPublicReturn.publicCode gamma) word ht.1
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (hp d hd).1
  · rw [stripLast_map]
    exact covered_reference gamma (stripLast word) hg ht.2.1
      (fun c hc => hbound c (stripLast_mem word c hc))
  · rw [hlast, hf.2]
    exact ht.2.2.2.1
  · rw [hlast, hf.2]
    exact ht.2.2.2.2.1
  · by_cases he : stripLast word = []
    · have hem : stripLast (word.map (UniformPublicReturn.publicCode gamma)) = [] := by
        rw [stripLast_map, he, List.map_nil]
      rw [if_pos hem, hlast, hf.2]
      have hb : base gamma ≤ interpretation gamma (lastCode word) := by
        simpa only [if_pos he] using ht.2.2.2.2.2
      exact (Order.one_le_iff_pos.mpr
        (base_pos gamma (MuCoveredRelativeAssignment.Support.base_caller gamma hg))).trans hb
    · have hem : stripLast (word.map (UniformPublicReturn.publicCode gamma)) ≠ [] := by
        rw [stripLast_map]
        exact fun h => he (List.map_eq_nil_iff.mp h)
      have hgRaw := ht.2.1.nodes _ (lastCode_mem (stripLast word) he)
      have hm := raw_public_mu gamma (lastCode (stripLast word)) hg hgRaw
        (hbound _ (stripLast_mem word _ (lastCode_mem (stripLast word) he)))
      have hb : 1 < interpretation gamma (lastCode word) ∧
          interpretation gamma (lastCode word) ≤
            SourceTrackingRaw.Support.muValue gamma (lastCode (stripLast word)) := by
        simpa only [if_neg he] using ht.2.2.2.2.2
      rw [if_neg hem, hlast, hf.2, stripLast_map,
        lastCode_map (UniformPublicReturn.publicCode gamma) _ he]
      simpa only [SkPublicRecurrence.muValue, hm.2] using hb

/-- The complete source assignment itself derives every entry's bound
from the real input value; no tracker or per-node interval is supplied. -/
theorem assignment_tracking (gamma raw : Nat) (word : List Nat)
    (hg : GlobalMuDictionary.Support.inputCheck gamma = true)
    (ho : word ∈ SourceAdditiveTracking.Assignment.execute gamma raw)
    (hb : interpretation gamma raw ≤ GlobalTrackingSequences.muValue gamma) :
    PublicTrackingSequences.Tracking (MuCoveredRelativeAssignment.publicWord gamma word) := by
  have hs := (SourceAdditiveTracking.Assignment.execute_spec gamma raw word ho).2.1
  exact covered_tracking gamma word hg hs.1 (fun c hc => (hs.2.1 c hc).trans hb)

/-- EVERY independently executing extended-mu-covered relative assignment,
including the actual endpoint singleton, derives its independent public
Tracking certificate. Actual search/execution derives all original callers. -/
theorem execute_tracking (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta) :
    PublicTrackingSequences.Tracking out := by
  have hs := (MuCoveredRelativeAssignment.execute_clauses gamma beta out).mp ho
  have hi := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp hs.1
  rcases hs.2 with ⟨hb, rfl⟩ | ⟨hb, raw, word, hr, hw, rfl⟩
  · have hgamma := (GlobalMuDictionary.Support.inputCheck_exact gamma).mp hi.1
    exact PublicTrackingSequences.singleton_tracking beta hi.2.1 hi.2.2.1 hi.2.2.2.1
      ((EpsilonOffsets.epsilon_one_lt hgamma.2).le.trans hi.2.2.2.2.1)
  · have hc := SkNextSearch.Support.search_spec gamma beta raw hr
    have hcover : interpretation gamma raw ≤ GlobalTrackingSequences.muValue gamma := by
      rw [hc.2.2.2]
      exact hi.2.2.2.2.2
    exact assignment_tracking gamma raw word hi.1 hw hcover

theorem execute_trackingCheck (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ MuCoveredRelativeAssignment.execute gamma beta) :
    PublicTrackingSequences.trackingCheck out = true :=
  (PublicTrackingSequences.trackingCheck_exact out).mpr (execute_tracking gamma beta out ho)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.CoveredPublicMu
