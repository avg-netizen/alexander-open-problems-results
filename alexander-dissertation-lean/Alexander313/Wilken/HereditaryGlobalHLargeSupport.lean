import Alexander313.Wilken.HereditaryPublicMtsCoveringRecognition
import Alexander313.Wilken.HereditaryGlobalHSmallSupport

/-!
# Genuine penultimate epsilon and global reference splice for large h

The independent covering recurrence supplies every proper epsilon caller,
including the actual penultimate code and its final mu cover. The original
segmented global reference keeps its literal upsilon chain when this genuine
covering prefix is attached. No mts definition, segment or output tracker
is used as a premise. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalHLargeSupport

open PublicMts.CoveringSupport (Covering)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton
  lastCode_singleton stripLast_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)

/-- An actual final adjacency extends the separately defined reference. -/
theorem reference_append (prefix : List Nat) (a b : Nat)
    (hr : PublicTrackingSequences.Reference (prefix ++ [a]))
    (hb : MuPublicDictionary.Support.inputCheck b = true)
    (he : PublicTrackingSequences.adjacencyCheck a b = true) :
    PublicTrackingSequences.Reference (prefix ++ [a, b]) := by
  revert hr
  induction prefix with
  | nil =>
    intro hr
    have ha := hr.nodes a List.mem_cons_self
    have hs := (PublicMts.Support.eligible_exact a b).mp he
    exact .cons a b [] ha hs.2.2.1 hs.2.2.2 (.one b hb)
  | cons c rest ih =>
    intro hr
    cases rest with
    | nil =>
      cases hr with
      | cons c a xs hc hca hcover ht =>
        have hs := (PublicMts.Support.eligible_exact a b).mp he
        exact .cons c a [b] hc hca hcover
          (.cons a b [] hs.1 hs.2.2.1 hs.2.2.2 (.one b hb))
    | cons d rest =>
      cases hr with
      | cons c d xs hc hcd hcover ht =>
        exact .cons c d (rest ++ [a, b]) hc hcd hcover (ih ht)

/-- Proper final admission turns the whole independent covering into an
actual proper epsilon reference, with no claimed input spelling identity. -/
theorem covering_reference {gamma current : Nat} {codes : List Nat}
    (hc : Covering gamma current codes)
    (ht : MuPublicDictionary.Support.inputCheck current = true) :
    PublicTrackingSequences.Reference codes := by
  revert ht
  induction hc with
  | root hg => intro ht; exact .one gamma hg
  | append previous current codes hp he ih =>
    intro ht
    have hs := (PublicMts.Support.eligible_exact previous current).mp he
    have hr := ih hs.1
    obtain ⟨last, hsplit, hmem⟩ := stripLast_split codes hp.nonempty
    have hl : last = previous := by
      calc
        last = lastCode codes := by rw [hsplit, lastCode_append_singleton]
        _ = previous := hp.last
    rw [hl] at hsplit
    have href : PublicTrackingSequences.Reference (stripLast codes ++ [previous]) := by
      rw [← hsplit]; exact hr
    rw [hsplit]
    simpa only [List.append_assoc, List.singleton_append] using
      reference_append (stripLast codes) previous current href ht he

/-- Genuine references splice at their shared literal epsilon. -/
theorem reference_splice (prefix : List Nat) (gamma : Nat) (tail : List Nat)
    (hp : PublicTrackingSequences.Reference (prefix ++ [gamma]))
    (ht : PublicTrackingSequences.Reference (gamma :: tail)) :
    PublicTrackingSequences.Reference (prefix ++ gamma :: tail) := by
  revert hp
  induction prefix with
  | nil => intro hp; exact ht
  | cons a rest ih =>
    intro hp
    cases rest with
    | nil =>
      cases hp with
      | cons a gamma xs ha hlt hcover href =>
        exact .cons a gamma tail ha hlt hcover ht
    | cons b rest =>
      cases hp with
      | cons a b xs ha hlt hcover href =>
        exact .cons a b (rest ++ gamma :: tail) ha hlt hcover (ih href)

/-- The independently proved proper covering prefix retains the original
literal upsilon segment and its genuine first endpoint gap. -/
theorem covering_global_reference (prefix : List Nat) (gamma current : Nat) (codes : List Nat)
    (hp : GlobalTrackingSequences.Reference (prefix ++ [gamma]))
    (hc : Covering gamma current codes)
    (ht : MuPublicDictionary.Support.inputCheck current = true) :
    GlobalTrackingSequences.Reference (prefix ++ codes) := by
  have hg := PublicMts.ReachBound.covering_root_input hc
  obtain ⟨m, before, hprefix, hrelative, hgap⟩ :=
    GlobalTrackingSequences.SmallHSupport.proper_last_segment prefix gamma hp hg
  obtain ⟨tail, hcodes⟩ := hc.first
  have href := covering_reference hc ht
  rw [hcodes] at href
  have hspliced := reference_splice before gamma tail hrelative href
  refine ⟨m, before ++ gamma :: tail, ?_, .of_relative hspliced, ?_⟩
  · simp only [hprefix, hcodes, List.append_assoc]
  · cases before <;> exact hgap

/-- A strict covering has a real penultimate epsilon and final public-mu
edge, with the literal two-code suffix required by Definition3.34. -/
theorem covering_penultimate {gamma beta : Nat} {codes : List Nat}
    (hc : Covering gamma beta codes)
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    ∃ eta : List Nat, ∃ epsilon : Nat, codes = eta ++ [epsilon, beta] ∧
      Covering gamma epsilon (eta ++ [epsilon]) ∧
        PublicTrackingSequences.adjacencyCheck epsilon beta = true := by
  cases hc with
  | root hg => exact False.elim (hlt.ne rfl)
  | append previous current before hp he =>
    obtain ⟨last, hsplit, hmem⟩ := stripLast_split before hp.nonempty
    have hl : last = previous := by
      calc
        last = lastCode before := by rw [hsplit, lastCode_append_singleton]
        _ = previous := hp.last
    rw [hl] at hsplit
    refine ⟨stripLast before, previous, ?_, ?_, he⟩
    · rw [hsplit, List.append_assoc]
      rfl
    · rw [← hsplit]; exact hp

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalHLargeSupport
