import Alexander313.Wilken.SourceOneNativeAdditiveTrackingLocalizationSupport
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingProperPrefix
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertionFidelity

/-!
# Genuine original source-one tracking localization subsequences

An actual RAW tracking word supplies each adjacent mu cover and the genuine
original principal caller of the next entry. When the preceding entry is
strictly smaller, its whole preceding epsilon reference is also smaller.
The actual own-endpoint theorem and first-crossing kernel therefore put the
entire prefix on the independently computed original localization by VALUE.
Specializing to the executing full assignment proves source3.21.4, without
assuming a tracking prefix, source support or a localization equation.
Original check zero is retained throughout. Uncompiled source candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.LocalizationProperties

open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton
  stripLast_append_singleton)
open SkTracking.Support (stripLast_cons_nonempty)

private theorem reference_pair_suffix (before : List Nat) (a b : Nat) (rest : List Nat)
    (hr : SourceTrackingRaw.Reference (before ++ a :: b :: rest)) :
    SourceTrackingRaw.Reference (a :: b :: rest) := by
  revert hr
  induction before with
  | nil => intro hr; exact hr
  | cons c cs ih =>
    intro hr
    cases cs with
    | nil =>
      cases hr with
      | cons c a xs hc hca hcover tail => exact tail
    | cons d ds =>
      cases hr with
      | cons c d xs hc hcd hcover tail => exact ih tail

/-- The real checker derives both the preceding reference and the
actual adjacent original mu cover, even when the next entry is final. -/
theorem tracking_adjacent (word before : List Nat) (a b : Nat) (rest : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true)
    (he : word = before ++ a :: b :: rest) :
    SourceTrackingRaw.Reference (before ++ [a]) ∧
      SourceLocalization.RootAdapter.inputCheck b = true ∧
      interpretation 0 b ≤ SourceTrackingRaw.Support.muValue a := by
  have hs := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  have hp := hs.2.1
  rw [he, InsertionFidelity.stripLast_append_nonempty before _ (List.cons_ne_nil _ _),
    stripLast_cons_nonempty a _ (List.cons_ne_nil _ _)] at hp
  have href : SourceTrackingRaw.Reference (before ++ [a]) :=
    InsertionFidelity.reference_prefix (before ++ [a]) (stripLast (b :: rest))
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp)
  refine ⟨href, ?_⟩
  cases rest with
  | nil =>
    have hpword : stripLast word = before ++ [a] := by
      rw [he]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        stripLast_append_singleton (before ++ [a]) b
    have hlword : lastCode word = b := by
      rw [he]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        lastCode_append_singleton (before ++ [a]) b
    have hne : before ++ [a] ≠ [] := by
      intro hz
      exact List.cons_ne_nil a [] (List.append_eq_nil_iff.mp hz).2
    have hb := hs.2.2.2.2.2
    rw [hpword, if_neg hne, hlword, lastCode_append_singleton] at hb
    refine ⟨(SourceLocalization.RootAdapter.inputCheck_exact b).mpr
      ⟨?_, hb.1.le, ?_⟩, hb.2⟩
    · simpa only [hlword] using hs.2.2.1
    · simpa only [hlword] using hs.2.2.2.2.1
  | cons d ds =>
    rw [stripLast_cons_nonempty b _ (List.cons_ne_nil _ _)] at hp
    have htail := reference_pair_suffix before a b (stripLast (d :: ds)) hp
    have hb := (SourceTrackingRaw.Support.inputCheck_exact b).mp
      (htail.nodes b (List.mem_cons_of_mem _ List.mem_cons_self))
    have hadd : Ordinal.IsPrincipal (· + ·) (interpretation 0 b) := by
      rw [← hb.2.2]
      exact Ordinal.isPrincipal_add_omega0_opow _
    exact ⟨(SourceLocalization.RootAdapter.inputCheck_exact b).mpr
      ⟨hb.1, hb.2.1.le, hadd⟩, htail.cover⟩

private theorem reference_strict_append (before : List Nat) (a b : Nat)
    (hr : SourceTrackingRaw.Reference (before ++ [a]))
    (hlt : interpretation 0 a < interpretation 0 b) :
    ((before ++ [a, b]).map (interpretation 0)).Pairwise (· < ·) := by
  have hp := hr.strict
  have hbefore := hp
  rw [List.map_append, List.map_singleton] at hbefore
  have he : before ++ [a, b] = (before ++ [a]) ++ [b] := by
    simpa only [List.cons_append, List.nil_append] using (List.append_assoc before [a] [b]).symm
  rw [he, List.map_append, List.map_singleton]
  apply List.pairwise_append.mpr
  refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
  intro v hv w hw
  have hw : w = interpretation 0 b := List.mem_singleton.mp hw
  subst w
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
  rcases List.mem_append.mp hc with hc | hc
  · exact ((List.pairwise_append.mp hbefore).2.2 _
      (List.mem_map.mpr ⟨c, hc, rfl⟩) _ List.mem_cons_self).trans hlt
  · have hc : c = a := List.mem_singleton.mp hc
    subst c
    exact hlt

/-- The actual original RAW tracker, not an assumed assignment or
prefix certificate, yields the printed localization subsequence clause. -/
theorem tracking_localization_subsequence (word before : List Nat) (a b : Nat) (rest : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true)
    (he : word = before ++ a :: b :: rest)
    (hlt : interpretation 0 a < interpretation 0 b) :
    ((before ++ [a, b]).map (interpretation 0)).Sublist
      ((Localization.nativePath 0 (SourceLocalization.RootAdapter.rootCode b)).map
        (Localization.value 0)) := by
  have hs := tracking_adjacent word before a b rest hw he
  have hne : before ++ [a] ≠ [] := by
    intro hz
    exact List.cons_ne_nil a [] (List.append_eq_nil_iff.mp hz).2
  have hstrict := reference_strict_append before a b hs.1 hlt
  have hp : (((before ++ [a]) ++ [b]).map (interpretation 0)).Pairwise (· < ·) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hstrict
  have ho := LocalizationSupport.reference_localization_subsequence (before ++ [a]) b
    hs.1 hne hs.2.1 (by simpa only [lastCode_append_singleton] using hs.2.2) hp
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using ho

/-- This is source3.21.4 for the genuine complete original-source-one
assignment: every actual adjacent cover, and the complete localization
VALUE subsequence whenever that adjacent pair increases strictly. -/
theorem execute_localization (current : Nat) (word : List Nat)
    (ho : word ∈ Assignment.execute current)
    (before : List Nat) (a b : Nat) (rest : List Nat)
    (he : word = before ++ a :: b :: rest) :
    interpretation 0 b ≤ SourceTrackingRaw.Support.muValue a ∧
      (interpretation 0 a < interpretation 0 b →
        ((before ++ [a, b]).map (interpretation 0)).Sublist
          ((Localization.nativePath 0 (SourceLocalization.RootAdapter.rootCode b)).map
            (Localization.value 0))) := by
  have hw := Assignment.execute_tracking current word ho
  exact ⟨(tracking_adjacent word before a b rest hw he).2.2,
    fun hlt => tracking_localization_subsequence word before a b rest hw he hlt⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.LocalizationProperties
