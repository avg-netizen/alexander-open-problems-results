import Alexander313.Wilken.SourceOneNativeAdditiveTrackingInsertionFidelity
import Alexander313.Wilken.SourceOneOmegaQuotientSupport

/-!
# Genuine original source-one final-epsilon append branch

The preceding code is the actual last proper-prefix head, or the genuine
original unit theta-zero-zero term when that prefix is empty. Original
check-zero admission licenses the actual strict comparator. The raw final
epsilon guard and real original mu cover recognize exactly the printed
append branch. Its whole old headword is derived as an original reference
before appending the unchanged factor. No Native base-one parser or
supplied epsilon, adjacency, cover or tracker. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.BranchesSupport

open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec lastCode_singleton
  lastCode_mem stripLast_singleton)

def previousCode (heads : List Nat) : Nat :=
  cond (stripLast heads).isEmpty OmegaQuotient.unitTerm.code (lastCode (stripLast heads))

theorem previousCode_primrec : Primrec previousCode :=
  (NativeContext.SourceTrackingSequences.list_isEmpty_primrec.comp stripLast_primrec).cond
    (Primrec.const _) (lastCode_primrec.comp stripLast_primrec)

theorem previousCode_checked (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) : checkCode 0 (previousCode heads) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_exact heads).mp hh
  by_cases he : stripLast heads = []
  · simpa only [previousCode, he, List.isEmpty_nil, Bool.cond_true, checkCode_code] using
      OmegaQuotient.unitTerm_spec.1
  · have hp := hs.2.1.nodes _ (lastCode_mem _ he)
    simpa only [previousCode, List.isEmpty_eq_false_iff.mpr he, Bool.cond_false] using
      SourceTrackingRaw.Support.original_checked _ ((SourceTrackingRaw.Support.inputCheck_exact _).mp hp).1

theorem previousCode_value (heads : List Nat) :
    interpretation 0 (previousCode heads) =
      if stripLast heads = [] then 1 else interpretation 0 (lastCode (stripLast heads)) := by
  by_cases he : stripLast heads = []
  · simp only [previousCode, he, List.isEmpty_nil, Bool.cond_true, if_pos rfl,
      interpretation_code, OmegaQuotient.unitTerm_spec.2.2]
  · simp only [previousCode, List.isEmpty_eq_false_iff.mpr he, Bool.cond_false, if_neg he]

def lastEligibleCheck (heads : List Nat) : Bool :=
  SourceTrackingRaw.Support.inputCheck (lastCode heads) &&
    Theta.Normalization.lessRawCode 0 (previousCode heads) (lastCode heads)

theorem lastEligibleCheck_primrec : Primrec lastEligibleCheck :=
  Primrec.and.comp (SourceTrackingRaw.Support.inputCheck_primrec.comp lastCode_primrec)
    (Theta.Normalization.Effective.lessRawCode_primrec.comp
      ((Primrec.const 0).pair (previousCode_primrec.pair lastCode_primrec)))

/-- The concrete checker recognizes the genuine final epsilon strictly
above the actual preceding head, with literal original floor one. -/
theorem lastEligibleCheck_exact (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) : lastEligibleCheck heads = true ↔
    SourceTrackingRaw.Support.inputCheck (lastCode heads) = true ∧
      if stripLast heads = [] then 1 < interpretation 0 (lastCode heads)
      else interpretation 0 (lastCode (stripLast heads)) < interpretation 0 (lastCode heads) := by
  have hs := (SourceTrackingRaw.trackingCheck_exact heads).mp hh
  have hc := SourceTrackingRaw.Support.original_checked _ hs.2.2.1
  rw [lastEligibleCheck, Bool.and_eq_true,
    Theta.Normalization.lessRawCode_correct 0 _ _ (previousCode_checked heads hh) hc,
    previousCode_value heads]
  constructor
  · rintro ⟨hr, hv⟩
    refine ⟨hr, ?_⟩
    by_cases he : stripLast heads = []
    · simpa only [if_pos he] using hv
    · simpa only [if_neg he] using hv
  · rintro ⟨hr, hv⟩
    refine ⟨hr, ?_⟩
    by_cases he : stripLast heads = []
    · simpa only [if_pos he] using hv
    · simpa only [if_neg he] using hv

def appendCheck (factor : Nat) (heads : List Nat) : Bool :=
  lastEligibleCheck heads && Insertion.coverCheck (lastCode heads) factor

theorem appendCheck_primrec : Primrec (fun p : Insertion.Query => appendCheck p.1 p.2) :=
  Primrec.and.comp (lastEligibleCheck_primrec.comp Primrec.snd)
    (Primrec.comp Insertion.coverCheck_primrec
      ((lastCode_primrec.comp Primrec.snd).pair Primrec.fst))

theorem appendCheck_exact (factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) : appendCheck factor heads = true ↔
    SourceTrackingRaw.Support.inputCheck (lastCode heads) = true ∧
      (if stripLast heads = [] then 1 < interpretation 0 (lastCode heads)
       else interpretation 0 (lastCode (stripLast heads)) < interpretation 0 (lastCode heads)) ∧
      lowCheckCode 0 factor = true ∧
        interpretation 0 factor ≤ SourceTrackingRaw.Support.muValue (lastCode heads) := by
  rw [appendCheck, Bool.and_eq_true, lastEligibleCheck_exact heads hh, Insertion.coverCheck_exact]
  constructor
  · rintro ⟨⟨hr, hs⟩, hr', hf, hc⟩; exact ⟨hr, hs, hf, hc⟩
  · rintro ⟨hr, hs, hf, hc⟩; exact ⟨⟨hr, hs⟩, hr, hf, hc⟩

theorem reference_append_one (prefix : List Nat) (last : Nat)
    (hr : SourceTrackingRaw.Reference prefix)
    (hl : SourceTrackingRaw.Support.inputCheck last = true)
    (hs : prefix ≠ [] → interpretation 0 (lastCode prefix) < interpretation 0 last)
    (hc : prefix ≠ [] → interpretation 0 last ≤ SourceTrackingRaw.Support.muValue (lastCode prefix)) :
    SourceTrackingRaw.Reference (prefix ++ [last]) := by
  by_cases hn : prefix = []
  · simpa only [hn, List.nil_append] using SourceTrackingRaw.Reference.one last hl
  · exact InsertionFidelity.reference_append prefix last [] hr (.one last hl) hn (hs hn) (hc hn)

/-- The actual append guard derives the entire old headword as a real
original reference. The true original mu cover licenses its factor append. -/
theorem append_tracking (factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hfactor : 1 < interpretation 0 factor) (hc : appendCheck factor heads = true) :
    SourceTrackingRaw.trackingCheck (heads ++ [factor]) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_exact heads).mp hh
  have ha := (appendCheck_exact factor heads hh).mp hc
  obtain ⟨last, he, hr⟩ := stripLast_split heads hs.1
  have hlast : lastCode heads = last := by simp only [NativeContext.SourceTrackingSequences.lastCode, hr, Option.getD_some]
  have he' : heads = stripLast heads ++ [lastCode heads] := by simpa only [hlast] using he
  have href : SourceTrackingRaw.Reference heads := by
    rw [he']
    exact reference_append_one _ _ hs.2.1 ha.1
      (fun hn => by simpa only [if_neg hn] using ha.2.1)
      (fun hn => (by simpa only [if_neg hn] using hs.2.2.2.2.2 :
        1 < interpretation 0 (lastCode heads) ∧ interpretation 0 (lastCode heads) ≤
          SourceTrackingRaw.Support.muValue (lastCode (stripLast heads))).2)
  have ht : SourceTrackingRaw.trackingCheck [factor] = true :=
    SkTracking.Support.singleton_tracking factor ha.2.2.1 hm.1 hm.2.1 hfactor.le
  exact InsertionFidelity.tracking_append heads [factor] href hs.1 ht
    (by simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using hfactor)
    (by simpa only [Insertion.firstCode, List.head?_cons, Option.getD_some] using ha.2.2.2)
    (fun hn => False.elim (hn (stripLast_singleton factor)))

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.BranchesSupport
