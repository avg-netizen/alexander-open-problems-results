import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertionFidelity

/-!
# Actual final-epsilon append condition of Definition 3.20.2.1

The preceding head is the actual last proper-prefix code, or the real
original base when the headword is a singleton. Original admission proves
both operands of the written strict comparator. The final epsilon and mu
cover are recognized by the genuine raw dictionary. Literal reference
induction then makes the entire old headword a proper reference before
appending the actual M factor. No epsilon, adjacency or cover oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.BranchesSupport

open PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_split)
open SourceTrackingSequences (lastCode lastCode_primrec lastCode_mem lastCode_singleton)
open InsertionFidelitySupport

def previousCode (q : Nat) (heads : List Nat) : Nat :=
  cond (stripLast heads).isEmpty (SourceLocalization.baseRaw q) (lastCode (stripLast heads))

theorem previousCode_primrec : Primrec₂ previousCode := by
  have hp := stripLast_primrec.comp Primrec.snd
  exact ((SourceTrackingSequences.list_isEmpty_primrec.comp hp).cond
    (SourceLocalization.baseRaw_primrec.comp Primrec.fst) (lastCode_primrec.comp hp)).to₂

theorem previousCode_checked (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) : checkCode q (previousCode q heads) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q heads).mp hh
  by_cases he : stripLast heads = []
  · have hq := (HeightBoundary.input_spec q (lastCode heads) hs.2.2.1).2.1
    simpa only [previousCode, he, List.isEmpty_nil, Bool.cond_true] using
      ((Comparison.acceptedCode_exact q _).mp
        (SourceLocalization.node_accepted q _ (SourceLocalization.baseRaw_node q hq))).1
  · have hp := hs.2.1.nodes _ (lastCode_mem _ he)
    have hl := ((SourceTrackingRaw.Support.inputCheck_exact q _).mp hp).1
    simpa only [previousCode, List.isEmpty_eq_false_iff.mpr he, Bool.cond_false] using
      (Bool.and_eq_true.mp hl).1

theorem previousCode_value (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) :
    interpretation q (previousCode q heads) =
      if stripLast heads = [] then base q else interpretation q (lastCode (stripLast heads)) := by
  by_cases he : stripLast heads = []
  · have hs := (SourceTrackingRaw.trackingCheck_conditions q heads).mp hh
    have hq := (HeightBoundary.input_spec q (lastCode heads) hs.2.2.1).2.1
    simpa only [previousCode, he, List.isEmpty_nil, Bool.cond_true, if_pos rfl, SourceLocalization.value] using
      SourceLocalization.baseRaw_value q hq
  · simp only [previousCode, List.isEmpty_eq_false_iff.mpr he, Bool.cond_false, if_neg he]

def lastEligibleCheck (q : Nat) (heads : List Nat) : Bool :=
  SourceTrackingRaw.Support.inputCheck q (lastCode heads) &&
    Normalization.lessRawCode q (previousCode q heads) (lastCode heads)

theorem lastEligibleCheck_primrec : Primrec₂ lastEligibleCheck := by
  have hl := lastCode_primrec.comp Primrec.snd
  exact (Primrec.and.comp (SourceTrackingRaw.Support.inputCheck_primrec.comp Primrec.fst hl)
    (Normalization.Effective.lessRawCode_primrec.comp (Primrec.fst.pair (previousCode_primrec.pair hl)))).to₂

/-- This is exactly the printed final epsilon above its preceding head,
including alpha_0=the original base for a one-entry headword. -/
theorem lastEligibleCheck_exact (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) : lastEligibleCheck q heads = true ↔
    SourceTrackingRaw.Support.inputCheck q (lastCode heads) = true ∧
      if stripLast heads = [] then base q < interpretation q (lastCode heads)
      else interpretation q (lastCode (stripLast heads)) < interpretation q (lastCode heads) := by
  rw [lastEligibleCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hr, hl⟩
    refine ⟨hr, ?_⟩
    have hv := ((Normalization.lessRawCode_exact q _ _).mp hl).2.2
    rw [previousCode_value q heads hh] at hv
    by_cases he : stripLast heads = []
    · simpa only [if_pos he] using hv
    · simpa only [if_neg he] using hv
  · rintro ⟨hr, hv⟩
    refine ⟨hr, (Normalization.lessRawCode_exact q _ _).mpr ⟨previousCode_checked q heads hh,
      (Bool.and_eq_true.mp ((SourceTrackingRaw.Support.inputCheck_exact q _).mp hr).1).1, ?_⟩⟩
    rw [previousCode_value q heads hh]
    by_cases he : stripLast heads = []
    · simpa only [if_pos he] using hv
    · simpa only [if_neg he] using hv

def appendCheck (q factor : Nat) (heads : List Nat) : Bool :=
  lastEligibleCheck q heads && Insertion.coverCheck q (lastCode heads) factor

theorem appendCheck_primrec : Primrec (fun p : (Nat × Nat) × List Nat =>
    appendCheck p.1.1 p.1.2 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hf := Primrec.snd.comp Primrec.fst
  have hl := lastCode_primrec.comp Primrec.snd
  exact Primrec.and.comp (Primrec.comp lastEligibleCheck_primrec (hq.pair Primrec.snd))
    (Insertion.coverCheck_primrec.comp ((hq.pair hl).pair hf))

theorem appendCheck_exact (q factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) : appendCheck q factor heads = true ↔
    SourceTrackingRaw.Support.inputCheck q (lastCode heads) = true ∧
      (if stripLast heads = [] then base q < interpretation q (lastCode heads)
       else interpretation q (lastCode (stripLast heads)) < interpretation q (lastCode heads)) ∧
      lowCheckCode q factor = true ∧
        interpretation q factor ≤ SourceTrackingRaw.Support.muValue q (lastCode heads) := by
  rw [appendCheck, Bool.and_eq_true, lastEligibleCheck_exact q heads hh, Insertion.coverCheck_exact]
  constructor
  · rintro ⟨⟨hr, hs⟩, hr', hf, hc⟩; exact ⟨hr, hs, hf, hc⟩
  · rintro ⟨hr, hs, hf, hc⟩; exact ⟨⟨hr, hs⟩, hr, hf, hc⟩

theorem reference_append_one (q : Nat) (prefix : List Nat) (last : Nat)
    (hr : SourceTrackingRaw.Reference q prefix)
    (hl : SourceTrackingRaw.Support.inputCheck q last = true)
    (hs : prefix ≠ [] → interpretation q (lastCode prefix) < interpretation q last)
    (hc : prefix ≠ [] → interpretation q last ≤ SourceTrackingRaw.Support.muValue q (lastCode prefix)) :
    SourceTrackingRaw.Reference q (prefix ++ [last]) := by
  revert hr hs hc
  induction prefix with
  | nil => intro hr hs hc; exact SkTracking.Support.reference_one q last hl
  | cons a rest ih =>
    intro hr hs hc
    cases rest with
    | nil =>
      exact SkTracking.Support.reference_prepend q a last [] (hr.nodes a List.mem_cons_self) hl
        (by simpa only [lastCode_singleton] using hs (List.cons_ne_nil _ _))
        (by simpa only [lastCode_singleton] using hc (List.cons_ne_nil _ _))
        (SkTracking.Support.reference_one q last hl)
    | cons b xs =>
      have ht := ih (reference_tail q a _ hr)
        (fun _ => by simpa only [SkTracking.Support.lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)]
          using hs (List.cons_ne_nil _ _))
        (fun _ => by simpa only [SkTracking.Support.lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)]
          using hc (List.cons_ne_nil _ _))
      exact SkTracking.Support.reference_prepend q a b (xs ++ [last])
        (hr.nodes a List.mem_cons_self) (hr.nodes b (by simp))
        ((List.pairwise_cons.mp hr.strict).1 _ (by simp)) hr.cover ht

/-- The actual final-epsilon condition turns the entire old checked word
into a genuine reference. The real computed mu cover then licenses the
literal factor append, exactly as in printed branch 2.1. -/
theorem append_tracking (q factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hfactor : 1 < interpretation q factor) (hc : appendCheck q factor heads = true) :
    SourceTrackingRaw.trackingCheck q (heads ++ [factor]) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q heads).mp hh
  have ha := (appendCheck_exact q factor heads hh).mp hc
  obtain ⟨last, he, hr⟩ := stripLast_split heads hs.1
  have hlast : lastCode heads = last := by simp only [SourceTrackingSequences.lastCode, hr, Option.getD_some]
  have he' : heads = stripLast heads ++ [lastCode heads] := by simpa only [hlast] using he
  have href : SourceTrackingRaw.Reference q heads := by
    rw [he']
    exact reference_append_one q _ _ hs.2.1 ha.1
      (fun hn => by simpa only [if_neg hn] using ha.2.1)
      (fun hn => (by simpa only [if_neg hn] using hs.2.2.2.2.2 :
        1 < interpretation q (lastCode heads) ∧ interpretation q (lastCode heads) ≤
          SourceTrackingRaw.Support.muValue q (lastCode (stripLast heads))).2)
  exact tracking_append_singleton q heads factor href hs.1 ha.2.2.1 hm.1 hm.2.1 hfactor ha.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.BranchesSupport
