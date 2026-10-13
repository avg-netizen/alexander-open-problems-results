import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingInsertion
import Alexander313.Wilken.PublicEpsilonNativeSkTrackingSupport

/-!
# Genuine raw-reference prefixes and tracking splices

The original raw reference dictionary supplies every prefix node, adjacent
strict comparison and actual mu cover. Literal list induction restricts a
reference to an original prefix and appends either a covered principal
singleton or a genuinely checked replacement tracker. A small singleton
need not itself be a tracker at the original base. No new source parser,
output tracking hypothesis for the combined word or assignment oracle.
All source candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionFidelitySupport

open PublicEpsilonUnboundedIota
open Hereditary.FinePredecessor (stripLast stripLast_split)
open SourceTrackingSequences (lastCode lastCode_mem lastCode_singleton
  stripLast_singleton stripLast_append_singleton)

theorem reference_tail (q a : Nat) (xs : List Nat)
    (h : SourceTrackingRaw.Reference q (a :: xs)) : SourceTrackingRaw.Reference q xs := by
  refine ⟨fun c hc => h.1 c (List.mem_cons_of_mem _ hc), ?_⟩
  cases xs with
  | nil => exact .nil
  | cons b xs =>
    have hs : SourceTrackingSequences.Reference q
        (SourceTrackingRaw.Support.rootCode q a :: SourceTrackingRaw.Support.rootCode q b ::
          SourceTrackingRaw.Support.rootWord q xs) := by
      simpa only [SourceTrackingRaw.Support.rootWord_cons] using h.2
    cases hs with
    | cons a b xs ha hab hc tail =>
      simpa only [SourceTrackingRaw.Support.rootWord_cons] using tail

theorem reference_prefix (q : Nat) (xs ys : List Nat)
    (h : SourceTrackingRaw.Reference q (xs ++ ys)) : SourceTrackingRaw.Reference q xs := by
  revert h
  induction xs with
  | nil => intro h; exact ⟨fun c hc => False.elim (List.not_mem_nil hc), .nil⟩
  | cons a xs ih =>
    intro h
    cases xs with
    | nil => exact SkTracking.Support.reference_one q a (h.nodes a (by simp))
    | cons b xs =>
      have ht := reference_tail q a ((b :: xs) ++ ys) h
      have hp := ih ht
      have hab : interpretation q a < interpretation q b :=
        (List.pairwise_cons.mp h.strict).1 _ (by simp)
      exact SkTracking.Support.reference_prepend q a b xs
        (h.nodes a (by simp)) (h.nodes b (by simp)) hab h.cover hp

theorem stripLast_append_nonempty (xs ys : List Nat) (hne : ys ≠ []) :
    stripLast (xs ++ ys) = xs ++ stripLast ys := by
  obtain ⟨d, he, hh⟩ := stripLast_split ys hne
  calc
    stripLast (xs ++ ys) = stripLast ((xs ++ stripLast ys) ++ [d]) := by
      rw [List.append_assoc, ← he]
    _ = xs ++ stripLast ys := stripLast_append_singleton _ _

theorem tracking_prefix_reference (q : Nat) (heads prefix : List Nat) (current : Nat)
    (after : List Nat) (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (he : heads = prefix ++ current :: after) : SourceTrackingRaw.Reference q prefix := by
  have hr := ((SourceTrackingRaw.trackingCheck_conditions q heads).mp hh).2.1
  rw [he, stripLast_append_nonempty prefix (current :: after) (List.cons_ne_nil _ _)] at hr
  exact reference_prefix q prefix _ hr

theorem tracking_first_ge_base (q a : Nat) (xs : List Nat)
    (ht : SourceTrackingRaw.trackingCheck q (a :: xs) = true) : base q ≤ interpretation q a := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q _).mp ht
  cases xs with
  | nil => simpa only [stripLast_singleton, if_pos rfl, lastCode_singleton] using hs.2.2.2.2.2
  | cons b xs =>
    have hp : a ∈ stripLast (a :: b :: xs) := by
      rw [SkTracking.Support.stripLast_cons_nonempty a _ (List.cons_ne_nil _ _)]
      exact List.mem_cons_self
    exact ((SourceTrackingRaw.Support.inputCheck_exact q a).mp (hs.2.1.nodes a hp)).2.1.le

theorem normal_tracking_first_ge_base (q a : Nat) (xs : List Nat)
    (ht : SourceTrackingSequences.trackingCheck q (a :: xs) = true) : base q ≤ interpretation q a := by
  have hs := (SourceTrackingSequences.trackingCheck_exact q _).mp ht
  cases xs with
  | nil => simpa only [stripLast_singleton, if_pos rfl, lastCode_singleton] using hs.2.2.2.2.2
  | cons b xs =>
    have hp : a ∈ stripLast (a :: b :: xs) := by
      rw [SkTracking.Support.stripLast_cons_nonempty a _ (List.cons_ne_nil _ _)]
      exact List.mem_cons_self
    exact (Mu.root_base_lt q a (hs.2.1.nodes a hp)).le

/-- Appending a covered principal to a genuine nonempty reference uses its
actual final cover. It does not require a separate singleton tracker. -/
theorem tracking_append_singleton (q : Nat) (prefix : List Nat) (d : Nat)
    (hr : SourceTrackingRaw.Reference q prefix) (hne : prefix ≠ [])
    (hl : lowCheckCode q d = true) (hp : 0 < interpretation q d)
    (hap : Ordinal.IsPrincipal (· + ·) (interpretation q d))
    (hd : 1 < interpretation q d)
    (hc : interpretation q d ≤ SourceTrackingRaw.Support.muValue q (lastCode prefix)) :
    SourceTrackingRaw.trackingCheck q (prefix ++ [d]) = true := by
  revert hr hne hc
  induction prefix with
  | nil => intro hr hne hc; exact False.elim (hne rfl)
  | cons a rest ih =>
    intro hr hne hc
    cases rest with
    | nil =>
      exact SkTracking.Support.pair_tracking q a d (hr.nodes a List.mem_cons_self) hl hp hap hd
        (by simpa only [lastCode_singleton] using hc)
    | cons b xs =>
      have htail := reference_tail q a (b :: xs) hr
      have hc' : interpretation q d ≤ SourceTrackingRaw.Support.muValue q (lastCode (b :: xs)) := by
        simpa only [SkTracking.Support.lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)] using hc
      have ht := ih htail (List.cons_ne_nil _ _) hc'
      have hb := (SourceTrackingRaw.Support.inputCheck_exact q b).mp
        (hr.nodes b (by simp))
      have hab : interpretation q a < interpretation q b :=
        (List.pairwise_cons.mp hr.strict).1 _ (by simp)
      exact SkTracking.Support.tracking_prepend q a b (xs ++ [d])
        (hr.nodes a List.mem_cons_self) (hr.nodes b (by simp)) hab hr.cover
        (Hereditary.EpsilonOffsets.epsilon_one_lt hb.2.2) ht

/-- The actual first-entry link attaches a checked replacement tracker to
an original nonempty reference prefix. Internal replacement mu conditions
come from its genuine tracker, not equal values alone. -/
theorem tracking_append_tracker (q : Nat) (prefix : List Nat) (first : Nat)
    (rest : List Nat) (hr : SourceTrackingRaw.Reference q prefix) (hne : prefix ≠ [])
    (ht : SourceTrackingRaw.trackingCheck q (first :: rest) = true)
    (hstrict : interpretation q (lastCode prefix) < interpretation q first)
    (hcover : interpretation q first ≤ SourceTrackingRaw.Support.muValue q (lastCode prefix)) :
    SourceTrackingRaw.trackingCheck q (prefix ++ first :: rest) = true := by
  revert hr hne hstrict hcover
  induction prefix with
  | nil => intro hr hne hstrict hcover; exact False.elim (hne rfl)
  | cons a tail ih =>
    intro hr hne hstrict hcover
    cases tail with
    | nil =>
      have hs := (SourceTrackingRaw.trackingCheck_conditions q _).mp ht
      have ha := hr.nodes a List.mem_cons_self
      cases rest with
      | nil =>
        exact SkTracking.Support.pair_tracking q a first ha
          (by simpa only [lastCode_singleton] using hs.2.2.1)
          (by simpa only [lastCode_singleton] using hs.2.2.2.1)
          (by simpa only [lastCode_singleton] using hs.2.2.2.2.1)
          ((Hereditary.EpsilonOffsets.epsilon_one_lt
            ((SourceTrackingRaw.Support.inputCheck_exact q a).mp ha).2.2).trans
              (by simpa only [lastCode_singleton] using hstrict))
          (by simpa only [lastCode_singleton] using hcover)
      | cons b xs =>
        have hf : SourceTrackingRaw.Support.inputCheck q first = true := hs.2.1.nodes first (by
          rw [SkTracking.Support.stripLast_cons_nonempty first _ (List.cons_ne_nil _ _)]
          exact List.mem_cons_self)
        exact SkTracking.Support.tracking_prepend q a first (b :: xs) ha hf
          (by simpa only [lastCode_singleton] using hstrict)
          (by simpa only [lastCode_singleton] using hcover)
          (Hereditary.EpsilonOffsets.epsilon_one_lt
            ((SourceTrackingRaw.Support.inputCheck_exact q first).mp hf).2.2) ht
    | cons b xs =>
      have htail := reference_tail q a (b :: xs) hr
      have hs' : interpretation q (lastCode (b :: xs)) < interpretation q first := by
        simpa only [SkTracking.Support.lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)] using hstrict
      have hc' : interpretation q first ≤ SourceTrackingRaw.Support.muValue q (lastCode (b :: xs)) := by
        simpa only [SkTracking.Support.lastCode_cons_nonempty a _ (List.cons_ne_nil _ _)] using hcover
      have ht' := ih htail (List.cons_ne_nil _ _) hs' hc'
      have hb := (SourceTrackingRaw.Support.inputCheck_exact q b).mp (hr.nodes b (by simp))
      have hab : interpretation q a < interpretation q b :=
        (List.pairwise_cons.mp hr.strict).1 _ (by simp)
      exact SkTracking.Support.tracking_prepend q a b (xs ++ first :: rest)
        (hr.nodes a List.mem_cons_self) (hr.nodes b (by simp)) hab hr.cover
        (Hereditary.EpsilonOffsets.epsilon_one_lt hb.2.2) ht'

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionFidelitySupport
