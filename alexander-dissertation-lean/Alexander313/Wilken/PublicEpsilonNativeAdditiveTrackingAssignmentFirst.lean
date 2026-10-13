import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFrameOrderSupport

/-!
# Actual whole assignment FIRST is above its genuine epsilon base

A RAW tracker beginning at its own base cannot have a second entry: the
first proper entry would have to be a strict epsilon above that same base.
The multiplicative leaf retains the actual input as LAST, the direct leaf
is its literal singleton, and every real factor frame strictly increases
the complete child word. A child FIRST at least the base cannot be strictly
below a singleton at the base. Thus full execution above the base derives
strict FIRST, without general inter-input assignment order or composition.
Only genuine native epsilon contexts are used. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentFirst

open PublicEpsilonUnboundedIota
open SourceTrackingSequences (lastCode lastCode_singleton)
open Insertion (firstCode)
open Hereditary.FinePredecessor (stripLast)
open PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)

theorem tracking_first_eq_base_singleton (q first : Nat) (rest : List Nat)
    (ht : SourceTrackingRaw.trackingCheck q (first :: rest) = true)
    (he : interpretation q first = base q) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons next rest =>
    have hs := (SourceTrackingRaw.trackingCheck_conditions q (first :: next :: rest)).mp ht
    have hm : first ∈ stripLast (first :: next :: rest) := by
      rw [stripLast_cons_nonempty first (next :: rest) (List.cons_ne_nil _ _)]
      exact List.mem_cons_self
    have hb := ((SourceTrackingRaw.Support.inputCheck_exact q first).mp (hs.2.1.nodes first hm)).2.1
    rw [he] at hb
    exact False.elim (lt_irrefl _ hb)

private theorem not_lex_floor_singleton (floor first : Ordinal.{0}) (rest : List Ordinal.{0})
    (hf : floor ≤ first) : ¬List.Lex (· < ·) (first :: rest) [floor] := by
  intro hl
  cases hl with
  | rel ht => exact ht.not_ge hf
  | cons ht => cases ht

/-- Every real source-clause alternative supplies the actual strict
FIRST bound. There is no lexical comparison with another input. -/
theorem execute_first_gt_base (q input first : Nat) (rest : List Nat)
    (ho : first :: rest ∈ Assignment.execute q input)
    (hi : base q < interpretation q input) : base q < interpretation q first := by
  have ht := Assignment.execute_tracking q input (first :: rest) ho
  have hfloor := InsertionFidelitySupport.tracking_first_ge_base q first rest ht
  by_contra hn
  have he : interpretation q first = base q := le_antisymm (le_of_not_gt hn) hfloor
  have hrest := tracking_first_eq_base_singleton q first rest ht he
  have hd := (Assignment.execute_spec q input (first :: rest) ho).2.2
  rcases Assignment.derivation_flags q input (first :: rest) hd with ⟨hm, hw⟩ |
    ⟨hm, hs, hw⟩ | ⟨hm, hs, prefix, factor, heads, hf, hh, hb⟩
  · have hlast : interpretation q input = interpretation q first := by
      calc
        interpretation q input = interpretation q (lastCode (SourceMultiplicativeTracking.rawWord q input)) := by
          rw [SourceMultiplicativeTracking.rawWord_last]
        _ = interpretation q (lastCode (first :: rest)) := congrArg (fun xs => interpretation q (lastCode xs)) hw.symm
        _ = interpretation q first := by rw [hrest, lastCode_singleton]
    exact hi.ne ((hlast.trans he).symm)
  · have hfirst : first = input := (List.cons.inj hw).1
    have hinput : interpretation q input = base q := (congrArg (interpretation q) hfirst).symm.trans he
    exact hi.ne hinput.symm
  · have hchild : heads ∈ Assignment.execute q prefix := (Assignment.execute_iff_derivation q prefix heads).mpr hh
    have hlex := FrameOrderSupport.execute_frame_lex q input prefix factor heads (first :: rest) hf hchild hb
    obtain ⟨head, tail, hheads⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty q prefix heads hchild)
    have hchildFloor := InsertionFidelitySupport.tracking_first_ge_base q head tail
      (by simpa only [hheads] using Assignment.execute_tracking q prefix heads hchild)
    have hlex' : List.Lex (· < ·) (interpretation q head :: tail.map (interpretation q)) [base q] := by
      simpa only [hheads, hrest, List.map_cons, List.map_nil, he] using hlex
    exact not_lex_floor_singleton (base q) (interpretation q head) _ hchildFloor hlex'

theorem execute_firstCode_gt_base (q input : Nat) (out : List Nat)
    (ho : out ∈ Assignment.execute q input)
    (hi : base q < interpretation q input) :
    base q < interpretation q (firstCode out) := by
  cases out with
  | nil => exact False.elim (Assignment.execute_nonempty q input [] ho rfl)
  | cons first rest =>
    simpa only [firstCode, List.head?_cons, Option.getD_some] using
      execute_first_gt_base q input first rest ho hi

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.AssignmentFirst
