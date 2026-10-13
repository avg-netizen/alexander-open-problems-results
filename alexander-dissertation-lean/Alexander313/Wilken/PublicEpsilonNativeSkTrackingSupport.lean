import Alexander313.Wilken.PublicEpsilonNativeSkSourceWord
import Alexander313.Wilken.PublicEpsilonNativeTrackingRaw

/-!
# Actual original-source tracking operations for returned sk entries

The RAW recognizer retains every returned code. Genuine original HIGH
representatives identify the real SAME-source mu of those spellings.
Literal prefix/last operations then construct tracking singletons, pairs
and prepended covered epsilon entries. These are structural consequences
of the actual original checkers, not a supplied tracking assignment.
No Par, endpoint or spelling equality is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support

open Hereditary.FinePredecessor (stripLast stripLast_split)
open SourceTrackingSequences (lastCode lastCode_singleton stripLast_singleton
  lastCode_append_singleton stripLast_append_singleton)
open SkSourceWord.Support (EntryMatches)

theorem stripLast_cons_nonempty (a : Nat) (xs : List Nat) (hne : xs ≠ []) :
    stripLast (a :: xs) = a :: stripLast xs := by
  obtain ⟨d, he, hh⟩ := stripLast_split xs hne
  calc
    stripLast (a :: xs) = stripLast ((a :: stripLast xs) ++ [d]) := by
      rw [← List.cons_append, ← he]
    _ = a :: stripLast xs := stripLast_append_singleton _ _

theorem lastCode_cons_nonempty (a : Nat) (xs : List Nat) (hne : xs ≠ []) :
    lastCode (a :: xs) = lastCode xs := by
  obtain ⟨d, he, hh⟩ := stripLast_split xs hne
  calc
    lastCode (a :: xs) = d := by rw [he, List.cons_append, lastCode_append_singleton]
    _ = lastCode xs := by simp only [lastCode, hh, Option.getD_some]

/-- A returned LOW spelling of a genuine original HIGH root derives its
RAW epsilon caller and its actual original mu value. -/
theorem entry_root (q root r current d : Nat)
    (ha : Mu.inputCheck q root = true)
    (hv : interpretation q root = interpretation r current)
    (hm : Mu.sourceValue q root = Mu.sourceValue r current)
    (hd : EntryMatches q (r, current) d) :
    SourceTrackingRaw.Support.inputCheck q d = true ∧
      SourceTrackingRaw.Support.muValue q d = Mu.sourceValue r current := by
  have hvalue : interpretation q d = interpretation q root := hd.2.2.trans hv.symm
  have hraw : SourceTrackingRaw.Support.inputCheck q d = true :=
    (SourceTrackingRaw.Support.inputCheck_exact q d).mpr
      ⟨hd.1, by rw [hvalue]; exact Mu.root_base_lt q root ha,
        by rw [hvalue]; exact RootLowCollapse.root_epsilon q root ha⟩
  exact ⟨hraw, (SourceTrackingRaw.Support.muValue_eq q d root hraw ha hvalue).trans hm⟩

theorem reference_one (q a : Nat) (ha : SourceTrackingRaw.Support.inputCheck q a = true) :
    SourceTrackingRaw.Reference q [a] := by
  refine ⟨fun c hc => by rw [List.mem_singleton.mp hc]; exact ha, ?_⟩
  simpa only [SourceTrackingRaw.Support.rootWord_cons, SourceTrackingRaw.Support.rootWord_nil]
    using (SourceTrackingSequences.Reference.one (SourceTrackingRaw.Support.rootCode q a)
      (SourceTrackingRaw.Support.rootCode_spec q a ha).2.1)

theorem reference_prepend (q a b : Nat) (xs : List Nat)
    (ha : SourceTrackingRaw.Support.inputCheck q a = true)
    (hb : SourceTrackingRaw.Support.inputCheck q b = true)
    (hab : interpretation q a < interpretation q b)
    (hcover : interpretation q b ≤ SourceTrackingRaw.Support.muValue q a)
    (ht : SourceTrackingRaw.Reference q (b :: xs)) :
    SourceTrackingRaw.Reference q (a :: b :: xs) := by
  have hsa := SourceTrackingRaw.Support.rootCode_spec q a ha
  have hsb := SourceTrackingRaw.Support.rootCode_spec q b hb
  refine ⟨?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · exact ht.1 c hc
  · rw [SourceTrackingRaw.Support.rootWord_cons, SourceTrackingRaw.Support.rootWord_cons]
    exact .cons _ _ _ hsa.2.1
      (by rw [hsa.2.2, hsb.2.2]; exact hab)
      (by rw [hsb.2.2]; exact hcover)
      (by simpa only [SourceTrackingRaw.Support.rootWord_cons] using ht.2)

theorem singleton_tracking (q a : Nat) (hl : lowCheckCode q a = true)
    (hp : 0 < interpretation q a)
    (hap : Ordinal.IsPrincipal (· + ·) (interpretation q a))
    (hb : base q ≤ interpretation q a) : SourceTrackingRaw.trackingCheck q [a] = true := by
  apply (SourceTrackingRaw.trackingCheck_conditions q [a]).mpr
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun c hc => False.elim (List.not_mem_nil hc), .nil⟩
  · simpa only [lastCode_singleton] using hl
  · simpa only [lastCode_singleton] using hp
  · simpa only [lastCode_singleton] using hap
  · simpa only [stripLast_singleton, if_pos rfl, lastCode_singleton] using hb

theorem pair_tracking (q a b : Nat)
    (ha : SourceTrackingRaw.Support.inputCheck q a = true)
    (hl : lowCheckCode q b = true) (hp : 0 < interpretation q b)
    (hap : Ordinal.IsPrincipal (· + ·) (interpretation q b))
    (hb : 1 < interpretation q b)
    (hcover : interpretation q b ≤ SourceTrackingRaw.Support.muValue q a) :
    SourceTrackingRaw.trackingCheck q [a, b] = true := by
  apply (SourceTrackingRaw.trackingCheck_conditions q [a, b]).mpr
  have hprefix : stripLast [a, b] = [a] := stripLast_append_singleton [a] b
  have hlast : lastCode [a, b] = b := lastCode_append_singleton [a] b
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprefix]; exact reference_one q a ha
  · rw [hlast]; exact hl
  · rw [hlast]; exact hp
  · rw [hlast]; exact hap
  · rw [hprefix, if_neg (List.cons_ne_nil _ _), hlast, lastCode_singleton]
    exact ⟨hb, hcover⟩

/-- A genuinely covered increasing RAW epsilon can be prepended to the
actual tracking word. Its last original principal spelling is unchanged. -/
theorem tracking_prepend (q a b : Nat) (xs : List Nat)
    (ha : SourceTrackingRaw.Support.inputCheck q a = true)
    (hb : SourceTrackingRaw.Support.inputCheck q b = true)
    (hab : interpretation q a < interpretation q b)
    (hcover : interpretation q b ≤ SourceTrackingRaw.Support.muValue q a)
    (hbpos : 1 < interpretation q b)
    (ht : SourceTrackingRaw.trackingCheck q (b :: xs) = true) :
    SourceTrackingRaw.trackingCheck q (a :: b :: xs) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q (b :: xs)).mp ht
  cases xs with
  | nil =>
    exact pair_tracking q a b ha
      (by simpa only [lastCode_singleton] using hs.2.2.1)
      (by simpa only [lastCode_singleton] using hs.2.2.2.1)
      (by simpa only [lastCode_singleton] using hs.2.2.2.2.1) hbpos hcover
  | cons c cs =>
    have hn : c :: cs ≠ [] := List.cons_ne_nil _ _
    have hprefix : stripLast (b :: c :: cs) = b :: stripLast (c :: cs) :=
      stripLast_cons_nonempty b _ hn
    have hpne : stripLast (b :: c :: cs) ≠ [] := by rw [hprefix]; exact List.cons_ne_nil _ _
    have hnew : stripLast (a :: b :: c :: cs) = a :: stripLast (b :: c :: cs) :=
      stripLast_cons_nonempty a _ (List.cons_ne_nil _ _)
    have hnewne : stripLast (a :: b :: c :: cs) ≠ [] := by rw [hnew]; exact List.cons_ne_nil _ _
    have hlast := lastCode_cons_nonempty a (b :: c :: cs) (List.cons_ne_nil _ _)
    apply (SourceTrackingRaw.trackingCheck_conditions q _).mpr
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnew, hprefix]
      exact reference_prepend q a b _ ha hb hab hcover (by rw [← hprefix]; exact hs.2.1)
    · rw [hlast]; exact hs.2.2.1
    · rw [hlast]; exact hs.2.2.2.1
    · rw [hlast]; exact hs.2.2.2.2.1
    · rw [if_neg hnewne, hlast, hnew, lastCode_cons_nonempty a _ hpne]
      simpa only [if_neg hpne] using hs.2.2.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support
