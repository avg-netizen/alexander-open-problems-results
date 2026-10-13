import Alexander313.Wilken.SourceOneNativeSkSourceWord
import Alexander313.Wilken.SourceOneNativeTrackingRaw

/-!
# Original source-one tracking callers for executing sk entries

Real source-zero LOW returns and derived original HIGH representatives
identify every prefix epsilon and its actual SAME-source mu. Pure list
operations construct the genuine original Reference and Tracking callers.
No Native base-one parser, endpoint, spelling or mu oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkTracking.Support

open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton stripLast_singleton
  lastCode_append_singleton stripLast_append_singleton)

abbrev Word := SkSourceWord.Support.Word

def EntryMatches (entry : NativeContext.PublicEpsilonUnboundedIota.Context) (d : Nat) : Prop :=
  Theta.acceptedLowCode 0 d = true ∧
    interpretation 0 d = NativeContext.interpretation entry.1 entry.2

theorem flatWord_relation (word : Word)
    (hl : ∀ entry ∈ word, NativeContext.lowCheckCode entry.1 entry.2 = true)
    (hb : ∀ entry ∈ word, NativeContext.interpretation entry.1 entry.2 < finiteBase 1) :
    List.Forall₂ EntryMatches word (SkSourceWord.Support.flatWord word) := by
  induction word with
  | nil => exact .nil
  | cons entry rest ih =>
    exact .cons (SkSourcePathSupport.entryCode_spec entry.1 entry.2
      (hl entry List.mem_cons_self) (hb entry List.mem_cons_self))
      (ih (fun e he => hl e (List.mem_cons_of_mem _ he))
        (fun e he => hb e (List.mem_cons_of_mem _ he)))

theorem first_flatWord_relation (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) (hh : out.1 = true)
    (word : Word) (hw : word ∈ NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
      ((alphaCode root, out.2), cutoff)) :
    List.Forall₂ EntryMatches word (SkSourceWord.Support.flatWord word) :=
  flatWord_relation word
    (fun e he => ((NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_spec
      _ _ _ word hw).2.2.2 e he).1)
    (SkSourcePathSupport.first_loop_entry_bound root cutoff out ho hh word hw)

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

theorem original_root (root : Nat) (ha : Mu.inputCheck root = true) :
    SourceTrackingRaw.Support.inputCheck root = true ∧
      SourceTrackingRaw.Support.muValue root = Mu.sourceValue root := by
  have hr := (SourceTrackingRaw.Support.inputCheck_exact root).mpr
    ⟨root_low root ha, EpsilonOffsets.epsilon_one_lt (root_epsilon root ha), root_epsilon root ha⟩
  exact ⟨hr, SourceTrackingRaw.Support.muValue_eq root root hr ha rfl⟩

/-- Real original-source root and emitted entry VALUE fidelity derive
the actual raw epsilon and original mu callers of the returned spelling. -/
theorem entry_root (root q current d : Nat)
    (ha : Mu.inputCheck root = true)
    (hv : interpretation 0 root = NativeContext.interpretation q current)
    (hm : Mu.sourceValue root = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current)
    (hd : EntryMatches (q, current) d) :
    SourceTrackingRaw.Support.inputCheck d = true ∧
      SourceTrackingRaw.Support.muValue d =
        NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current := by
  have he : interpretation 0 d = interpretation 0 root := hd.2.trans hv.symm
  have hr := (SourceTrackingRaw.Support.inputCheck_exact d).mpr
    ⟨((Theta.acceptedLowCode_iff 0 d).mp hd.1).1,
      by rw [he]; exact EpsilonOffsets.epsilon_one_lt (root_epsilon root ha),
      by rw [he]; exact root_epsilon root ha⟩
  exact ⟨hr, (SourceTrackingRaw.Support.muValue_eq d root hr ha he).trans hm⟩

theorem singleton_tracking (a : Nat) (hl : lowCheckCode 0 a = true)
    (hp : 0 < interpretation 0 a)
    (hap : Ordinal.IsPrincipal (· + ·) (interpretation 0 a))
    (hb : 1 ≤ interpretation 0 a) : SourceTrackingRaw.trackingCheck [a] = true := by
  apply (SourceTrackingRaw.trackingCheck_exact [a]).mpr
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stripLast_singleton]; exact .nil
  · simpa only [lastCode_singleton] using hl
  · simpa only [lastCode_singleton] using hp
  · simpa only [lastCode_singleton] using hap
  · simpa only [stripLast_singleton, if_pos rfl, lastCode_singleton] using hb

theorem pair_tracking (a b : Nat)
    (ha : SourceTrackingRaw.Support.inputCheck a = true)
    (hl : lowCheckCode 0 b = true) (hp : 0 < interpretation 0 b)
    (hap : Ordinal.IsPrincipal (· + ·) (interpretation 0 b))
    (hb : 1 < interpretation 0 b)
    (hc : interpretation 0 b ≤ SourceTrackingRaw.Support.muValue a) :
    SourceTrackingRaw.trackingCheck [a, b] = true := by
  apply (SourceTrackingRaw.trackingCheck_exact [a, b]).mpr
  have hprefix : stripLast [a, b] = [a] := stripLast_append_singleton [a] b
  have hlast : lastCode [a, b] = b := lastCode_append_singleton [a] b
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprefix]; exact .one a ha
  · rw [hlast]; exact hl
  · rw [hlast]; exact hp
  · rw [hlast]; exact hap
  · rw [hprefix, if_neg (List.cons_ne_nil _ _), hlast, lastCode_singleton]
    exact ⟨hb, hc⟩

theorem tracking_prepend (a b : Nat) (xs : List Nat)
    (ha : SourceTrackingRaw.Support.inputCheck a = true)
    (hb : SourceTrackingRaw.Support.inputCheck b = true)
    (hab : interpretation 0 a < interpretation 0 b)
    (hc : interpretation 0 b ≤ SourceTrackingRaw.Support.muValue a)
    (hbpos : 1 < interpretation 0 b)
    (ht : SourceTrackingRaw.trackingCheck (b :: xs) = true) :
    SourceTrackingRaw.trackingCheck (a :: b :: xs) = true := by
  have hs := (SourceTrackingRaw.trackingCheck_exact (b :: xs)).mp ht
  cases xs with
  | nil =>
    exact pair_tracking a b ha
      (by simpa only [lastCode_singleton] using hs.2.2.1)
      (by simpa only [lastCode_singleton] using hs.2.2.2.1)
      (by simpa only [lastCode_singleton] using hs.2.2.2.2.1) hbpos hc
  | cons c cs =>
    have hn : c :: cs ≠ [] := List.cons_ne_nil _ _
    have hprefix : stripLast (b :: c :: cs) = b :: stripLast (c :: cs) :=
      stripLast_cons_nonempty b _ hn
    have hpne : stripLast (b :: c :: cs) ≠ [] := by rw [hprefix]; exact List.cons_ne_nil _ _
    have hnew : stripLast (a :: b :: c :: cs) = a :: stripLast (b :: c :: cs) :=
      stripLast_cons_nonempty a _ (List.cons_ne_nil _ _)
    have hnewne : stripLast (a :: b :: c :: cs) ≠ [] := by rw [hnew]; exact List.cons_ne_nil _ _
    have hlast := lastCode_cons_nonempty a (b :: c :: cs) (List.cons_ne_nil _ _)
    apply (SourceTrackingRaw.trackingCheck_exact _).mpr
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnew, hprefix]
      exact .cons a b _ ha hab hc (by rw [← hprefix]; exact hs.2.1)
    · rw [hlast]; exact hs.2.2.1
    · rw [hlast]; exact hs.2.2.2.1
    · rw [hlast]; exact hs.2.2.2.2.1
    · rw [if_neg hnewne, hlast, hnew, lastCode_cons_nonempty a _ hpne]
      simpa only [if_neg hpne] using hs.2.2.2.2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkTracking.Support
