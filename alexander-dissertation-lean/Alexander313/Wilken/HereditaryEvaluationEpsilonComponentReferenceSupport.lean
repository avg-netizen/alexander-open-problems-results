import Alexander313.Wilken.HereditaryEvaluationComponentReferenceLength

/-!
# A genuinely strict epsilon component retains its whole reference

Independent public Tracking supplies the actual proper prefix and final
mu cover. If the actual final entry is independently proper and the whole
word is strictly increasing, these facts append the final entry to the
reference. Consequently its complete length has no extra final-entry cost.
The operational adapters must derive strictness and final admission from
the real epsilon assignment. Common height and final append are separate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEpsilonComponentReferenceSupport

open PublicTrackingSequences
open EvaluationInitialReferenceHeight
open Hereditary.FinePredecessor (stripLast stripLast_split)
open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton
  lastCode_singleton lastCode_mem)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (lastCode_cons_nonempty)
open NativeContext.SourceAdditiveTracking.Insertion (firstCode)

theorem reference_append_one (prefix : List Nat) (last : Nat)
    (hr : Reference prefix) (hlast : MuPublicDictionary.Support.inputCheck last = true)
    (hlt : ∀ a ∈ prefix, unionInterpretation a < unionInterpretation last)
    (hcover : if prefix = [] then True else
      unionInterpretation last ≤ SkPublicRecurrence.muValue (lastCode prefix)) :
    Reference (prefix ++ [last]) := by
  revert hlt hcover
  induction hr with
  | nil => intro hlt hcover; exact .one last hlast
  | one a ha =>
    intro hlt hcover
    have hc : unionInterpretation last ≤ SkPublicRecurrence.muValue a := by
      simpa only [if_neg (List.cons_ne_nil _ _), lastCode_singleton] using hcover
    exact .cons a last [] ha (hlt a List.mem_cons_self) hc (.one last hlast)
  | cons a b xs ha hab hc ht ih =>
    intro hlt hcover
    have htail : if b :: xs = [] then True else
        unionInterpretation last ≤ SkPublicRecurrence.muValue (lastCode (b :: xs)) := by
      simpa only [if_neg (List.cons_ne_nil _ _),
        lastCode_cons_nonempty a (b :: xs) (List.cons_ne_nil _ _)] using hcover
    exact .cons a b (xs ++ [last]) ha hab hc
      (ih (fun c hmem => hlt c (List.mem_cons_of_mem _ hmem)) htail)

theorem tracking_whole_reference (word : List Nat) (ht : Tracking word)
    (hs : (word.map unionInterpretation).Pairwise (· < ·))
    (hlast : MuPublicDictionary.Support.inputCheck (lastCode word) = true) :
    Reference word := by
  obtain ⟨last, he, hmem⟩ := stripLast_split word ht.1
  have hl : lastCode word = last := by rw [he, lastCode_append_singleton]
  have hstrict := hs
  rw [he, List.map_append, List.map_singleton] at hstrict
  have hlt : ∀ a ∈ stripLast word, unionInterpretation a < unionInterpretation last := by
    intro a ha
    exact (List.pairwise_append.mp hstrict).2.2 _
      (List.mem_map.mpr ⟨a, ha, rfl⟩) _ List.mem_cons_self
  have hc : if stripLast word = [] then True else
      unionInterpretation last ≤ SkPublicRecurrence.muValue (lastCode (stripLast word)) := by
    by_cases hn : stripLast word = []
    · simp only [if_pos hn]
    · have hb := ht.2.2.2.2.2
      rw [if_neg hn, hl] at hb
      rw [if_neg hn]
      exact hb.2
  have hp := reference_append_one (stripLast word) last ht.2.2.1
    (by simpa only [hl] using hlast) hlt hc
  rw [he]
  exact hp

theorem whole_reference_length (word : List Nat) (ht : Tracking word)
    (hs : (word.map unionInterpretation).Pairwise (· < ·))
    (hlast : MuPublicDictionary.Support.inputCheck (lastCode word) = true) :
    word.length ≤ initialHeight (firstCode word) := by
  have hr := tracking_whole_reference word ht hs hlast
  cases word with
  | nil => exact False.elim (ht.1 rfl)
  | cons first rest =>
    simpa only [firstCode, List.head?_cons, Option.getD_some] using
      reference_length_le first rest hr

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationEpsilonComponentReferenceSupport
