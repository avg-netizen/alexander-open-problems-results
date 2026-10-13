import Alexander313.Wilken.HereditaryEvaluationInitialHeightCoveredMonotonicity
import Alexander313.Wilken.HereditaryEvaluationBlocks

/-!
# The genuine public component reference bounds its actual written length

An independent public Tracking word has a proper Reference before its
last input. The actual first original height therefore bounds the entire
word by one more. This applies to every genuinely executed proper component
because the complete component graph derives its public Tracking predicate.
The actual first code is computed from the word. Bounding that first height
by the common initial height, the whole epsilon Reference certificate and
the possible final-factor append remain separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponentReferenceLength

open EvaluationInitialReferenceHeight
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceAdditiveTracking.Insertion (firstCode)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)

theorem tracking_length_le (first : Nat) (rest : List Nat)
    (ht : PublicTrackingSequences.Tracking (first :: rest)) :
    (first :: rest).length ≤ initialHeight first + 1 := by
  cases rest with
  | nil => simp only [List.length_singleton]; omega
  | cons next rest =>
    have hp := ht.2.2.1
    rw [stripLast_cons_nonempty first (next :: rest) (List.cons_ne_nil _ _)] at hp
    have hb := reference_length_le first (stripLast (next :: rest)) hp
    have hlength : (stripLast (next :: rest)).length = rest.length := by
      simp only [stripLast, List.length_reverse, List.length_tail, List.length_cons,
        Nat.add_sub_cancel]
    simp only [List.length_cons, hlength] at hb ⊢
    omega

theorem tracking_length_le_firstCode (word : List Nat)
    (ht : PublicTrackingSequences.Tracking word) :
    word.length ≤ initialHeight (firstCode word) + 1 := by
  cases word with
  | nil => exact False.elim (ht.1 rfl)
  | cons first rest =>
    simpa only [firstCode, List.head?_cons, Option.getD_some] using tracking_length_le first rest ht

/-- The actual component graph supplies its independent certificate;
no supplied component length or first-height bound is required. -/
theorem assigned_lengths {gamma : Nat} {inputs : List Nat} {words : List EvaluationBlocks.Block}
    (ha : EvaluationBlocks.Assigned gamma inputs words) :
    ∀ word ∈ words, word.length ≤ initialHeight (firstCode word) + 1 :=
  fun word hw => tracking_length_le_firstCode word (EvaluationBlocks.assigned_tracking ha word hw)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationComponentReferenceLength
