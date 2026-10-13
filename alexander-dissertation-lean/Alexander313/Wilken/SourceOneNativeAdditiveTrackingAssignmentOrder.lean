import Alexander313.Wilken.SourceOneNativeAdditiveTrackingIntervalOrder
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentValueInvariance

/-!
# Genuine complete original source-one assignment order

A proof-only induction on the actual right input's canonical MNF count
handles the independently executing complete Assignment. A multiplicative
right input uses the genuine selected-right comparison. A nonmultiplicative
right input derives its actual smaller Factor child: smaller left inputs
compare recursively with that child, equal values use actual Assignment
value invariance, and inputs above the child use the exhaustive actual
critical-interval branch proof. Thus no intermediate word, recursive
comparison, branch choice or lexical bound is supplied. Uncompiled source
candidates in the original check-zero dictionary; global source changes
and the evaluation inverse remain separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment.Order

open Alexander313.Wilken.MultiplicativeNormalForm

/-- Every pair of independently executing complete original Assignments
is strictly ordered by its genuine input ordinal comparison. -/
theorem execute_lex (left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute left) (hy : ys ∈ Assignment.execute right)
    (hlt : interpretation 0 left < interpretation 0 right) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  let P : Nat → Prop := fun n => ∀ right : Nat,
    (canonicalMNF (interpretation 0 right)).length = n → ∀ left : Nat, ∀ xs ys : List Nat,
      xs ∈ Assignment.execute left → ys ∈ Assignment.execute right →
        interpretation 0 left < interpretation 0 right →
          List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0))
  have hp : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro right hn left xs ys hx hy hlt
      rcases Assignment.execute_clauses right ys hy with ⟨hm, he⟩ |
        ⟨hm, prefix, factor, heads, hf, hh, ho⟩
      · exact CoverPrefix.execute_right_multiplicative_lex left right xs ys hx hy hm hlt
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, hcount⟩ := Factor.execute_spec right (prefix, factor) hf
        have hframe := FrameOrderSupport.execute_factor_frame_lex right prefix factor heads ys hf hh ho
        rcases lt_trichotomy (interpretation 0 left) (interpretation 0 prefix) with hl | he | hl
        · have hchild := ih (canonicalMNF (interpretation 0 prefix)).length (by simpa only [hn] using hcount)
            prefix rfl left xs heads hx hh hl
          exact List.lex_trans (fun hab hbc => hab.trans hbc) hchild hframe
        · rw [Assignment.ValueInvariance.execute_values_eq left prefix xs heads hx hh he]
          exact hframe
        · exact IntervalOrder.execute_interval_lex right prefix factor left xs ys hf hx hy hl hlt
  exact hp (canonicalMNF (interpretation 0 right)).length right rfl left xs ys hx hy hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment.Order
