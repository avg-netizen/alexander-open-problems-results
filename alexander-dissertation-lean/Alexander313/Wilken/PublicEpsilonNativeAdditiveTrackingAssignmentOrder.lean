import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFullIntervalOrder
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentValueInvariance

/-!
# Genuine complete native assignment order

Proof-only induction on the actual right input's canonical MNF count uses
its real executing clauses. The M leaf uses the derived selected-right
comparison. The genuine nonM singleton leaf compares directly with every
entry bounded by the smaller input. Actual factor frames compare smaller
left inputs recursively with their actual child, equal child values by
complete execution value invariance, and larger left inputs through the
exhaustive actual critical-interval proof. No recursive comparison, branch,
word, suffix provenance or lexical bound is supplied. Source-only uncompiled
candidates in genuine native epsilon contexts; no Native base-one dictionary.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment.Order

open Alexander313.Wilken.MultiplicativeNormalForm

/-- Every pair of independently executing complete native Assignments is
strictly ordered by its genuine original input ordinal comparison. -/
theorem execute_lex (q left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute q left) (hy : ys ∈ Assignment.execute q right)
    (hlt : interpretation q left < interpretation q right) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  let P : Nat → Prop := fun n => ∀ right : Nat,
    (canonicalMNF (interpretation q right)).length = n → ∀ left : Nat, ∀ xs ys : List Nat,
      xs ∈ Assignment.execute q left → ys ∈ Assignment.execute q right →
        interpretation q left < interpretation q right →
          List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q))
  have hp : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro right hn left xs ys hx hy hlt
      rcases Assignment.execute_clauses q right ys hy with ⟨hm, he⟩ |
        ⟨hm, hs, he⟩ | ⟨hm, hs, prefix, factor, heads, hf, hh, ho⟩
      · exact AssignmentCoverPrefix.execute_right_multiplicative_lex q left right xs ys hm hlt hx hy
      · obtain ⟨a, tail, hxs⟩ := List.exists_cons_of_ne_nil (Assignment.execute_nonempty q left xs hx)
        have ha : interpretation q a < interpretation q right :=
          ((Assignment.execute_spec q left xs hx).2.1.2.1 a (by rw [hxs]; exact List.mem_cons_self)).trans_lt hlt
        simpa only [hxs, he, List.map_cons, List.map_nil] using
          (List.Lex.rel ha : List.Lex (· < ·)
            (interpretation q a :: tail.map (interpretation q)) [interpretation q right])
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcount⟩ :=
          Factor.execute_spec q right (prefix, factor) hf
        have hframe := FrameOrderSupport.execute_frame_lex q right prefix factor heads ys hf hh ho
        rcases lt_trichotomy (interpretation q left) (interpretation q prefix) with hl | he | hl
        · have hchild := ih (canonicalMNF (interpretation q prefix)).length
            (by simpa only [hn] using hcount) prefix rfl left xs heads hx hh hl
          exact List.lex_trans (fun hab hbc => hab.trans hbc) hchild hframe
        · rw [Assignment.ValueInvariance.execute_values_eq q left prefix xs heads hx hh he]
          exact hframe
        · exact IntervalOrder.execute_interval_lex q right prefix factor left xs ys hf hx hy hl hlt
  exact hp (canonicalMNF (interpretation q right)).length right rfl left xs ys hx hy hlt

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment.Order
