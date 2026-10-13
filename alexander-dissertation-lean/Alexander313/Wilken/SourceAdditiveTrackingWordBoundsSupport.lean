import Alexander313.Wilken.PublicEpsilonNativeSkTrackingSupport

/-!
# Finite last-entry bounds for the actual additive tracking procedures

These list lemmas preserve the genuine final position through value-wise
recoding and concatenation. They make no claim that the final value equals
the original input. Both the native epsilon and original source-one
procedures can use these same finite code-list facts. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceAdditiveTrackingWordBounds

open NativeContext.SourceTrackingSequences

theorem lastCode_append_nonempty (before word : List Nat) (hne : word ≠ []) :
    lastCode (before ++ word) = lastCode word := by
  obtain ⟨last, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split word hne
  rw [he, ← List.append_assoc, lastCode_append_singleton, lastCode_append_singleton]

/-- A whole chronological equality of values preserves the last value,
without requiring code identity or any relation between source contexts. -/
theorem lastCode_values_eq (f g : Nat → Ordinal.{0}) (xs ys : List Nat)
    (hx : xs ≠ []) (hmap : xs.map f = ys.map g) :
    f (lastCode xs) = g (lastCode ys) := by
  revert hx hmap
  induction xs generalizing ys with
  | nil => intro hx hmap; exact False.elim (hx rfl)
  | cons a xs ih =>
    intro hx hmap
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hmap
    | cons b ys =>
      have he := List.cons.inj hmap
      by_cases ht : xs = []
      · subst xs
        have hn : ys = [] := List.map_eq_nil_iff.mp he.2.symm
        subst ys
        simpa only [lastCode_singleton] using he.1
      · have hy : ys ≠ [] := by
          intro hn
          apply ht
          exact List.map_eq_nil_iff.mp (by simpa only [hn, List.map_nil] using he.2)
        rw [NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support.lastCode_cons_nonempty a xs ht,
          NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support.lastCode_cons_nonempty b ys hy]
        exact ih ys ht he.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceAdditiveTrackingWordBounds
