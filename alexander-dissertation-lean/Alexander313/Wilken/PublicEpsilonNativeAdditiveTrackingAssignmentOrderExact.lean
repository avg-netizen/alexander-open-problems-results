import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignmentOrder

/-!
# Exact value and lexical reflection for native assignments

Genuine full strict order and actual SAME-value word invariance yield both
value injectivity and exact lexical reflection on independently executing
complete words. Ordinal trichotomy supplies the reverse directions; no
assigned word, inverse evaluator or tracking-image oracle is supplied.
Source-only uncompiled candidates in the genuine native epsilon dictionaries.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment.OrderExact

/-- Equal complete word VALUES reflect equality of the original inputs. -/
theorem execute_values_eq_iff (q left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute q left) (hy : ys ∈ Assignment.execute q right) :
    xs.map (interpretation q) = ys.map (interpretation q) ↔
      interpretation q left = interpretation q right := by
  constructor
  · intro hv
    rcases lt_trichotomy (interpretation q left) (interpretation q right) with hl | he | hr
    · have hlex := Order.execute_lex q left right xs ys hx hy hl
      rw [hv] at hlex
      exact False.elim ((lt_irrefl _) hlex)
    · exact he
    · have hlex := Order.execute_lex q right left ys xs hy hx hr
      rw [hv] at hlex
      exact False.elim ((lt_irrefl _) hlex)
  · exact ValueInvariance.execute_values_eq q left right xs ys hx hy

/-- Lexical comparison of complete actual word VALUES is equivalent to
strict comparison of the genuine original principal input values. -/
theorem execute_lex_iff (q left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute q left) (hy : ys ∈ Assignment.execute q right) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) ↔
      interpretation q left < interpretation q right := by
  constructor
  · intro hlex
    rcases lt_trichotomy (interpretation q left) (interpretation q right) with hl | he | hr
    · exact hl
    · have hv := ValueInvariance.execute_values_eq q left right xs ys hx hy he
      rw [hv] at hlex
      exact False.elim ((lt_irrefl _) hlex)
    · exact False.elim (asymm hlex (Order.execute_lex q right left ys xs hy hx hr))
  · exact Order.execute_lex q left right xs ys hx hy

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.Assignment.OrderExact
