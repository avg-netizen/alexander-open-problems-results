import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignmentOrder

/-!
# Exact value and lexical reflection for original source-one assignments

Genuine full strict order and actual SAME-value word invariance yield both
value injectivity and exact lexical reflection on independently executing
complete words. Ordinal trichotomy supplies the reverse directions; no
assigned word, inverse evaluator or tracking-image oracle is supplied.
Source-only uncompiled candidates in the original source-zero dictionary.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment.OrderExact

/-- Equal complete word VALUES reflect equality of the original inputs. -/
theorem execute_values_eq_iff (left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute left) (hy : ys ∈ Assignment.execute right) :
    xs.map (interpretation 0) = ys.map (interpretation 0) ↔
      interpretation 0 left = interpretation 0 right := by
  constructor
  · intro hv
    rcases lt_trichotomy (interpretation 0 left) (interpretation 0 right) with hl | he | hr
    · have hlex := Order.execute_lex left right xs ys hx hy hl
      rw [hv] at hlex
      exact False.elim ((lt_irrefl _) hlex)
    · exact he
    · have hlex := Order.execute_lex right left ys xs hy hx hr
      rw [hv] at hlex
      exact False.elim ((lt_irrefl _) hlex)
  · exact ValueInvariance.execute_values_eq left right xs ys hx hy

/-- Lexical comparison of complete actual word VALUES is equivalent to
strict comparison of the genuine original principal input values. -/
theorem execute_lex_iff (left right : Nat) (xs ys : List Nat)
    (hx : xs ∈ Assignment.execute left) (hy : ys ∈ Assignment.execute right) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) ↔
      interpretation 0 left < interpretation 0 right := by
  constructor
  · intro hlex
    rcases lt_trichotomy (interpretation 0 left) (interpretation 0 right) with hl | he | hr
    · exact hl
    · have hv := ValueInvariance.execute_values_eq left right xs ys hx hy he
      rw [hv] at hlex
      exact False.elim ((lt_irrefl _) hlex)
    · exact False.elim (asymm hlex (Order.execute_lex right left ys xs hy hx hr))
  · exact Order.execute_lex left right xs ys hx hy

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.Assignment.OrderExact
