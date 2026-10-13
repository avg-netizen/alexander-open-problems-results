import Alexander313.Wilken.HereditarySourceZeta

/-!
# The actual last component under positive right addition

Principal normalization can absorb a prefix, but never the final component
of a nonzero right summand. The actual canonical additive normal form thus
proves the last-component and last-logarithm identities needed in the
shifted high-tail branch of lambda transport. The zero residual is excluded
from these identities and needs the genuine strict fixed-point argument.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.LastExponentAddition

universe u

private def lastValue (xs : List Ordinal.{u}) : Ordinal.{u} := xs.reverse[0]?.getD 0

private theorem lastValue_cons (a : Ordinal.{u}) (xs : List Ordinal.{u}) (hx : xs ≠ []) :
    lastValue (a :: xs) = lastValue xs := by
  cases hr : xs.reverse with
  | nil =>
    have he := congrArg List.reverse hr
    have hz : xs = [] := by simpa only [List.reverse_reverse, List.reverse_nil] using he
    exact False.elim (hx hz)
  | cons b bs =>
    simp only [lastValue, List.reverse_cons, hr, List.cons_append,
      List.getElem?_cons_zero, Option.getD_some]

private theorem prependPrincipal_nonempty (a : Ordinal.{u}) (xs : List Ordinal.{u}) :
    prependPrincipal a xs ≠ [] := by
  classical
  cases xs with
  | nil => exact List.cons_ne_nil a []
  | cons b bs =>
    by_cases h : a < b
    · simpa only [prependPrincipal, if_pos h] using List.cons_ne_nil b bs
    · simpa only [prependPrincipal, if_neg h] using List.cons_ne_nil a (b :: bs)

private theorem normalizePrincipal_nonempty (xs : List Ordinal.{u}) (hx : xs ≠ []) :
    normalizePrincipal xs ≠ [] := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons a as => exact prependPrincipal_nonempty a (normalizePrincipal as)

private theorem lastValue_prependPrincipal (a : Ordinal.{u}) (xs : List Ordinal.{u})
    (hx : xs ≠ []) : lastValue (prependPrincipal a xs) = lastValue xs := by
  classical
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons b bs =>
    by_cases h : a < b
    · simp only [prependPrincipal, if_pos h]
    · rw [prependPrincipal, if_neg h]
      exact lastValue_cons a (b :: bs) (by simp)

private theorem lastValue_normalizePrincipal (xs : List Ordinal.{u}) (hx : xs ≠ []) :
    lastValue (normalizePrincipal xs) = lastValue xs := by
  revert hx
  induction xs with
  | nil => intro hx; exact False.elim (hx rfl)
  | cons a as ih =>
    intro hx
    by_cases ha : as = []
    · subst as
      simp only [normalizePrincipal, prependPrincipal]
    · rw [normalizePrincipal, lastValue_prependPrincipal a _ (normalizePrincipal_nonempty as ha),
        ih ha, lastValue_cons a as ha]

private theorem lastValue_append (xs ys : List Ordinal.{u}) (hy : ys ≠ []) :
    lastValue (xs ++ ys) = lastValue ys := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.cons_append, lastValue_cons a (as ++ ys) (by
      intro he
      exact hy (List.append_eq_nil_iff.mp he).2), ih]

theorem endValue_add (alpha rho : Ordinal.{0}) (hr : 0 < rho) :
    LogEnd.endValue (alpha + rho) = LogEnd.endValue rho := by
  have hn : canonicalANF rho ≠ [] := by
    intro he
    have hz : rho = 0 := by
      have hv := principalSum_canonicalANF rho
      simpa only [he, principalSum] using hv.symm
    exact (ne_of_gt hr) hz
  change lastValue (canonicalANF (alpha + rho)) = lastValue (canonicalANF rho)
  rw [canonicalANF_add, lastValue_normalizePrincipal _ (by
    intro he
    exact hn (List.append_eq_nil_iff.mp he).2), lastValue_append _ _ hn]

theorem lastExponent_add (alpha rho : Ordinal.{0}) (hr : 0 < rho) :
    SourceZeta.lastExponent (alpha + rho) = SourceZeta.lastExponent rho := by
  simp only [SourceZeta.lastExponent, endValue_add alpha rho hr]

theorem lastLogSpec_add (alpha rho eta : Ordinal.{0}) (hr : 0 < rho) :
    LogEnd.SourceLogSpec true (alpha + rho) eta ↔ LogEnd.SourceLogSpec true rho eta := by
  have hn : alpha + rho ≠ 0 := ne_of_gt (hr.trans_le le_add_self)
  simp only [LogEnd.SourceLogSpec, if_neg hn, if_neg (ne_of_gt hr),
    LogEnd.componentValue, Bool.cond_true]
  change Ordinal.omega0 ^ eta = LogEnd.endValue (alpha + rho) ↔
    Ordinal.omega0 ^ eta = LogEnd.endValue rho
  rw [endValue_add alpha rho hr]

end Alexander313.Wilken.RelativeTerm.Hereditary.LastExponentAddition
