import Alexander313.Wilken.MultiplicativeNormalForm

/-!
# The genuine final factor after a principal product

Actual ordinal absorption of a finite principal sum preserves its last
summand. Consequently adding a positive principal on the right leaves
that principal as the real final ANF exponent. Applying the genuine
omega logarithms proves that a positive additive principal multiplied by
a multiplicative principal greater than one ends at that factor in its
canonical MNF. This supplies the normal-form clause of Lemma 3.21.2.
No factorization, normal-form equality or last-factor oracle. Uncompiled.
-/

namespace Alexander313.Wilken.MultiplicativeNormalForm.LastFactorProduct

universe u

open MultiplicativePrincipalArithmetic

private theorem prepend_ends (a last : Ordinal.{u}) (before : List Ordinal.{u}) :
    ∃ kept, prependPrincipal a (before ++ [last]) = kept ++ [last] := by
  classical
  cases before with
  | nil =>
    by_cases h : a < last
    · exact ⟨[], by simp only [List.nil_append, prependPrincipal, if_pos h]⟩
    · exact ⟨[a], by simp only [List.nil_append, prependPrincipal, if_neg h, List.singleton_append]⟩
  | cons b bs =>
    by_cases h : a < b
    · exact ⟨b :: bs, by simp only [List.cons_append, prependPrincipal, if_pos h]⟩
    · exact ⟨a :: b :: bs, by simp only [List.cons_append, prependPrincipal, if_neg h]⟩

private theorem normalize_ends (before : List Ordinal.{u}) (last : Ordinal.{u}) :
    ∃ kept, normalizePrincipal (before ++ [last]) = kept ++ [last] := by
  classical
  induction before with
  | nil => exact ⟨[], by simp only [List.nil_append, normalizePrincipal, prependPrincipal]⟩
  | cons a bs ih =>
    obtain ⟨kept, he⟩ := ih
    simp only [List.cons_append, normalizePrincipal, he]
    exact prepend_ends a last kept

/-- This concerns the actual canonical ANF, including genuine absorption
of any smaller terminal summands of the left operand. -/
theorem endExponent_add_principal (left right : Ordinal.{u})
    (hr : 0 < right) (hp : Ordinal.IsPrincipal (· + ·) right) :
    endExponent (left + right) = right := by
  rw [endExponent, canonicalANF_add, canonicalANF_principal hr hp]
  obtain ⟨kept, he⟩ := normalize_ends (canonicalANF left) right
  rw [he]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.getElem?_cons_zero, Option.getD_some]

/-- The real final MNF factor of head*factor is exactly factor. -/
theorem lf_principal_mul (head factor : Ordinal.{u})
    (hh : 0 < head) (hp : Ordinal.IsPrincipal (· + ·) head)
    (hf : IsMultiplicativePrincipal factor) (hone : 1 < factor) :
    lf (head * factor) = factor := by
  have hl := multiplicative_log_spec hf hone
  have he : head * factor = Ordinal.omega0 ^
      (Ordinal.log Ordinal.omega0 head + Ordinal.log Ordinal.omega0 factor) := by
    rw [Ordinal.opow_add, positivePrincipal_eq_omegaLog hh hp,
      positivePrincipal_eq_omegaLog hf.1 hf.2.1]
  calc
    lf (head * factor) = lf (Ordinal.omega0 ^
        (Ordinal.log Ordinal.omega0 head + Ordinal.log Ordinal.omega0 factor)) := congrArg lf he
    _ = Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 factor := by
      rw [lf_omegaPower, endExponent_add_principal _ _ hl.1 hl.2]
    _ = factor := positivePrincipal_eq_omegaLog hf.1 hf.2.1

theorem principal_mul_prefix_last (head factor : Ordinal.{u})
    (hh : 0 < head) (hp : Ordinal.IsPrincipal (· + ·) head)
    (hf : IsMultiplicativePrincipal factor) (hone : 1 < factor) :
    head * factor = factorProduct (factorPrefix (canonicalMNF (head * factor))) * factor := by
  have hpos := hh.trans_le (Ordinal.le_mul_left head hf.1)
  have hadd := Ordinal.isPrincipal_add_mul_of_isPrincipal_add head (ne_of_gt hone) hf.2.1
  simpa only [lf_principal_mul head factor hh hp hf hone] using source_prefix_last hpos hadd

end Alexander313.Wilken.MultiplicativeNormalForm.LastFactorProduct
