import Alexander313.Wilken.MultiplicativePrincipalInterval
import Alexander313.Wilken.MultiplicativeFactorRemovalBounds

/-!
# The actual factor stack in an intervening principal interval

The descending final factor of the greater input is no greater than the
real last factor of its prefix. The genuinely computed smaller quotient
is therefore below every factor in that prefix. Reduced MNF uniqueness
identifies the intervening input's complete factor list as the unchanged
prefix list followed by the actual quotient list. Removing one factor
from that real list leaves the same original prefix and removes exactly
one quotient factor. No written source syntax equality or subsidiary
tracking comparison follows from this ordinal list identity. Uncompiled.
-/

namespace Alexander313.Wilken.MultiplicativePrincipalInterval.Factors

universe u

open MultiplicativeNormalForm MultiplicativeFactorRemoval MultiplicativePrincipalArithmetic

theorem lastFactor_le_member {xs : List Ordinal.{u}} (hne : xs ≠ [])
    (horder : xs.Pairwise (fun a b => b ≤ a)) (a : Ordinal.{u}) (ha : a ∈ xs) :
    lastFactor xs ≤ a := by
  have hs := prefix_last_split xs hne
  have ho := horder
  rw [hs] at ho ha
  rcases List.mem_append.mp ha with hp | hl
  · exact (List.pairwise_append.mp ho).2.2 a hp _ List.mem_cons_self
  · simpa only [List.mem_singleton.mp hl] using (le_refl (lastFactor xs))

theorem canonical_factor_le {alpha : Ordinal.{u}} (hp : 0 < alpha)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (a : Ordinal.{u})
    (hm : a ∈ canonicalMNF alpha) : a ≤ alpha := by
  have hr := canonicalMNF_reduced alpha
  have hl := factorProduct_mem_le _ (fun b hb => (hr.1.1 b hb).1) a hm
  simpa only [factorProduct_canonicalMNF hp ha] using hl

theorem lf_le_principal {alpha : Ordinal.{u}} (hp : 0 < alpha)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) : lf alpha ≤ alpha := by
  by_cases he : alpha = 1
  · simp only [he, lf_one, le_refl]
  · have hn : canonicalMNF alpha ≠ [] :=
      fun hn => he ((canonicalMNF_nil_iff hp ha).mp hn)
    exact canonical_factor_le hp ha _ (lastFactor_mem _ hn)

/-- Actual reduced-list uniqueness, with the strict cut supplying every
cross-list descending comparison. -/
theorem canonicalMNF_mul_of_smaller_right {eta delta : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta) (hne : eta ≠ 1)
    (hd : 0 < delta) (hda : Ordinal.IsPrincipal (· + ·) delta)
    (hcut : delta < lf eta) :
    canonicalMNF (eta * delta) = canonicalMNF eta ++ canonicalMNF delta := by
  have hx := canonicalMNF_reduced eta
  have hy := canonicalMNF_reduced delta
  have hn : canonicalMNF eta ≠ [] := fun hn => hne ((canonicalMNF_nil_iff heta he).mp hn)
  have hred : IsReducedMNF (canonicalMNF eta ++ canonicalMNF delta) := by
    refine ⟨⟨?_, List.pairwise_append.mpr ⟨hx.1.2, hy.1.2, ?_⟩⟩, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hx.1.1 a ha
      · exact hy.1.1 a ha
    · intro a ha b hb
      exact (canonical_factor_le hd hda b hb).trans
        (hcut.le.trans (lastFactor_le_member hn hx.1.2 a ha))
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hx.2 a ha
      · exact hy.2 a ha
  have hv : factorProduct (canonicalMNF eta ++ canonicalMNF delta) = eta * delta := by
    rw [factorProduct_append, factorProduct_canonicalMNF heta he,
      factorProduct_canonicalMNF hd hda]
  have hp := isMNF_product_principal hred.1
  have hpos : 0 < eta * delta := by rw [← hv]; exact hp.1
  have hadd : Ordinal.IsPrincipal (· + ·) (eta * delta) := by rw [← hv]; exact hp.2
  exact (reducedMNF_unique hred (canonicalMNF_reduced _)
    (hv.trans (factorProduct_canonicalMNF hpos hadd).symm)).symm

theorem lastFactor_append (xs ys : List Ordinal.{u}) (hy : ys ≠ []) :
    lastFactor (xs ++ ys) = lastFactor ys := by
  cases hr : ys.reverse with
  | nil => exact False.elim (hy (List.reverse_eq_nil_iff.mp hr))
  | cons a as =>
    simp only [lastFactor, List.reverse_append, hr, List.cons_append,
      List.getElem?_cons_zero, Option.getD_some]

theorem factorPrefix_append (xs ys : List Ordinal.{u}) (hy : ys ≠ []) :
    factorPrefix (xs ++ ys) = xs ++ factorPrefix ys := by
  cases hr : ys.reverse with
  | nil => exact False.elim (hy (List.reverse_eq_nil_iff.mp hr))
  | cons a as =>
    simp only [factorPrefix, List.reverse_append, hr, List.cons_append,
      List.tail_cons, List.reverse_append, List.reverse_reverse]

/-- The original interval and genuine last-factor cut derive the actual
nonempty quotient factor stack, including every strict factor bound. -/
theorem interval_factor_stack {eta alpha factor : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (hf : 1 < factor)
    (hfinal : factor ≤ lf eta) (hl : eta < alpha) (hr : alpha < eta * factor) :
    ¬ IsMultiplicativePrincipal alpha ∧ 1 < alpha / eta ∧
      alpha / eta < factor ∧
      canonicalMNF alpha = canonicalMNF eta ++ canonicalMNF (alpha / eta) ∧
      canonicalMNF (alpha / eta) ≠ [] ∧
      (∀ a ∈ canonicalMNF (alpha / eta), a < factor) ∧ lf alpha < factor := by
  have hne : eta ≠ 1 := by
    intro hz
    have hu : factor ≤ 1 := by simpa only [hz, lf_one] using hfinal
    exact (not_le_of_gt hf) hu
  have hle : factor ≤ eta := hfinal.trans (lf_le_principal heta he)
  have hs := descending_interval_spec heta he ha hle hl hr
  have hd : 0 < alpha / eta := zero_lt_one.trans hs.2.1
  have hda := hs.2.2.2.2.2.1
  have hvalue := hs.2.2.2.2.2.2
  have hstack : canonicalMNF alpha = canonicalMNF eta ++ canonicalMNF (alpha / eta) := by
    calc
      canonicalMNF alpha = canonicalMNF (eta * (alpha / eta)) := congrArg canonicalMNF hvalue.symm
      _ = canonicalMNF eta ++ canonicalMNF (alpha / eta) :=
        canonicalMNF_mul_of_smaller_right heta he hne hd hda
          (hs.2.2.1.trans_le hfinal)
  have hqne : canonicalMNF (alpha / eta) ≠ [] := by
    intro hz
    exact (ne_of_gt hs.2.1) ((canonicalMNF_nil_iff hd hda).mp hz)
  have hbound : ∀ a ∈ canonicalMNF (alpha / eta), a < factor :=
    fun a hm => (canonical_factor_le hd hda a hm).trans_lt hs.2.2.1
  have hlast : lf alpha < factor := by
    change lastFactor (canonicalMNF alpha) < factor
    rw [hstack, lastFactor_append _ _ hqne]
    exact hbound _ (lastFactor_mem _ hqne)
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hstack, hqne, hbound, hlast⟩

/-- The real final-factor removal step leaves the original prefix
untouched and removes one factor from the actual smaller quotient. -/
theorem interval_prefix_step {eta alpha factor : Ordinal.{u}}
    (heta : 0 < eta) (he : Ordinal.IsPrincipal (· + ·) eta)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (hf : 1 < factor)
    (hfinal : factor ≤ lf eta) (hl : eta < alpha) (hr : alpha < eta * factor) :
    canonicalMNF (factorProduct (factorPrefix (canonicalMNF alpha))) =
      canonicalMNF eta ++ factorPrefix (canonicalMNF (alpha / eta)) ∧
    factorProduct (factorPrefix (canonicalMNF alpha)) =
      eta * factorProduct (factorPrefix (canonicalMNF (alpha / eta))) := by
  have hs := interval_factor_stack heta he ha hf hfinal hl hr
  have hpre : factorPrefix (canonicalMNF alpha) =
      canonicalMNF eta ++ factorPrefix (canonicalMNF (alpha / eta)) := by
    rw [hs.2.2.2.1, factorPrefix_append _ _ hs.2.2.2.2.1]
  refine ⟨by rw [source_prefix_canonicalMNF, hpre], ?_⟩
  rw [hpre, factorProduct_append, factorProduct_canonicalMNF heta he]

end Alexander313.Wilken.MultiplicativePrincipalInterval.Factors
