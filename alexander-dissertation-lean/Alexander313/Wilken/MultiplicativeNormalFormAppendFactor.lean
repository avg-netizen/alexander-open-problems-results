import Alexander313.Wilken.MultiplicativeFactorRemovalBounds

/-!
# A genuine descending factor append identifies the canonical next frame

The actual reduced MNF of a positive additive principal is extended by a
nonunit multiplicative principal at most its actual last factor. Descending
order and reduced uniqueness identify the complete canonical MNF, its prefix
product and its last factor. The product is nonmultiplicative when the old
input exceeds one. No supplied next factorization or parser equality occurs.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.MultiplicativeNormalForm.AppendFactor

universe u

open MultiplicativePrincipalArithmetic MultiplicativeFactorRemoval

theorem lastFactor_le_member (xs : List Ordinal.{u}) (hx : IsReducedMNF xs)
    (hne : xs ≠ []) (a : Ordinal.{u}) (ha : a ∈ xs) : lastFactor xs ≤ a := by
  have hs := prefix_last_split xs hne
  have hp : (factorPrefix xs ++ [lastFactor xs]).Pairwise (fun a b => b ≤ a) := by
    simpa only [← hs] using hx.1.2
  have hm : a ∈ factorPrefix xs ++ [lastFactor xs] := by simpa only [← hs] using ha
  rcases List.mem_append.mp hm with hm | hm
  · exact (List.pairwise_append.mp hp).2.2 a hm _ List.mem_cons_self
  · rw [List.mem_singleton.mp hm]

theorem reduced_append (xs : List Ordinal.{u}) (hx : IsReducedMNF xs)
    (hne : xs ≠ []) (factor : Ordinal.{u})
    (hm : IsMultiplicativePrincipal factor) (hone : 1 < factor)
    (hcut : factor ≤ lastFactor xs) : IsReducedMNF (xs ++ [factor]) := by
  refine ⟨⟨?_, (List.pairwise_append).mpr ⟨hx.1.2, by simp, ?_⟩⟩, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hx.1.1 a ha
    · simpa only [List.mem_singleton.mp ha] using hm
  · intro a ha b hb
    rw [List.mem_singleton.mp hb]
    exact hcut.trans (lastFactor_le_member xs hx hne a ha)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hx.2 a ha
    · simpa only [List.mem_singleton.mp ha] using hone

theorem canonical_append {current factor : Ordinal.{u}}
    (hcurrent : 1 < current) (hp : Ordinal.IsPrincipal (· + ·) current)
    (hm : IsMultiplicativePrincipal factor) (hone : 1 < factor)
    (hcut : factor ≤ lf current) :
    canonicalMNF (current * factor) = canonicalMNF current ++ [factor] := by
  have hne : canonicalMNF current ≠ [] := by
    intro he
    exact (ne_of_gt hcurrent) ((canonicalMNF_nil_iff (zero_lt_one.trans hcurrent) hp).mp he)
  have hx := reduced_append _ (canonicalMNF_reduced current) hne factor hm hone hcut
  have hv : factorProduct (canonicalMNF current ++ [factor]) = current * factor := by
    simp only [factorProduct_append, factorProduct, mul_one,
      factorProduct_canonicalMNF (zero_lt_one.trans hcurrent) hp]
  have hprincipal := isMNF_product_principal hx.1
  exact (reducedMNF_unique hx (canonicalMNF_reduced (current * factor))
    (hv.trans (factorProduct_canonicalMNF
      (by simpa only [hv] using hprincipal.1)
      (by simpa only [hv] using hprincipal.2)).symm)).symm

theorem prefix_last {current factor : Ordinal.{u}}
    (hcurrent : 1 < current) (hp : Ordinal.IsPrincipal (· + ·) current)
    (hm : IsMultiplicativePrincipal factor) (hone : 1 < factor)
    (hcut : factor ≤ lf current) :
    factorProduct (factorPrefix (canonicalMNF (current * factor))) = current ∧
      lf (current * factor) = factor ∧ ¬IsMultiplicativePrincipal (current * factor) := by
  have he := canonical_append hcurrent hp hm hone hcut
  have hprefix : factorPrefix (canonicalMNF (current * factor)) = canonicalMNF current := by
    simp only [he, factorPrefix, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.tail_cons, List.reverse_reverse]
  have hlast : lf (current * factor) = factor := by
    simp only [lf, he, lastFactor, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.getElem?_cons_zero, Option.getD_some]
  refine ⟨by rw [hprefix]; exact factorProduct_canonicalMNF (zero_lt_one.trans hcurrent) hp,
    hlast, ?_⟩
  intro hmul
  have hproduct : 1 < current * factor :=
    hcurrent.trans_le (by
      simpa only [mul_one] using mul_le_mul_right hone.le current)
  have hsingle := canonicalMNF_multiplicative hmul hproduct
  have hlength := congrArg List.length (he.symm.trans hsingle)
  simp only [List.length_append, List.length_singleton] at hlength
  have hne : canonicalMNF current ≠ [] := by
    intro hn
    exact (ne_of_gt hcurrent) ((canonicalMNF_nil_iff (zero_lt_one.trans hcurrent) hp).mp hn)
  have hpositive : 0 < (canonicalMNF current).length := List.length_pos_iff.mpr hne
  omega

end Alexander313.Wilken.MultiplicativeNormalForm.AppendFactor
