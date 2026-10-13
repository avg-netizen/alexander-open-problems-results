import Alexander313.Wilken.MultiplicativeNormalForm

/-!
# Genuine removal of the final multiplicative normal-form factor

The real reduced MNF supplies its final factor and the retained prefix.
For a non-multiplicative positive additive principal at least a source M
base, the prefix is nonempty and its product stays in the source interval.
Descending factors and actual multiplicative closure prove the lower
bound; strict multiplication by the final factor proves the upper bound.
No factorization or interval premise is supplied. Uncompiled candidates.
-/

namespace Alexander313.Wilken.MultiplicativeFactorRemoval

universe u

open MultiplicativeNormalForm MultiplicativePrincipalArithmetic

theorem factorProduct_pos (xs : List Ordinal.{u})
    (hx : ∀ a ∈ xs, 0 < a) : 0 < factorProduct xs := by
  revert hx
  induction xs with
  | nil => intro _; exact zero_lt_one
  | cons a xs ih =>
    intro hx
    exact mul_pos (hx a List.mem_cons_self)
      (ih (fun b hb => hx b (List.mem_cons_of_mem _ hb)))

theorem factorProduct_mem_le (xs : List Ordinal.{u})
    (hx : ∀ a ∈ xs, 0 < a) (a : Ordinal.{u}) (ha : a ∈ xs) :
    a ≤ factorProduct xs := by
  revert hx ha
  induction xs with
  | nil => intro _ ha; exact False.elim (List.not_mem_nil ha)
  | cons b xs ih =>
    intro hx ha
    have hb := hx b List.mem_cons_self
    have ht : ∀ c ∈ xs, 0 < c := fun c hc => hx c (List.mem_cons_of_mem _ hc)
    rcases List.mem_cons.mp ha with rfl | ha
    · calc
        a = a * 1 := (mul_one a).symm
        _ ≤ a * factorProduct xs := mul_le_mul_right
          (Order.one_le_iff_pos.mpr (factorProduct_pos xs ht)) a
    · exact (ih ht ha).trans (Ordinal.le_mul_right (factorProduct xs) hb)

theorem factorPrefix_sublist (xs : List Ordinal.{u}) : (factorPrefix xs).Sublist xs := by
  simpa only [factorPrefix, List.reverse_reverse] using (List.tail_sublist xs.reverse).reverse

theorem factorPrefix_reduced (xs : List Ordinal.{u}) (hx : IsReducedMNF xs) :
    IsReducedMNF (factorPrefix xs) := by
  have hs := factorPrefix_sublist xs
  exact ⟨⟨fun a ha => hx.1.1 a (hs.subset ha), hx.1.2.sublist hs⟩,
    fun a ha => hx.2 a (hs.subset ha)⟩

theorem prefix_last_split (xs : List Ordinal.{u}) (hne : xs ≠ []) :
    xs = factorPrefix xs ++ [lastFactor xs] := by
  cases hr : xs.reverse with
  | nil => exact False.elim (hne (List.reverse_eq_nil_iff.mp hr))
  | cons a as =>
    have he := congrArg List.reverse hr
    simp only [List.reverse_reverse, List.reverse_cons] at he
    simp only [factorPrefix, lastFactor, hr, List.tail_cons,
      List.getElem?_cons_zero, Option.getD_some]
    exact he

theorem nonmultiplicative_prefix_nonempty {α : Ordinal.{u}}
    (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : ¬ IsMultiplicativePrincipal α) : factorPrefix (canonicalMNF α) ≠ [] := by
  have hn : canonicalMNF α ≠ [] := by
    intro he
    have hu := (canonicalMNF_nil_iff hα hp).mp he
    apply hm
    rw [hu]
    exact ⟨zero_lt_one, Ordinal.isPrincipal_add_one, Ordinal.isPrincipal_mul_one⟩
  intro he
  have hs := prefix_last_split (canonicalMNF α) hn
  rw [he, List.nil_append] at hs
  have hl := lastFactor_spec (canonicalMNF_reduced α) hn
  have hv := factorProduct_canonicalMNF hα hp
  rw [hs] at hv
  have ha : lastFactor (canonicalMNF α) = α := by
    simpa only [factorProduct, mul_one] using hv
  exact hm (ha ▸ hl.1)

theorem source_prefix_canonicalMNF (α : Ordinal.{u}) :
    canonicalMNF (factorProduct (factorPrefix (canonicalMNF α))) =
      factorPrefix (canonicalMNF α) := by
  have hf := factorPrefix_reduced _ (canonicalMNF_reduced α)
  have hp := isMNF_product_principal hf.1
  exact (reducedMNF_unique hf (canonicalMNF_reduced _)
    (factorProduct_canonicalMNF hp.1 hp.2).symm).symm

theorem source_prefix_factor_count_lt {α : Ordinal.{u}}
    (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : ¬ IsMultiplicativePrincipal α) :
    (canonicalMNF (factorProduct (factorPrefix (canonicalMNF α)))).length <
      (canonicalMNF α).length := by
  have hn : canonicalMNF α ≠ [] := by
    intro he
    have hpne := nonmultiplicative_prefix_nonempty hα hp hm
    exact hpne (by simp only [he, factorPrefix, List.reverse_nil, List.tail_nil])
  rw [source_prefix_canonicalMNF]
  have hlen := congrArg List.length (prefix_last_split (canonicalMNF α) hn)
  simp only [List.length_append, List.length_singleton] at hlen
  omega

/-- The genuine source interval for the printed Definition3.20 recursion.
The non-M hypothesis and the actual canonical MNF derive every factor and
both interval endpoints; the base retains its full displayed M predicate. -/
theorem source_prefix_last_interval {τ α : Ordinal.{u}}
    (hτ : IsMultiplicativePrincipal τ) (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) (hτα : τ ≤ α)
    (hm : ¬ IsMultiplicativePrincipal α) :
    τ ≤ factorProduct (factorPrefix (canonicalMNF α)) ∧
      factorProduct (factorPrefix (canonicalMNF α)) < α ∧
      IsMultiplicativePrincipal (lf α) ∧ 1 < lf α ∧
      α = factorProduct (factorPrefix (canonicalMNF α)) * lf α := by
  let xs := canonicalMNF α
  have hx : IsReducedMNF xs := canonicalMNF_reduced α
  have hpne : factorPrefix xs ≠ [] := nonmultiplicative_prefix_nonempty hα hp hm
  have hne : xs ≠ [] := by
    intro he
    exact hpne (by simp only [he, factorPrefix, List.reverse_nil, List.tail_nil])
  have hs := prefix_last_split xs hne
  have hf := factorPrefix_reduced xs hx
  have hpos := factorProduct_pos (factorPrefix xs) (fun a ha => (hf.1.1 a ha).1)
  have hl := lastFactor_spec hx hne
  have hvalue : α = factorProduct (factorPrefix xs) * lastFactor xs := by
    exact (factorProduct_canonicalMNF hα hp).symm.trans (factorProduct_prefix_last xs)
  have hu : factorProduct (factorPrefix xs) < α := by
    rw [hvalue]
    simpa only [mul_one] using positive_mul_strictMono hpos hl.2
  have hb : τ ≤ factorProduct (factorPrefix xs) := by
    apply le_of_not_gt
    intro hsmall
    cases he : factorPrefix xs with
    | nil => exact False.elim (hpne he)
    | cons a as =>
      have has : xs = (a :: as) ++ [lastFactor xs] := by rw [← he]; exact hs
      have hlast : lastFactor xs ≤ a := by
        have ht := hx.1.2
        rw [has, List.cons_append] at ht
        exact (List.pairwise_cons.mp ht).1 _ (List.mem_append.mpr (Or.inr List.mem_cons_self))
      have ha : a ≤ factorProduct (factorPrefix xs) :=
        factorProduct_mem_le _ (fun b hb => (hf.1.1 b hb).1) _
          (by rw [he]; exact List.mem_cons_self)
      have hlt := hτ.2.2 hsmall ((hlast.trans ha).trans_lt hsmall)
      have halt : α < τ := by rw [hvalue]; exact hlt
      exact (not_lt_of_ge hτα) halt
  exact ⟨hb, hu, hl.1, hl.2, hvalue⟩

end Alexander313.Wilken.MultiplicativeFactorRemoval
