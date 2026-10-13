import Alexander313.Wilken.MultiplicativeFactorRemoval

/-!
# Genuine final-factor bounds for the printed insertion footnote

The original non-M guard makes the retained reduced MNF prefix nonempty.
Its actual descending factor order puts the removed last factor below the
last factor of that prefix. Actual canonical MNF uniqueness identifies the
prefix product's last factor. This is the factor inequality used with the
separate source3.21 bound on a computed headword's last value; it does not
assume that a non-M tracking word ends at its input value. Uncompiled.
-/

namespace Alexander313.Wilken.MultiplicativeFactorRemoval.Bounds

universe u

open MultiplicativeNormalForm MultiplicativeFactorRemoval MultiplicativePrincipalArithmetic

theorem source_last_le_prefix_last {α : Ordinal.{u}}
    (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : ¬IsMultiplicativePrincipal α) :
    lf α ≤ lf (factorProduct (factorPrefix (canonicalMNF α))) := by
  let xs := canonicalMNF α
  have hx : IsReducedMNF xs := canonicalMNF_reduced α
  have hpre : factorPrefix xs ≠ [] := nonmultiplicative_prefix_nonempty hα hp hm
  have hne : xs ≠ [] := by
    intro he
    exact hpre (by simp only [he, factorPrefix, List.reverse_nil, List.tail_nil])
  have hs := prefix_last_split xs hne
  have horder := hx.1.2
  rw [hs] at horder
  have hlast : lastFactor xs ≤ lastFactor (factorPrefix xs) :=
    (List.pairwise_append.mp horder).2.2 _ (lastFactor_mem _ hpre) _ List.mem_cons_self
  change lastFactor (canonicalMNF α) ≤
    lastFactor (canonicalMNF (factorProduct (factorPrefix (canonicalMNF α))))
  rw [source_prefix_canonicalMNF]
  exact hlast

theorem source_last_le_prefix_product {α : Ordinal.{u}}
    (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : ¬IsMultiplicativePrincipal α) :
    lf α ≤ factorProduct (factorPrefix (canonicalMNF α)) := by
  have hpre := nonmultiplicative_prefix_nonempty hα hp hm
  have hx := factorPrefix_reduced _ (canonicalMNF_reduced α)
  have hle := factorProduct_mem_le _ (fun a ha => (hx.1.1 a ha).1)
    _ (lastFactor_mem _ hpre)
  have hl := source_last_le_prefix_last hα hp hm
  simp only [lf, source_prefix_canonicalMNF] at hl
  exact hl.trans hle

end Alexander313.Wilken.MultiplicativeFactorRemoval.Bounds
