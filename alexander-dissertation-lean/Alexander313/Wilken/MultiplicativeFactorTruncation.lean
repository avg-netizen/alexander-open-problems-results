import Alexander313.Wilken.MultiplicativeNormalForm

/-!
# Actual overlined multiplicative factor truncation

Definition 3.33 removes MNF factors strictly below beta. This module retains
the literal factors at least beta, in their original order, and takes their
actual ordered product. On a genuine reduced MNF the retained list is a finite
prefix, remains reduced, and has product at most the original principal.
Empty retention has product one. Nested retention uses the larger threshold.

The source caller has beta in M above one. Actual multiplicative closure of
that beta proves nonempty retention when beta is at most the original value.
The M condition is essential: beta>1 and beta<=alpha alone do not imply that
an individual factor reaches beta. The operation is overlined truncation,
not ordinary multiplication. No mu function, sk sequence, height decrease,
tracking algorithm, arithmetic contract or effectivity oracle is supplied.
All terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.MultiplicativeFactorTruncation

universe u

open MultiplicativeNormalForm MultiplicativePrincipalArithmetic

noncomputable def retain (β : Ordinal.{u}) (xs : List Ordinal.{u}) : List Ordinal.{u} := by
  classical
  exact xs.filter (fun a => decide (β ≤ a))

noncomputable def truncate (α β : Ordinal.{u}) : Ordinal.{u} :=
  factorProduct (retain β (canonicalMNF α))

theorem retain_nil (β : Ordinal.{u}) : retain β [] = [] := rfl

theorem retain_cons (β a : Ordinal.{u}) (xs : List Ordinal.{u}) :
    retain β (a :: xs) = if β ≤ a then a :: retain β xs else retain β xs := by
  classical
  by_cases h : β ≤ a <;> simp [retain, h]

theorem retain_mem (β a : Ordinal.{u}) (xs : List Ordinal.{u}) :
    a ∈ retain β xs ↔ a ∈ xs ∧ β ≤ a := by
  classical
  simp [retain]

theorem retain_all (β : Ordinal.{u}) (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, β ≤ a) : retain β xs = xs := by
  revert hx
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro hx
    rw [retain_cons, if_pos (hx a List.mem_cons_self), ih (fun b hb => hx b (List.mem_cons_of_mem _ hb))]

theorem retain_none (β : Ordinal.{u}) (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, a < β) : retain β xs = [] := by
  revert hx
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro hx
    rw [retain_cons, if_neg (not_le_of_gt (hx a List.mem_cons_self)),
      ih (fun b hb => hx b (List.mem_cons_of_mem _ hb))]

theorem retain_nil_iff (β : Ordinal.{u}) (xs : List Ordinal.{u}) :
    retain β xs = [] ↔ ∀ a ∈ xs, a < β := by
  constructor
  · intro h a ha
    apply lt_of_not_ge
    intro hle
    have hm := (retain_mem β a xs).mpr ⟨ha, hle⟩
    rw [h] at hm
    exact List.not_mem_nil hm
  · exact retain_none β xs

theorem retain_eq_self_iff (β : Ordinal.{u}) (xs : List Ordinal.{u}) :
    retain β xs = xs ↔ ∀ a ∈ xs, β ≤ a := by
  constructor
  · intro h a ha
    have hm : a ∈ retain β xs := by rw [h]; exact ha
    exact ((retain_mem β a xs).mp hm).2
  · exact retain_all β xs

theorem retain_nonempty_iff (β : Ordinal.{u}) (xs : List Ordinal.{u}) :
    retain β xs ≠ [] ↔ ∃ a ∈ xs, β ≤ a := by
  constructor
  · intro hn
    cases h : retain β xs with
    | nil => exact False.elim (hn h)
    | cons a as =>
      have hm : a ∈ retain β xs := by rw [h]; exact List.mem_cons_self
      exact ⟨a, (retain_mem β a xs).mp hm⟩
  · rintro ⟨a, ha, hβ⟩ h
    have hm := (retain_mem β a xs).mpr ⟨ha, hβ⟩
    rw [h] at hm
    exact List.not_mem_nil hm

theorem retain_pairwise (β : Ordinal.{u}) (xs : List Ordinal.{u})
    (hx : xs.Pairwise (fun a b => b ≤ a)) : (retain β xs).Pairwise (fun a b => b ≤ a) := by
  revert hx
  induction xs with
  | nil => intro _; exact List.Pairwise.nil
  | cons a xs ih =>
    intro hx
    have ht := List.pairwise_cons.mp hx
    rw [retain_cons]
    split_ifs with hβ
    · exact List.pairwise_cons.mpr ⟨fun b hb => ht.1 b ((retain_mem β b xs).mp hb).1, ih ht.2⟩
    · exact ih ht.2

theorem retain_reduced (β : Ordinal.{u}) {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) :
    IsReducedMNF (retain β xs) :=
  ⟨⟨fun a ha => hx.1.1 a ((retain_mem β a xs).mp ha).1, retain_pairwise β xs hx.1.2⟩,
    fun a ha => hx.2 a ((retain_mem β a xs).mp ha).1⟩

/-- A failed head test rejects the entire tail, because source factors descend. -/
theorem retain_prefix (β : Ordinal.{u}) (xs : List Ordinal.{u})
    (hx : xs.Pairwise (fun a b => b ≤ a)) :
    ∃ ys : List Ordinal.{u}, xs = retain β xs ++ ys ∧ ∀ a ∈ ys, a < β := by
  revert hx
  induction xs with
  | nil => intro _; exact ⟨[], rfl, by simp⟩
  | cons a xs ih =>
    intro hx
    have ht := List.pairwise_cons.mp hx
    by_cases hβ : β ≤ a
    · obtain ⟨ys, he, hs⟩ := ih ht.2
      refine ⟨ys, ?_, hs⟩
      rw [retain_cons, if_pos hβ]
      exact congrArg (List.cons a) he
    · have hsmall : ∀ b ∈ a :: xs, b < β := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact lt_of_not_ge hβ
        · exact (ht.1 b hb).trans_lt (lt_of_not_ge hβ)
      exact ⟨a :: xs, by rw [retain_none β (a :: xs) hsmall]; rfl, hsmall⟩

private theorem take_prefix (xs ys : List Ordinal.{u}) : (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change a :: (xs ++ ys).take xs.length = a :: xs
    exact congrArg (List.cons a) ih

/-- Literal numerical prefix length; factors are neither reordered nor replaced. -/
theorem retain_eq_take (β : Ordinal.{u}) (xs : List Ordinal.{u})
    (hx : xs.Pairwise (fun a b => b ≤ a)) : retain β xs = xs.take (retain β xs).length := by
  obtain ⟨ys, he, _⟩ := retain_prefix β xs hx
  have ht := (congrArg (fun zs => zs.take (retain β xs).length) he).trans (take_prefix _ _)
  exact ht.symm

theorem retain_threshold (β γ : Ordinal.{u}) (xs : List Ordinal.{u}) :
    retain γ (retain β xs) = retain (max β γ) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases hb : β ≤ a <;> by_cases hg : γ ≤ a <;>
      simp [retain_cons, hb, hg, max_le_iff, ih]

theorem retain_idempotent (β : Ordinal.{u}) (xs : List Ordinal.{u}) : retain β (retain β xs) = retain β xs := by
  simpa only [max_self] using retain_threshold β β xs

theorem retain_threshold_of_le {β γ : Ordinal.{u}} (h : β ≤ γ) (xs : List Ordinal.{u}) :
    retain γ (retain β xs) = retain γ xs := by
  simpa only [max_eq_right h] using retain_threshold β γ xs

theorem one_le_factorProduct (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, 1 ≤ a) : 1 ≤ factorProduct xs := by
  revert hx
  induction xs with
  | nil => intro _; exact le_rfl
  | cons a xs ih =>
    intro hx
    have h := mul_le_mul' (hx a List.mem_cons_self) (ih (fun b hb => hx b (List.mem_cons_of_mem _ hb)))
    simpa only [one_mul, factorProduct] using h

theorem factorProduct_mem_le (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, 1 ≤ a)
    (a : Ordinal.{u}) (ha : a ∈ xs) : a ≤ factorProduct xs := by
  revert hx ha
  induction xs with
  | nil => intro _ ha; exact False.elim (List.not_mem_nil ha)
  | cons b xs ih =>
    intro hx ha
    have ht := fun c hc => hx c (List.mem_cons_of_mem _ hc)
    rcases List.mem_cons.mp ha with rfl | ha
    · have h := mul_le_mul' (le_rfl : a ≤ a) (one_le_factorProduct xs ht)
      simpa only [mul_one, factorProduct] using h
    · have h := mul_le_mul' (hx b List.mem_cons_self) (le_rfl : factorProduct xs ≤ factorProduct xs)
      exact (ih ht ha).trans (by simpa only [one_mul, factorProduct] using h)

theorem retain_product_le (β : Ordinal.{u}) {xs : List Ordinal.{u}} (hx : IsReducedMNF xs) :
    factorProduct (retain β xs) ≤ factorProduct xs := by
  obtain ⟨ys, he, _⟩ := retain_prefix β xs hx.1.2
  have hys : ∀ a ∈ ys, 1 ≤ a := by
    intro a ha
    have hm : a ∈ xs := by rw [he]; exact List.mem_append_right _ ha
    exact (hx.2 a hm).le
  have h := mul_le_mul' (le_rfl : factorProduct (retain β xs) ≤ factorProduct (retain β xs))
    (one_le_factorProduct ys hys)
  calc
    factorProduct (retain β xs) ≤ factorProduct (retain β xs) * factorProduct ys := by
      simpa only [mul_one] using h
    _ = factorProduct (retain β xs ++ ys) := (factorProduct_append _ _).symm
    _ = factorProduct xs := congrArg factorProduct he.symm

theorem lastFactor_retain_ge (β : Ordinal.{u}) (xs : List Ordinal.{u}) (hn : retain β xs ≠ []) :
    β ≤ lastFactor (retain β xs) :=
  ((retain_mem β _ xs).mp (lastFactor_mem _ hn)).2

theorem truncate_reduced (α β : Ordinal.{u}) : IsReducedMNF (retain β (canonicalMNF α)) :=
  retain_reduced β (canonicalMNF_reduced α)

theorem truncate_pos_principal (α β : Ordinal.{u}) :
    0 < truncate α β ∧ Ordinal.IsPrincipal (· + ·) (truncate α β) :=
  isMNF_product_principal (truncate_reduced α β).1

theorem truncate_le {α : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α) (β : Ordinal.{u}) :
    truncate α β ≤ α := (retain_product_le β (canonicalMNF_reduced α)).trans_eq (factorProduct_canonicalMNF hα hp)

theorem truncate_eq_of_reducedMNF {α : Ordinal.{u}} {xs : List Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) (hx : IsReducedMNF xs) (hv : factorProduct xs = α) (β : Ordinal.{u}) :
    truncate α β = factorProduct (retain β xs) := by
  have he : canonicalMNF α = xs := reducedMNF_unique (canonicalMNF_reduced α) hx
    ((factorProduct_canonicalMNF hα hp).trans hv.symm)
  rw [truncate, he]

theorem canonicalMNF_truncate (α β : Ordinal.{u}) : canonicalMNF (truncate α β) = retain β (canonicalMNF α) :=
  reducedMNF_unique (canonicalMNF_reduced _) (truncate_reduced α β)
    (factorProduct_canonicalMNF (truncate_pos_principal α β).1 (truncate_pos_principal α β).2)

theorem truncate_threshold (α β γ : Ordinal.{u}) : truncate (truncate α β) γ = truncate α (max β γ) := by
  change factorProduct (retain γ (canonicalMNF (truncate α β))) =
    factorProduct (retain (max β γ) (canonicalMNF α))
  rw [canonicalMNF_truncate, retain_threshold]

theorem truncate_idempotent (α β : Ordinal.{u}) : truncate (truncate α β) β = truncate α β := by
  simpa only [max_self] using truncate_threshold α β β

theorem truncate_threshold_of_le (α : Ordinal.{u}) {β γ : Ordinal.{u}} (h : β ≤ γ) :
    truncate (truncate α β) γ = truncate α γ := by
  simpa only [max_eq_right h] using truncate_threshold α β γ

theorem truncate_antitone_threshold (α : Ordinal.{u}) {β γ : Ordinal.{u}} (h : β ≤ γ) : truncate α γ ≤ truncate α β := by
  rw [← truncate_threshold_of_le α h]
  exact truncate_le (truncate_pos_principal α β).1 (truncate_pos_principal α β).2 γ

theorem truncate_eq_one_iff (α β : Ordinal.{u}) : truncate α β = 1 ↔
    ∀ a ∈ canonicalMNF α, a < β := by
  exact (reducedMNF_product_one_iff (truncate_reduced α β)).trans (retain_nil_iff β (canonicalMNF α))

theorem truncate_one (β : Ordinal.{u}) : truncate (1 : Ordinal.{u}) β = 1 := by
  rw [truncate, canonicalMNF_one, retain_nil, factorProduct]

theorem truncate_eq_self {α : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (β : Ordinal.{u}) (hβ : ∀ a ∈ canonicalMNF α, β ≤ a) : truncate α β = α := by
  rw [truncate, retain_all β _ hβ]
  exact factorProduct_canonicalMNF hα hp

theorem truncate_zero {α : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α) : truncate α 0 = α :=
  truncate_eq_self hα hp 0 (fun _ _ => zero_le)

theorem truncate_unit_threshold {α : Ordinal.{u}} (hα : 0 < α)
    (hp : Ordinal.IsPrincipal (· + ·) α) : truncate α 1 = α :=
  truncate_eq_self hα hp 1 (fun a ha => ((canonicalMNF_reduced α).2 a ha).le)

/-- Source multiplicative closure forces a finite product of smaller factors
below beta. Empty product one needs the explicit source beta>1 condition. -/
theorem factorProduct_lt_source {β : Ordinal.{u}} (hm : IsMultiplicativePrincipal β) (hβ : 1 < β)
    (xs : List Ordinal.{u}) (hx : ∀ a ∈ xs, a < β) : factorProduct xs < β := by
  revert hx
  induction xs with
  | nil => intro _; exact hβ
  | cons a xs ih =>
    intro hx
    exact hm.2.2 (hx a List.mem_cons_self) (ih (fun b hb => hx b (List.mem_cons_of_mem _ hb)))

theorem retain_nonempty_source {β : Ordinal.{u}} (hm : IsMultiplicativePrincipal β) (hβ : 1 < β)
    (xs : List Ordinal.{u}) (hb : β ≤ factorProduct xs) : retain β xs ≠ [] := by
  intro hn
  exact (not_lt_of_ge hb) (factorProduct_lt_source hm hβ xs ((retain_nil_iff β xs).mp hn))

theorem truncate_nonempty_source {α β : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : IsMultiplicativePrincipal β) (hβ : 1 < β) (hb : β ≤ α) : retain β (canonicalMNF α) ≠ [] :=
  retain_nonempty_source hm hβ _ (hb.trans_eq (factorProduct_canonicalMNF hα hp).symm)

theorem truncate_ge_source {α β : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : IsMultiplicativePrincipal β) (hβ : 1 < β) (hb : β ≤ α) : β ≤ truncate α β := by
  have hn := truncate_nonempty_source hα hp hm hβ hb
  have ha := firstFactor_mem (retain β (canonicalMNF α)) hn
  have hcut := ((retain_mem β _ (canonicalMNF α)).mp ha).2
  exact hcut.trans (factorProduct_mem_le _
    (fun a ha => ((truncate_reduced α β).2 a ha).le) _ ha)

theorem truncate_lf_ge_source {α β : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : IsMultiplicativePrincipal β) (hβ : 1 < β) (hb : β ≤ α) : β ≤ lf (truncate α β) := by
  rw [lf, canonicalMNF_truncate]
  exact lastFactor_retain_ge β _ (truncate_nonempty_source hα hp hm hβ hb)

/-- The actual local overlined step of Definition 3.33. This does not
construct the source mu function or the height-controlled sk iteration. -/
theorem source_definition_3_33 {α β : Ordinal.{u}} (hα : 0 < α) (hp : Ordinal.IsPrincipal (· + ·) α)
    (hm : IsMultiplicativePrincipal β) (hβ : 1 < β) (hb : β ≤ α) :
    β ≤ truncate α β ∧ truncate α β ≤ α ∧ β ≤ lf (truncate α β) ∧
      ∃ ys : List Ordinal.{u}, canonicalMNF α = retain β (canonicalMNF α) ++ ys ∧
        (∀ a ∈ ys, a < β) ∧ IsReducedMNF (retain β (canonicalMNF α)) := by
  refine ⟨truncate_ge_source hα hp hm hβ hb, truncate_le hα hp β,
    truncate_lf_ge_source hα hp hm hβ hb, ?_⟩
  obtain ⟨ys, he, hs⟩ := retain_prefix β (canonicalMNF α) (canonicalMNF_reduced α).1.2
  exact ⟨ys, he, hs, truncate_reduced α β⟩

end Alexander313.Wilken.MultiplicativeFactorTruncation
