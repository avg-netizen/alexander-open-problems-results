import Alexander313.Wilken.ProperCollapse

/-!
# The actual finite notation domains

Definition 2.5 and Lemma 2.6 of Wilken are matched by an inductive domain,
with the source's cardinal-sort restrictions on every collapsing call.
Corollary 2.8 is proved using the already constructed proper collapse:
local outputs can be absorbed into the next parameter segment.

These are semantic finite notation domains. Unique normal forms, the
public hereditary recursive-code domain and direct limits remain separate.
All proof terms are uncompiled candidates.
-/

namespace Alexander313.Wilken

/-- The literal inductive domain in Wilken Lemma 2.6. -/
inductive FiniteNotation (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal)
    (n m : Nat) : Ordinal → Prop where
  | parameter {ξ} : ξ < omega m → FiniteNotation omega theta n m ξ
  | add {ξ η} : FiniteNotation omega theta n m ξ →
      FiniteNotation omega theta n m η → FiniteNotation omega theta n m (ξ + η)
  | collapse {k ξ} : m ≤ k → k < n → ξ < omega (k + 2) →
      FiniteNotation omega theta n m ξ → FiniteNotation omega theta n m (theta k ξ)

/-- Definition 2.5 agrees with the closure grammar of Lemma 2.6. -/
theorem finiteNotation_iff_hull {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} (hm : m < n) (ξ : Ordinal) :
    FiniteNotation omega theta n m ξ ↔ Hull omega theta n m (omega (m + 2)) 0 ξ := by
  constructor
  · intro h
    induction h with
    | parameter h => exact .below_base h
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | collapse hmk hkn hsort _ ih =>
      obtain rfl | hmk := hmk.eq_or_lt
      · exact .«local» hsort ih
      · exact .higher hmk hkn hsort ih
  · intro h
    induction h with
    | below_base h => exact .parameter h
    | below_parameter h => exact False.elim ((not_lt_of_ge (zero_le)) h)
    | add _ _ ihξ ihη => exact .add ihξ ihη
    | higher hmk hkn hsort _ ih => exact .collapse hmk.le hkn hsort ih
    | «local» hξ _ ih => exact .collapse le_rfl hm hξ ih

/-- Tⁿₘ for m<n, with the source convention Tⁿₙ=Ωₙ. The auxiliary
definition at m>n is not used in any source correspondence theorem. -/
def sourceNotation (τ : Ordinal) (n m : Nat) (ξ : Ordinal) : Prop :=
  if m < n then FiniteNotation (omegaSequence τ) (sourceFiniteCollapse τ n) n m ξ
    else ξ < omegaSequence τ m

theorem sourceNotation_iff_hull (τ : Ordinal) (n m : Nat)
    (hm : m < n) (ξ : Ordinal) :
    sourceNotation τ n m ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m (omegaSequence τ (m + 2)) 0 ξ := by
  rw [sourceNotation, if_pos hm]
  exact finiteNotation_iff_hull hm ξ

/-- The endpoint hull is the union in Definition 2.5. -/
theorem sourceNotation_iff_bounded_hull (τ : Ordinal) (n m : Nat)
    (hm : m < n) (ξ : Ordinal) :
    sourceNotation τ n m ξ ↔ ∃ α < omegaSequence τ (m + 2),
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α 0 ξ := by
  rw [sourceNotation_iff_hull τ n m hm ξ]
  exact hull_limit_argument (omegaSequence_isSuccLimit τ (m + 1))

/-- All calls in a source hull stay in Cⁿₘ(0,Ωₘ₊₁). In the local case
the inductively established argument domain licenses proper collapse. -/
theorem source_hull_to_admissible (τ : Ordinal) (n m : Nat) (hm : m < n)
    {α β ξ : Ordinal} (hα : α ≤ omegaSequence τ (m + 2))
    (hβ : β ≤ omegaSequence τ (m + 1))
    (h : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α β ξ) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m 0 (omegaSequence τ (m + 1)) ξ := by
  induction h with
  | below_base h => exact .below_parameter (h.trans (omegaSequence_step τ m))
  | below_parameter h => exact .below_parameter (h.trans_le hβ)
  | add _ _ ihξ ihη => exact .add ihξ ihη
  | higher hmk hkn hsort _ ih => exact .higher hmk hkn hsort ih
  | «local» hξ _ ih =>
    exact .below_parameter (sourceFiniteCollapse_proper τ n m hm _ (hξ.trans_le hα) ih)

/-- Cⁿₘ(Ωₘ₊₂,Ωₘ₊₁)=Cⁿₘ(0,Ωₘ₊₁), the second equality in Corollary 2.8. -/
theorem source_hull_parameter_endpoint (τ : Ordinal) (n m : Nat) (hm : m < n) (ξ : Ordinal) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m (omegaSequence τ (m + 2))
        (omegaSequence τ (m + 1)) ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m 0 (omegaSequence τ (m + 1)) ξ :=
  ⟨source_hull_to_admissible τ n m hm le_rfl le_rfl,
    hull_mono (zero_le) le_rfl⟩

/-- Cⁿₘ(0,Ωₘ₊₁)=Tⁿₘ₊₁, including the terminal convention Tⁿₙ=Ωₙ. -/
theorem source_nextNotation_iff_hull (τ : Ordinal) (n m : Nat)
    (hm : m < n) (ξ : Ordinal) :
    sourceNotation τ n (m + 1) ξ ↔
      Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m 0 (omegaSequence τ (m + 1)) ξ := by
  by_cases hnext : m + 1 < n
  · rw [sourceNotation, if_pos hnext]
    constructor
    · intro h
      induction h with
      | parameter h => exact .below_parameter h
      | add _ _ ihξ ihη => exact .add ihξ ihη
      | collapse hmk hkn hsort _ ih =>
        exact .higher (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmk) hkn hsort ih
    · intro h
      induction h with
      | below_base h => exact .parameter (h.trans (omegaSequence_step τ m))
      | below_parameter h => exact .parameter h
      | add _ _ ihξ ihη => exact .add ihξ ihη
      | higher hmk hkn hsort _ ih => exact .collapse (Nat.succ_le_of_lt hmk) hkn hsort ih
      | «local» hξ _ ih => exact False.elim ((not_lt_of_ge (zero_le)) hξ)
  · have hterminal : n = m + 1 := by omega
    rw [sourceNotation, if_neg hnext]
    constructor
    · exact Hull.below_parameter
    · intro h
      induction h with
      | below_base h => exact h.trans (omegaSequence_step τ m)
      | below_parameter h => exact h
      | add _ _ ihξ ihη => exact omegaSequence_add_closed τ m ihξ ihη
      | higher hmk hkn hsort _ ih => exact False.elim (by omega)
      | «local» hξ _ ih => exact False.elim ((not_lt_of_ge (zero_le)) hξ)

/-- The inclusion Tⁿₘ⊆Tⁿₘ₊₁ in Corollary 2.8. -/
theorem sourceNotation_embeds_next (τ : Ordinal) (n m : Nat) (hm : m < n)
    {ξ : Ordinal} (hξ : sourceNotation τ n m ξ) : sourceNotation τ n (m + 1) ξ := by
  apply (source_nextNotation_iff_hull τ n m hm ξ).mpr
  apply source_hull_to_admissible τ n m hm le_rfl (zero_le)
  exact (sourceNotation_iff_hull τ n m hm ξ).mp hξ

/-- Actual notation membership provides the input domain of Lemma 2.7. -/
theorem sourceFiniteCollapse_proper_notation (τ : Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) (hsort : α < omegaSequence τ (m + 2))
    (hα : sourceNotation τ n (m + 1) α) :
    sourceFiniteCollapse τ n m α < omegaSequence τ (m + 1) :=
  sourceFiniteCollapse_proper τ n m hm α hsort
    ((source_nextNotation_iff_hull τ n m hm α).mp hα)

theorem sourceFiniteCollapse_argument_notation (τ : Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) (hsort : α < omegaSequence τ (m + 2))
    (hα : sourceNotation τ n (m + 1) α) :
    Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m α (sourceFiniteCollapse τ n m α) α :=
  finiteCollapse_arg_mem_of_lt hm α (sourceFiniteCollapse_proper_notation τ n m hm α hsort hα)

end Alexander313.Wilken
