import Alexander313.Wilken.Hulls
import Alexander313.Wilken.OmegaSequence

/-!
# Concrete finite-level collapsing functions

This is the hull/minimum construction of Wilken Definition 2.1. The
well-founded recursion order decreases `n - m` on higher-level calls and
decreases the ordinal argument on same-level calls. Values on irrelevant
levels are zero; no such value participates in the defining hull.

The upper-cardinal fallback is part of the source definition, rather than
an assumption that proper collapse has already been proved. The theorem
excluding that fallback on the source-admissible domain remains separate.
All declarations are candidate proof terms awaiting external compilation.
-/

namespace Alexander313.Wilken

open Order

/-- An actual, non-fallback candidate in Definition 2.1. -/
def CollapseCandidate (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal)
    (n m : Nat) (α β : Ordinal) : Prop :=
  β < omega (m + 1) ∧
    (∀ ξ, Hull omega theta n m α β ξ → ξ < omega (m + 1) → ξ < β) ∧
    Hull omega theta n m α β α

/-- This nonempty set includes the source's explicit fallback. -/
def collapseCandidates (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal)
    (n m : Nat) (α : Ordinal) : Set Ordinal :=
  {β | CollapseCandidate omega theta n m α β ∨ β = omega (m + 1)}

theorem collapseCandidates_nonempty (omega : Nat → Ordinal)
    (theta : Nat → Ordinal → Ordinal) (n m : Nat) (α : Ordinal) :
    (collapseCandidates omega theta n m α).Nonempty :=
  ⟨omega (m + 1), Or.inr rfl⟩

noncomputable def hullMinimum (omega : Nat → Ordinal)
    (theta : Nat → Ordinal → Ordinal) (n m : Nat) (α : Ordinal) : Ordinal :=
  sInf (collapseCandidates omega theta n m α)

theorem hullMinimum_mem (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal)
    (n m : Nat) (α : Ordinal) :
    CollapseCandidate omega theta n m α (hullMinimum omega theta n m α) ∨
      hullMinimum omega theta n m α = omega (m + 1) :=
  csInf_mem (collapseCandidates_nonempty omega theta n m α)

theorem hullMinimum_le (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal)
    (n m : Nat) (α : Ordinal) : hullMinimum omega theta n m α ≤ omega (m + 1) :=
  csInf_le' (Or.inr rfl : omega (m + 1) ∈ collapseCandidates omega theta n m α)

theorem hullMinimum_minimal {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {α β : Ordinal}
    (hβ : CollapseCandidate omega theta n m α β) :
    hullMinimum omega theta n m α ≤ β :=
  csInf_le' (Or.inl hβ : β ∈ collapseCandidates omega theta n m α)

theorem hullMinimum_family_congr {omega : Nat → Ordinal}
    {theta theta' : Nat → Ordinal → Ordinal} {n m : Nat} {α : Ordinal}
    (higher : ∀ k, m < k → k < n → ∀ ξ, ξ < omega (k + 2) →
      theta k ξ = theta' k ξ)
    («local» : ∀ ξ, ξ < α → theta m ξ = theta' m ξ) :
    hullMinimum omega theta n m α = hullMinimum omega theta' n m α := by
  have hc : collapseCandidates omega theta n m α =
      collapseCandidates omega theta' n m α := by
    ext β
    simp only [collapseCandidates, Set.mem_setOf_eq, CollapseCandidate]
    simp_rw [hull_family_congr higher «local»]
  exact congrArg sInf hc

/-- Descending level followed by increasing ordinal argument. -/
def collapseOrder (n : Nat) (p q : Fin n × Ordinal) : Prop :=
  Prod.Lex (· < ·) (· < ·) (n - p.1.val, p.2) (n - q.1.val, q.2)

theorem collapseOrder_wf (n : Nat) : WellFounded (collapseOrder n) :=
  InvImage.wf (fun p : Fin n × Ordinal => (n - p.1.val, p.2))
    (Nat.lt_wfRel.wf.prod_lex Ordinal.lt_wf)

theorem collapseOrder_higher (n : Nat) (p : Fin n × Ordinal)
    (k : Nat) (hmk : p.1.val < k) (hkn : k < n) (ξ : Ordinal) :
    collapseOrder n (⟨k, hkn⟩, ξ) p := by
  apply Prod.Lex.left
  change n - k < n - p.1.val
  have hm := p.1.isLt
  omega

theorem collapseOrder_local (n : Nat) (p : Fin n × Ordinal)
    (ξ : Ordinal) (hξ : ξ < p.2) : collapseOrder n (p.1, ξ) p :=
  Prod.Lex.right _ hξ

/-- A stage sees precisely the values already supplied by recursion. -/
noncomputable def recursorFamily (n : Nat) (p : Fin n × Ordinal)
    (ih : ∀ q, collapseOrder n q p → Ordinal) (k : Nat) (ξ : Ordinal) : Ordinal :=
  if hk : p.1.val < k ∧ k < n then
    ih (⟨k, hk.2⟩, ξ) (collapseOrder_higher n p k hk.1 hk.2 ξ)
  else if hk : k = p.1.val then
    if hξ : ξ < p.2 then ih (p.1, ξ) (collapseOrder_local n p ξ hξ) else 0
  else 0

noncomputable def collapseStep (omega : Nat → Ordinal) (n : Nat)
    (p : Fin n × Ordinal) (ih : ∀ q, collapseOrder n q p → Ordinal) : Ordinal :=
  hullMinimum omega (recursorFamily n p ih) n p.1.val p.2

noncomputable def finiteCollapseAux (omega : Nat → Ordinal) (n : Nat)
    (p : Fin n × Ordinal) : Ordinal :=
  (collapseOrder_wf n).fix (collapseStep omega n) p

/-- The actual finite fragment ϑⁿₘ. Only m<n is a source level. -/
noncomputable def finiteCollapse (omega : Nat → Ordinal) (n m : Nat)
    (α : Ordinal) : Ordinal :=
  if hm : m < n then finiteCollapseAux omega n (⟨m, hm⟩, α) else 0

/-- The completed family satisfies the literal source hull/minimum equation.
No collapsing-family contract is a parameter of this theorem. -/
theorem finiteCollapse_eq (omega : Nat → Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) :
    finiteCollapse omega n m α =
      hullMinimum omega (finiteCollapse omega n) n m α := by
  rw [finiteCollapse, dif_pos hm, finiteCollapseAux, WellFounded.fix_eq]
  change hullMinimum omega
      (recursorFamily n (⟨m, hm⟩, α)
        (fun q _ => finiteCollapseAux omega n q)) n m α =
    hullMinimum omega (finiteCollapse omega n) n m α
  apply hullMinimum_family_congr
  · intro k hmk hkn ξ hsort
    simp [recursorFamily, hmk, hkn, finiteCollapse]
  · intro ξ hξ
    have hnot : ¬ (m < m ∧ m < n) := by omega
    simp [recursorFamily, hnot, hξ, finiteCollapse, hm]

theorem finiteCollapse_le (omega : Nat → Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) : finiteCollapse omega n m α ≤ omega (m + 1) := by
  rw [finiteCollapse_eq omega n m hm α]
  exact hullMinimum_le omega (finiteCollapse omega n) n m α

theorem finiteCollapse_candidate_or_fallback (omega : Nat → Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) :
    CollapseCandidate omega (finiteCollapse omega n) n m α
        (finiteCollapse omega n m α) ∨
      finiteCollapse omega n m α = omega (m + 1) := by
  rw [finiteCollapse_eq omega n m hm α]
  exact hullMinimum_mem omega (finiteCollapse omega n) n m α

theorem finiteCollapse_minimal {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) {α β : Ordinal}
    (hβ : CollapseCandidate omega (finiteCollapse omega n) n m α β) :
    finiteCollapse omega n m α ≤ β := by
  rw [finiteCollapse_eq omega n m hm α]
  exact hullMinimum_minimal hβ

theorem finiteCollapse_base_le {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) (hbase : omega m ≤ omega (m + 1)) (α : Ordinal) :
    omega m ≤ finiteCollapse omega n m α := by
  rcases finiteCollapse_candidate_or_fallback omega n m hm α with h | h
  · by_contra! hsmall
    have inHull : Hull omega (finiteCollapse omega n) n m α
        (finiteCollapse omega n m α) (finiteCollapse omega n m α) :=
      .below_base hsmall
    exact (lt_irrefl _ (h.2.1 _ inHull h.1))
  · rw [h]
    exact hbase

/-- Wilken Lemma 2.3(a): the hull below the next cardinal is exactly
the initial segment determined by the chosen minimum, including fallback. -/
theorem finiteCollapse_hull_initial {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) (α ξ : Ordinal) :
    (Hull omega (finiteCollapse omega n) n m α (finiteCollapse omega n m α) ξ ∧
      ξ < omega (m + 1)) ↔ ξ < finiteCollapse omega n m α := by
  constructor
  · rintro ⟨hξ, hsort⟩
    rcases finiteCollapse_candidate_or_fallback omega n m hm α with h | h
    · exact h.2.1 ξ hξ hsort
    · simpa [h] using hsort
  · intro hξ
    exact ⟨.below_parameter hξ,
      hξ.trans_le (finiteCollapse_le omega n m hm α)⟩

theorem finiteCollapse_arg_mem_of_lt {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) (α : Ordinal)
    (hproper : finiteCollapse omega n m α < omega (m + 1)) :
    Hull omega (finiteCollapse omega n) n m α (finiteCollapse omega n m α) α := by
  rcases finiteCollapse_candidate_or_fallback omega n m hm α with h | h
  · exact h.2.2
  · exact False.elim (hproper.ne h)

theorem finiteCollapse_not_mem_of_lt {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) (α : Ordinal)
    (hproper : finiteCollapse omega n m α < omega (m + 1)) :
    ¬ Hull omega (finiteCollapse omega n) n m α (finiteCollapse omega n m α)
        (finiteCollapse omega n m α) := by
  intro h
  exact lt_irrefl _ ((finiteCollapse_hull_initial hm α _).mp ⟨h, hproper⟩)

/-- Wilken Lemma 2.3(b), additive closure part, proved from the minimum. -/
theorem finiteCollapse_add_closed {omega : Nat → Ordinal} {n m : Nat}
    (hm : m < n) (hsort : Ordinal.IsPrincipal (· + ·) (omega (m + 1))) (α : Ordinal) :
    Ordinal.IsPrincipal (· + ·) (finiteCollapse omega n m α) := by
  intro ξ η hξ hη
  apply (finiteCollapse_hull_initial hm α (ξ + η)).mp
  exact ⟨.add (.below_parameter hξ) (.below_parameter hη),
    hsort (hξ.trans_le (finiteCollapse_le omega n m hm α))
      (hη.trans_le (finiteCollapse_le omega n m hm α))⟩

/-- A completely constructed finite-level family over every actual base τ. -/
noncomputable def sourceFiniteCollapse (τ : Ordinal) (n m : Nat)
    (α : Ordinal) : Ordinal := finiteCollapse (omegaSequence τ) n m α

theorem sourceFiniteCollapse_bounds (τ : Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) :
    omegaSequence τ m ≤ sourceFiniteCollapse τ n m α ∧
      sourceFiniteCollapse τ n m α ≤ omegaSequence τ (m + 1) :=
  ⟨finiteCollapse_base_le hm (omegaSequence_step τ m).le α,
    finiteCollapse_le (omegaSequence τ) n m hm α⟩

theorem sourceFiniteCollapse_add_closed (τ : Ordinal) (n m : Nat)
    (hm : m < n) (α : Ordinal) :
    Ordinal.IsPrincipal (· + ·) (sourceFiniteCollapse τ n m α) :=
  finiteCollapse_add_closed hm (omegaSequence_add_closed τ m) α

theorem sourceFiniteCollapse_pos (τ : Ordinal) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) (α : Ordinal) :
    0 < sourceFiniteCollapse τ n m α := by
  have hbase : τ ≤ omegaSequence τ m :=
    (omegaSequence_strictMono τ).monotone (Nat.zero_le m)
  exact hτ.trans_le (hbase.trans (sourceFiniteCollapse_bounds τ n m hm α).1)

/-- In the zero-argument hull all higher collapsing values lie at or above
the next cardinal; only base-sized summands can yield a smaller result. -/
theorem source_hull_zero_small (τ : Ordinal) (n m : Nat)
    (hbase : Ordinal.IsPrincipal (· + ·) (omegaSequence τ m)) {ξ : Ordinal}
    (h : Hull (omegaSequence τ) (sourceFiniteCollapse τ n) n m 0
      (omegaSequence τ m) ξ) :
    ξ < omegaSequence τ (m + 1) → ξ < omegaSequence τ m := by
  induction h with
  | below_base h => exact fun _ => h
  | below_parameter h => exact fun _ => h
  | add _ _ ihξ ihη =>
    intro hsum
    exact hbase (ihξ (le_self_add.trans_lt hsum)) (ihη (le_add_self.trans_lt hsum))
  | @higher k η hmk hkn hsort _ ih =>
    intro hsmall
    have hupper : omegaSequence τ (m + 1) ≤ omegaSequence τ k :=
      (omegaSequence_strictMono τ).monotone (Nat.succ_le_of_lt hmk)
    have hvalue : omegaSequence τ k ≤ sourceFiniteCollapse τ n k η :=
      finiteCollapse_base_le hkn (omegaSequence_step τ k).le η
    exact False.elim (hsmall.not_ge (hupper.trans hvalue))
  | «local» hξ _ ih => exact False.elim (not_lt_of_ge zero_le hξ)

/-- The explicit zero value noted immediately after Definition 2.1.
The base hypotheses hold for τ=1 and every positive epsilon base. -/
theorem sourceFiniteCollapse_zero (τ : Ordinal) (hτ : 0 < τ)
    (hτadd : Ordinal.IsPrincipal (· + ·) τ) (n m : Nat) (hm : m < n) :
    sourceFiniteCollapse τ n m 0 = omegaSequence τ m := by
  have hbase : Ordinal.IsPrincipal (· + ·) (omegaSequence τ m) := by
    cases m with
    | zero => exact hτadd
    | succ m => exact omegaSequence_add_closed τ m
  have hpositive : 0 < omegaSequence τ m :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le m))
  have hc : CollapseCandidate (omegaSequence τ) (sourceFiniteCollapse τ n)
      n m 0 (omegaSequence τ m) :=
    ⟨omegaSequence_step τ m,
      fun ξ hξ hsort => source_hull_zero_small τ n m hbase hξ hsort,
      .below_base hpositive⟩
  exact le_antisymm (finiteCollapse_minimal hm hc)
    (sourceFiniteCollapse_bounds τ n m hm 0).1

end Alexander313.Wilken
