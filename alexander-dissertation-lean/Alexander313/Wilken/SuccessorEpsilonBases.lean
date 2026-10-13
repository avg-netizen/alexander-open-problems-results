import Alexander313.Wilken.CollapseExponentiation
import Alexander313.Wilken.FiniteUpsilonDomain

/-!
# Actual successor bases belong to the source epsilon class

The low collapse exponentiation bound and genuine initial-segment collapse
closure prove ordinary omega-power closure. The actual principal boundary
must therefore equal omega raised to itself. This establishes the source's
literal epsilon condition, without an epsilon-base or arithmetic-fidelity
premise. In particular the actual finite bases are one or epsilon, and every
positive zero-started finite upsilon value is epsilon.

The omega supremum is also an actual omega fixed point: every smaller
argument is below a finite epsilon base, and the supremum is additively
principal. No named-epsilon enumeration, source tracking, reflection or
transfinite upsilon construction is asserted. Proof terms are uncompiled.
-/

namespace Alexander313.Wilken

/-- The source's literal epsilon-or-one class supplies actual positivity. -/
theorem epsilon_or_one_pos {τ : Ordinal.{0}}
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) : 0 < τ := by
  rcases hτ with rfl | hτ
  · exact zero_lt_one
  · rw [← hτ]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos

/-- The source class also supplies the additive-principal premise used by
the actual zero-collapse equation, rather than assuming that premise anew. -/
theorem epsilon_or_one_add_closed {τ : Ordinal.{0}}
    (hτ : τ = 1 ∨ Ordinal.omega0 ^ τ = τ) : Ordinal.IsPrincipal (· + ·) τ := by
  rcases hτ with rfl | hτ
  · simpa using Ordinal.isPrincipal_add_omega0_opow (0 : Ordinal.{0})
  · rw [← hτ]
    exact Ordinal.isPrincipal_add_omega0_opow _

/-- The real finite low initial segment is closed under its own collapsing
function. Both the constructor's notation and its proper range are derived. -/
theorem finiteBoundary_low_collapse_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {α : Ordinal.{0}} (hα : α < finiteBoundary τ n m) :
    sourceFiniteCollapse τ n m α < finiteBoundary τ n m := by
  have ha := (source_finite_notation_low_iff_lt_boundary τ hτ n m hm α).mpr hα
  have hsort : α < omegaSequence τ (m + 2) :=
    ha.2.trans (omegaSequence_step τ (m + 1))
  have hbody := ha.1
  have hnotation : sourceNotation τ n m (sourceFiniteCollapse τ n m α) := by
    rw [sourceNotation, if_pos hm] at hbody ⊢
    exact .collapse le_rfl hm hsort hbody
  have hsmall : sourceFiniteCollapse τ n m α < omegaSequence τ (m + 1) :=
    sourceFiniteCollapse_proper_notation τ n m hm α hsort
      (sourceNotation_embeds_next τ n m hm ha.1)
  exact (source_finite_notation_low_iff_lt_boundary τ hτ n m hm _).mp
    ⟨hnotation, hsmall⟩

theorem finiteBoundary_omegaPower_closed (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) {α : Ordinal.{0}} (hα : α < finiteBoundary τ n m) :
    Ordinal.omega0 ^ α < finiteBoundary τ n m :=
  (sourceFiniteCollapse_low_omegaPower_le τ n m hm α
    (hα.trans (finiteBoundary_lt_cardinal τ hτ n m hm))).trans_lt
      (finiteBoundary_low_collapse_closed τ hτ n m hm hα)

theorem finiteBoundary_omegaPower_eq_self (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n m : Nat) (hm : m < n) :
    Ordinal.omega0 ^ finiteBoundary τ n m = finiteBoundary τ n m :=
  omegaPower_eq_self_of_principal_closed
    ((zero_le : 0 ≤ omegaSequence τ m).trans_lt (finiteBoundary_base_lt τ hτ n m hm))
    (finiteBoundary_add_closed τ hτ n m hm)
    (fun _ h => finiteBoundary_omegaPower_closed τ hτ n m hm h)

/-- The duplicated terminal endpoint is included; auxiliary fragments with
n=0 or a level above n are not used as source boundaries. -/
theorem finiteBoundary_omegaPower_eq_self_of_le (τ : Ordinal.{0}) (hτ : 0 < τ)
    (n : Nat) (hn : 0 < n) (m : Nat) (hm : m ≤ n) :
    Ordinal.omega0 ^ finiteBoundary τ n m = finiteBoundary τ n m := by
  rcases hm.eq_or_lt with hmn | hmn
  · subst m
    rw [finiteBoundary_terminal τ n hn]
    exact finiteBoundary_omegaPower_eq_self τ hτ n (n - 1) (by omega)
  · exact finiteBoundary_omegaPower_eq_self τ hτ n m hmn

/-- Every smaller argument has its ordinary omega power strictly below
the actual terminal boundary. -/
theorem terminalBoundary_omegaPower_closed (τ : Ordinal.{0}) (m : Nat)
    {α : Ordinal.{0}} (hα : α < terminalBoundary τ m) :
    Ordinal.omega0 ^ α < terminalBoundary τ m :=
  (sourceFiniteCollapse_low_omegaPower_le τ (m + 1) m (Nat.lt_succ_self m)
    α (hα.trans (terminalBoundary_lt_cardinal τ m))).trans_lt
      (terminalBoundary_collapse_closed τ m hα)

/-- Literal epsilon status of the independently constructed terminal
boundary, valid without a source epsilon assumption on its starting base. -/
theorem terminalBoundary_omegaPower_eq_self (τ : Ordinal.{0}) (m : Nat) :
    Ordinal.omega0 ^ terminalBoundary τ m = terminalBoundary τ m :=
  omegaPower_eq_self_of_principal_closed (terminalBoundary_pos τ m)
    (terminalBoundary_add_closed τ m) (fun _ h => terminalBoundary_omegaPower_closed τ m h)

/-- Actual global collapse closure and finite/global agreement give ordinary
omega-power closure throughout the real global initial segment. -/
theorem globalBoundary_omegaPower_closed (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat)
    {α : Ordinal.{0}} (hα : α < globalBoundary τ m) :
    Ordinal.omega0 ^ α < globalBoundary τ m :=
  (globalCollapse_low_omegaPower_le τ hτ m α
    (hα.trans (globalBoundary_lt_cardinal τ hτ m))).trans_lt
      (globalBoundary_collapse_closed τ hτ m hα)

/-- Every actual successor global base satisfies the source's literal
epsilon definition, omega raised to the base equals the base. -/
theorem globalBoundary_omegaPower_eq_self (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    Ordinal.omega0 ^ globalBoundary τ m = globalBoundary τ m :=
  omegaPower_eq_self_of_principal_closed
    ((zero_le : 0 ≤ omegaSequence τ m).trans_lt (globalBoundary_base_lt τ hτ m))
    (globalBoundary_add_closed τ hτ m) (fun _ h => globalBoundary_omegaPower_closed τ hτ m h)

namespace RelativeTerm.Hereditary

theorem finiteBase_strictMono : StrictMono finiteBase :=
  strictMono_nat_of_lt_succ finiteBase_step

theorem finiteBase_succ_omegaPower_closed (r : Nat) {α : Ordinal.{0}}
    (hα : α < finiteBase (r + 1)) : Ordinal.omega0 ^ α < finiteBase (r + 1) :=
  globalBoundary_omegaPower_closed (finiteBase r) (finiteBase_pos r) 0 hα

theorem finiteBase_succ_omegaPower_eq_self (r : Nat) :
    Ordinal.omega0 ^ finiteBase (r + 1) = finiteBase (r + 1) :=
  globalBoundary_omegaPower_eq_self (finiteBase r) (finiteBase_pos r) 0

/-- Actual E union {1} membership for every previously constructed finite
base. The zero-index base is one; all later bases are literal epsilons. -/
theorem finiteBase_epsilon_or_one (r : Nat) :
    finiteBase r = 1 ∨ Ordinal.omega0 ^ finiteBase r = finiteBase r := by
  cases r with
  | zero => exact Or.inl finiteBase_zero
  | succ r => exact Or.inr (finiteBase_succ_omegaPower_eq_self r)

/-- Principal closure of the actual finite-base supremum. -/
theorem finiteBaseLimit_add_closed :
    Ordinal.IsPrincipal (· + ·) finiteBaseLimit := by
  intro α β hα hβ
  obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.mp hα
  obtain ⟨j, hj⟩ := Ordinal.lt_iSup_iff.mp hβ
  let r := max i j
  have hi' : α < finiteBase r :=
    hi.trans_le (finiteBase_strictMono.monotone (le_max_left i j))
  have hj' : β < finiteBase r :=
    hj.trans_le (finiteBase_strictMono.monotone (le_max_right i j))
  exact ((finiteBase_add_closed r) hi' hj').trans_le (Ordinal.le_iSup finiteBase r)

theorem finiteBaseLimit_omegaPower_closed {α : Ordinal.{0}}
    (hα : α < finiteBaseLimit) : Ordinal.omega0 ^ α < finiteBaseLimit := by
  obtain ⟨r, hr⟩ := Ordinal.lt_iSup_iff.mp hα
  have hnext : α < finiteBase (r + 1) := hr.trans (finiteBase_step r)
  exact (finiteBase_succ_omegaPower_closed r hnext).trans_le
    (Ordinal.le_iSup finiteBase (r + 1))

theorem finiteBaseLimit_omegaPower_eq_self :
    Ordinal.omega0 ^ finiteBaseLimit = finiteBaseLimit :=
  omegaPower_eq_self_of_principal_closed finiteBaseLimit_pos finiteBaseLimit_add_closed
    (fun _ h => finiteBaseLimit_omegaPower_closed h)

end RelativeTerm.Hereditary

/-- The independently defined source extension, including its literal
zero-to-one convention, has genuine epsilon status. -/
theorem sourceBaseExtension_omegaPower_eq_self (τ : Ordinal.{0}) :
    Ordinal.omega0 ^ sourceBaseExtension τ = sourceBaseExtension τ := by
  rw [sourceBaseExtension_eq_globalBoundary]
  exact globalBoundary_omegaPower_eq_self (sourceStartingBase τ) (sourceStartingBase_pos τ) 0

theorem sourceUpsilonFinite_succ_omegaPower_eq_self (r : Nat) :
    Ordinal.omega0 ^ sourceUpsilonFinite (r + 1) = sourceUpsilonFinite (r + 1) :=
  sourceBaseExtension_omegaPower_eq_self (sourceUpsilonFinite r)

/-- Zero is the indexing endpoint, while every actual source starting base
for this finite recurrence belongs to E union {1}. -/
theorem sourceUpsilonFinite_startingBase_epsilon_or_one (r : Nat) :
    sourceStartingBase (sourceUpsilonFinite r) = 1 ∨
      Ordinal.omega0 ^ sourceStartingBase (sourceUpsilonFinite r) =
        sourceStartingBase (sourceUpsilonFinite r) := by
  cases r with
  | zero => exact Or.inl (by rw [sourceUpsilonFinite_zero, sourceStartingBase_zero])
  | succ r =>
    rw [sourceStartingBase_of_pos _ (sourceUpsilonFinite_pos r)]
    exact Or.inr (sourceUpsilonFinite_succ_omegaPower_eq_self r)

theorem sourceUpsilonOmega_omegaPower_eq_self :
    Ordinal.omega0 ^ sourceUpsilonOmega = sourceUpsilonOmega := by
  rw [sourceUpsilonOmega_eq_finiteBaseLimit]
  exact RelativeTerm.Hereditary.finiteBaseLimit_omegaPower_eq_self

end Alexander313.Wilken
