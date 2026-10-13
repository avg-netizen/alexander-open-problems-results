import Alexander313.Wilken.LowCollapseArithmetic
import Alexander313.Wilken.HereditaryPublicCodes

/-!
# Principal arithmetic of the actual iterated bases

The actual global initial-segment identity gives additive closure of every
global boundary. Hence the previously constructed finite bases are positive
additive principals. Actual finite/global coherence supplies their zero
collapse values; the auxiliary outside-domain zero is never used.

Low successor arithmetic is also transported to genuine global calls. These
facts do not prove epsilon status, the prescribed υ indexing, Lemma 2.4's
full non-epsilon enumeration, or an executable hereditary comparator.
Proof terms await external compilation.
-/

namespace Alexander313.Wilken

theorem globalBoundary_add_closed (τ : Ordinal.{0}) (hτ : 0 < τ) (m : Nat) :
    Ordinal.IsPrincipal (· + ·) (globalBoundary τ m) := by
  intro α β hα hβ
  have ha := (globalNotation_low_iff_lt_boundary τ hτ m α).mpr hα
  have hb := (globalNotation_low_iff_lt_boundary τ hτ m β).mpr hβ
  exact (globalNotation_low_iff_lt_boundary τ hτ m (α + β)).mp
    ⟨.add ha.1 hb.1, omegaSequence_add_closed τ m ha.2 hb.2⟩

/-- Zero is in the real next-boundary domain. -/
theorem globalCollapse_zero (τ : Ordinal.{0}) (hτ : 0 < τ)
    (hτadd : Ordinal.IsPrincipal (· + ·) τ) (m : Nat) :
    globalCollapse τ m 0 = omegaSequence τ m := by
  have hpositive : 0 < omegaSequence τ (m + 1) :=
    hτ.trans_le ((omegaSequence_strictMono τ).monotone (Nat.zero_le (m + 1)))
  have hzero : (0 : Ordinal.{0}) < globalBoundary τ (m + 1) :=
    hpositive.trans (globalBoundary_base_lt τ hτ (m + 1))
  let n := globalFragment τ m 0 hzero
  have hm : m < n := by
    have h := globalFragment_gt τ m 0 hzero
    omega
  rw [globalCollapse_finite_agreement τ hτ n m hm 0
    (globalFragment_bound τ m 0 hzero)]
  exact sourceFiniteCollapse_zero τ hτ hτadd n m hm

/-- Low successor inputs are inside the real next-boundary domain because
that boundary lies strictly above the next cardinal. -/
theorem globalCollapse_succ_eq_nextAdditivePrincipal (τ : Ordinal.{0})
    (hτ : 0 < τ) (m : Nat) (α : Ordinal.{0})
    (hα : α < omegaSequence τ (m + 1)) :
    globalCollapse τ m (α + 1) =
      nextAdditivePrincipal (globalCollapse τ m α) := by
  have hsucc : α + 1 < omegaSequence τ (m + 1) :=
    (omegaSequence_isSuccLimit τ m).add_one_lt hα
  have hglobal : α + 1 < globalBoundary τ (m + 1) :=
    hsucc.trans (globalBoundary_base_lt τ hτ (m + 1))
  let n := globalFragment τ m (α + 1) hglobal
  have hm : m < n := by
    have h := globalFragment_gt τ m (α + 1) hglobal
    omega
  have hbound := globalFragment_bound τ m (α + 1) hglobal
  rw [globalCollapse_finite_agreement τ hτ n m hm (α + 1) hbound,
    globalCollapse_finite_agreement τ hτ n m hm α ((lt_add_one α).trans hbound)]
  exact sourceFiniteCollapse_succ_eq_nextAdditivePrincipal τ n m hm α hα

namespace RelativeTerm.Hereditary

theorem finiteBase_add_closed (r : Nat) :
    Ordinal.IsPrincipal (· + ·) (finiteBase r) := by
  cases r with
  | zero =>
    intro α β hα hβ
    have ha : α = 0 := by simpa [finiteBase_zero] using hα
    have hb : β = 0 := by simpa [finiteBase_zero] using hβ
    simpa only [ha, hb, zero_add] using hα
  | succ r => exact globalBoundary_add_closed (finiteBase r) (finiteBase_pos r) 0

theorem finiteBase_collapse_zero (r m : Nat) :
    globalCollapse (finiteBase r) m 0 = omegaSequence (finiteBase r) m :=
  globalCollapse_zero (finiteBase r) (finiteBase_pos r) (finiteBase_add_closed r) m

@[simp] theorem finiteBase_collapse_zero_base (r : Nat) :
    globalCollapse (finiteBase r) 0 0 = finiteBase r := by
  simpa only [omegaSequence_zero] using finiteBase_collapse_zero r 0

end RelativeTerm.Hereditary

end Alexander313.Wilken
