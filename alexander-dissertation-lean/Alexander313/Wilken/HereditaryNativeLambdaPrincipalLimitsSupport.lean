import Alexander313.Wilken.HereditaryNativeSourceChiPowers
import Alexander313.Wilken.HereditaryNativeIotaOrderInduction
import Alexander313.Wilken.HereditarySuccessorLimit

/-!
# Actual principal limits and the low lambda zero branch

The source class L is exactly omega powers with a proper-limit exponent.
The actual last ANF component detects successors, and the genuine low-collapse
exponent includes its epsilon-plus-finite correction. Original checked normal
theta arguments derive the strict-supremum branch; no limit, fixed-point or
branch-equivalence oracle is supplied. Uncompiled source candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.PrincipalLimits

/-- The literal source class L = {omega^eta | eta is a proper limit},
as defined in the source preliminaries; this is not root limitness. -/
def PrincipalLimit (α : Ordinal.{0}) : Prop :=
  ∃ η : Ordinal.{0}, Order.IsSuccLimit η ∧ Ordinal.omega0 ^ η = α

theorem omega_principalLimit_iff (η : Ordinal.{0}) :
    PrincipalLimit (Ordinal.omega0 ^ η) ↔ Order.IsSuccLimit η := by
  constructor
  · rintro ⟨γ, hγ, he⟩
    have hγη : γ = η := omegaPower_strictMono.injective he
    simpa only [hγη] using hγ
  · intro hη
    exact ⟨η, hη, rfl⟩

theorem epsilon_principalLimit (α : Ordinal.{0}) (hα : Ordinal.omega0 ^ α = α) :
    PrincipalLimit α := by
  have hprincipal : Ordinal.IsPrincipal (· + ·) α := by
    rw [← hα]
    exact Ordinal.isPrincipal_add_omega0_opow α
  exact ⟨α, Ordinal.isSuccLimit_of_isPrincipal_add
    (EpsilonOffsets.epsilon_one_lt hα) hprincipal, hα⟩

/-- An actual zero last exponent is exactly zero or a successor, derived
from the complete actual ANF rather than an input classifier. -/
theorem sourceZero_iff_not_limit (η : Ordinal.{0}) :
    Hereditary.LogEndZero.SourceZero η ↔ ¬ Order.IsSuccLimit η := by
  classical
  constructor
  · rintro (hz | he)
    · simpa only [hz, Ordinal.isSuccLimit_iff, ne_eq, not_true_eq_false,
        false_and, not_false_eq_true]
    · cases hw : (canonicalANF η).reverse with
      | nil =>
        have hf : (0 : Ordinal.{0}) = 1 := by
          simpa only [LogEnd.endValue, LogEnd.componentValue, Bool.cond_true, hw,
            List.getElem?_nil, Option.getD_none] using he
        exact False.elim (zero_ne_one hf)
      | cons a as =>
        have ha : a = 1 := by
          simpa only [LogEnd.endValue, LogEnd.componentValue, Bool.cond_true, hw,
            List.getElem?_cons_zero, Option.getD_some] using he
        have hword : canonicalANF η = as.reverse ++ [1] := by
          simpa only [List.reverse_reverse, List.reverse_cons, ha] using
            congrArg List.reverse hw
        have hv : principalSum as.reverse + 1 = η := by
          calc
            principalSum as.reverse + 1 = principalSum (as.reverse ++ [1]) := by
              simp only [principalSum_append, principalSum, add_zero]
            _ = principalSum (canonicalANF η) := congrArg principalSum hword.symm
            _ = η := principalSum_canonicalANF η
        intro hl
        have hs : ¬ Order.IsSuccPrelimit η :=
          (Hereditary.SuccessorLimit.successor_iff_exists η).mpr ⟨_, hv⟩
        exact hs hl.isSuccPrelimit
  · intro hn
    by_cases hz : η = 0
    · exact Or.inl hz
    · have hp : ¬ Order.IsSuccPrelimit η := fun hp =>
        hn (Ordinal.isSuccLimit_iff.mpr ⟨hz, hp⟩)
      obtain ⟨ξ, hξ⟩ := (Hereditary.SuccessorLimit.successor_iff_exists η).mp hp
      right
      rw [← hξ]
      exact SourceChi.Powers.endValue_successor ξ

theorem lastExponent_spec (η : Ordinal.{0}) :
    LogEnd.SourceLogSpec true η (Hereditary.SourceZeta.lastExponent η) := by
  classical
  by_cases hz : η = 0
  · simpa only [LogEnd.SourceLogSpec, hz, if_pos rfl, Hereditary.SourceZeta.lastExponent_zero]
  · have hne : canonicalANF η ≠ [] := by
      intro he
      have hv := principalSum_canonicalANF η
      simp only [he, principalSum] at hv
      exact hz hv.symm
    cases hw : (canonicalANF η).reverse with
    | nil => exact False.elim (hne (by simpa using congrArg List.reverse hw))
    | cons a as =>
      have hm : a ∈ canonicalANF η := List.mem_reverse.mp (by
        rw [hw]
        exact List.mem_cons_self)
      have hp := (canonicalANF_normal η).1 a hm
      obtain ⟨γ, hγ⟩ := (Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hp.2).resolve_left
        (ne_of_gt hp.1)
      have hend : LogEnd.endValue η = a := by
        simp only [LogEnd.endValue, LogEnd.componentValue, Bool.cond_true, hw,
          List.getElem?_cons_zero, Option.getD_some]
      simp only [LogEnd.SourceLogSpec, if_neg hz]
      change Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 (LogEnd.endValue η) = LogEnd.endValue η
      rw [hend, ← hγ, Ordinal.log_opow Ordinal.one_lt_omega0]

theorem lastExponent_zero_iff (η : Ordinal.{0}) :
    Hereditary.SourceZeta.lastExponent η = 0 ↔ ¬ Order.IsSuccLimit η :=
  (Hereditary.LogEndZero.sourceLogSpec_zero_iff η _ (lastExponent_spec η)).trans
    (sourceZero_iff_not_limit η)

theorem strict_iff_not_fixed (q : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta 0 t) = true) (hn : Comparison.Normal q t) :
    FixedPoint.SourceStrict q 0 t.code ↔ ¬ FixedPoint.SourceFixed q 0 t.code := by
  have hi := SourceChi.theta_argument_input q 0 t ht hn
  rw [← FixedPoint.strictCode_correct q 0 t.code hi,
    ← FixedPoint.fixedCode_correct q 0 t.code hi]
  simp only [FixedPoint.strictCode, hi, Bool.true_and, Bool.not_eq_true_eq_eq_false,
    Bool.eq_false_eq_not_eq_true]

/-- The actual low zero branch is equivalent to failure of proper-limit
exponenthood in the GENUINE low collapse formula, including fixed residuals
and every epsilon-plus-finite offset. -/
theorem low_zeta_zero_iff (q : Nat) (t : RelativeTerm Nat)
    (ht : check q (.theta 0 t) = true) (hn : Comparison.Normal q t)
    (hl : denote q t < omegaSequence (base q) 1) (hp : 0 < denote q t) :
    (if FixedPoint.SourceStrict q 0 t.code then
      Hereditary.SourceZeta.lastExponent (denote q t) else 0) = 0 ↔
        ¬ Order.IsSuccLimit (lowOmegaExponent (base q) (denote q t)) := by
  classical
  have hq := (Bool.and_eq_true.mp ht).1
  have hepsilon := (baseCheck_exact q).mp hq |>.2
  by_cases hoff : EpsilonFiniteAbove (base q) (denote q t)
  · have hnot : ¬ Order.IsSuccLimit (lowOmegaExponent (base q) (denote q t)) := by
      rw [lowOmegaExponent_of_offset _ _ hoff]
      exact fun h => Order.not_isSuccPrelimit_succ (denote q t)
        (by simpa only [Order.succ_eq_add_one] using h.isSuccPrelimit)
    have hz : (if FixedPoint.SourceStrict q 0 t.code then
        Hereditary.SourceZeta.lastExponent (denote q t) else 0) = 0 := by
      obtain ⟨ε, k, hτε, hε, hη⟩ := hoff
      cases k with
      | zero =>
        have hηε : denote q t = ε := by simpa only [Nat.cast_zero, add_zero] using hη
        have hf : FixedPoint.SourceFixed q 0 t.code := by
          simp only [FixedPoint.SourceFixed, FixedPoint.delta, FixedPoint.residual,
            interpretation_code, Ordinal.div_eq_zero_of_lt hl, mul_zero,
            Ordinal.mod_eq_of_lt hl, hηε]
          exact SourceChi.Powers.epsilon_low_sup_fixed (base q) ε hepsilon hτε hε
            (by simpa only [hηε] using hl)
        have hs : ¬ FixedPoint.SourceStrict q 0 t.code := fun hs =>
          (strict_iff_not_fixed q t ht hn).mp hs hf
        simp only [if_neg hs]
      | succ k =>
        have he : Hereditary.SourceZeta.lastExponent (denote q t) = 0 := by
          rw [hη, Nat.cast_succ, ← add_assoc, Hereditary.SourceZeta.lastExponent,
            SourceChi.Powers.endValue_successor, Ordinal.log_one_right]
        split_ifs <;> simp only [he]
    exact ⟨fun _ => hnot, fun _ => hz⟩
  · have hnf : ¬ FixedPoint.SourceFixed q 0 t.code := by
      intro hf
      have hε := SourceChi.Powers.fixed_low_epsilon q t ht hn hl hp hf
      exact hoff ⟨denote q t, 0, hε.2, hε.1, by simp only [Nat.cast_zero, add_zero]⟩
    have hs := (strict_iff_not_fixed q t ht hn).mpr hnf
    rw [if_pos hs, lowOmegaExponent_of_not_offset _ _ hoff,
      lowOmegaBase_of_epsilon _ hepsilon, Ordinal.isSuccLimit_add_iff]
    have hnz : denote q t ≠ 0 := ne_of_gt hp
    simpa only [hnz, false_and, or_false] using lastExponent_zero_iff (denote q t)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.PrincipalLimits
