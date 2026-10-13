import Alexander313.Wilken.PublicEpsilonNativePowerBaseChangeSupport

/-!
# Actual omega power preserves the original smaller-base payload domain

The original raw LOW source word and its chosen-presentation atomic-stop
Par cutoff derive admission at the smaller coded epsilon. Actual numerical
power branch agreement then gives a genuinely checked target output. Its
full syntactic Payloads cutoff, and hence the original Par cutoff, follow
from that checker. The actual pi caller and exact executing pi/power
equation are constructed. No output cutoff, admission, power naturality or
presentation-invariance oracle is supplied. Source-only uncompiled proofs.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers.BaseChange

open ThetaCourse
open BaseTransformation (ParBounded)

/-- Original chosen-presentation Par supplies the real second-context
caller for the SAME raw finite word. -/
theorem target_low (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    lowCheckCode v c = true := by
  have hqc := (Bool.and_eq_true.mp hc).1
  have hqt := Arithmetic.raw_checked q c hqc
  have hpayload := (BaseTransformation.parBounded_iff_payloads q v _ hqt hv).mp hp
  have hvt := BaseTransformation.check_change q v _ hqt hv hpayload
  have hvc : checkCode v c = true := by
    obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hqc
    simpa only [← he, rawTree_code, checkCode_code] using hvt
  exact Bool.and_eq_true.mpr ⟨hvc, (Bool.and_eq_true.mp hc).2⟩

/-- ALL original raw LOW terms satisfying the actual source Par cutoff
have literally equal executing omega-power codes at the two bases. -/
theorem powerCode_change (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    powerCode q c = powerCode v c :=
  powerCode_context q v c hc (target_low q v c hc hv hp)

/-- This FULL hidden payload cutoff is derived from the actual target
power checker, rather than inferred from ordinal-value equality. -/
theorem powerCode_payloads (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    Payloads v (rawTree (powerCode q c)) := by
  have ht := powerCode_spec v c (target_low q v c hc hv hp)
  have htarget : checkCode v (powerCode q c) = true := by
    rw [powerCode_change q v c hc hv hp]
    exact (Bool.and_eq_true.mp ht.1).1
  exact (checked_admissible v _ (Arithmetic.raw_checked v _ htarget)).1

theorem powerCode_parBounded (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hp : ParBounded q v (rawTree c)) :
    ParBounded q v (rawTree (powerCode q c)) := by
  have hsource := (Bool.and_eq_true.mp (powerCode_spec q c hc).1).1
  exact (BaseTransformation.parBounded_iff_payloads q v _
    (Arithmetic.raw_checked q _ hsource) hv).mpr (powerCode_payloads q v c hc hv hp)

theorem input_pi_caller (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) : BaseTransformation.inputCheck q v c = true :=
  (BaseTransformation.inputCheck_exact q v c).mpr
    ⟨(Bool.and_eq_true.mp hc).1, hv, hl, hp⟩

theorem output_pi_caller (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    BaseTransformation.inputCheck q v (powerCode q c) = true :=
  (BaseTransformation.inputCheck_exact q v _).mpr
    ⟨(Bool.and_eq_true.mp (powerCode_spec q c hc).1).1, hv, hl,
      powerCode_parBounded q v c hc hv hp⟩

/-- The real executing finite pi map commutes with the real finite
omega-power producer on the complete original smaller-payload domain. -/
theorem piCode_powerCode (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    BaseTransformation.piCode q v (powerCode q c) =
      powerCode v (BaseTransformation.piCode q v c) := by
  rw [BaseTransformation.piCode_eq q v _ (output_pi_caller q v c hc hv hl hp),
    BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp)]
  exact powerCode_change q v c hc hv hp

theorem piCode_power_value (q v c : Nat) (hc : lowCheckCode q c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hp : ParBounded q v (rawTree c)) :
    interpretation v (BaseTransformation.piCode q v (powerCode q c)) =
      Ordinal.omega0 ^ interpretation v (BaseTransformation.piCode q v c) := by
  rw [piCode_powerCode q v c hc hv hl hp,
    BaseTransformation.piCode_eq q v c (input_pi_caller q v c hc hv hl hp)]
  exact (powerCode_spec v c (target_low q v c hc hv hp)).2.2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers.BaseChange
