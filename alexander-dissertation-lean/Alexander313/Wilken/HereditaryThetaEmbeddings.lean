import Alexander313.Wilken.HereditaryThetaSupport
import Alexander313.Wilken.HereditaryBaseArithmeticCodes

/-!
# Literal embeddings of every old hereditary low code

The earlier arithmetic-fragment embedding algorithm is ordinary repeated
parameter wrapping on all raw inputs. Here its admission and value theorems
are extended to the full original low grammar, including arbitrary theta
arguments. Recursively normal payloads remain normal. This allows two genuine
normal union codes to be compared at one common level; no normalization of an
arbitrary admitted input is asserted. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta

theorem lift_old_checked (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode (r + 1) (BaseArithmetic.liftCode c) = true := by
  rw [BaseArithmetic.liftCode, lowCheckCode_code]
  change (lowCheckCode r c && decide ((0 : Nat) ≤ 1)) = true
  simp only [hc, decide_true, Bool.true_and]
  decide

theorem lift_original_value (r c : Nat) :
    interpretation (r + 1) (BaseArithmetic.liftCode c) = interpretation r c := by
  rw [BaseArithmetic.liftCode, interpretation_code]
  rfl

theorem lift_normal (r c : Nat)
    (hn : Normal r ((decode c).getD (.parameter 0))) :
    Normal (r + 1) ((decode (BaseArithmetic.liftCode c)).getD (.parameter 0)) := by
  simpa only [BaseArithmetic.liftCode, decode_code, Option.getD_some,
    normal_parameter_succ] using hn

@[simp] theorem full_embed_zero (c : Nat) : BaseArithmetic.embedCode 0 c = c := rfl

@[simp] theorem full_embed_succ (steps c : Nat) :
    BaseArithmetic.embedCode (steps + 1) c =
      BaseArithmetic.liftCode (BaseArithmetic.embedCode steps c) := rfl

theorem embed_old_checked (r steps c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode (r + steps) (BaseArithmetic.embedCode steps c) = true := by
  induction steps with
  | zero => exact hc
  | succ steps ih =>
    rw [Nat.add_succ, full_embed_succ]
    exact lift_old_checked (r + steps) _ ih

theorem embed_original_value (r steps c : Nat) :
    interpretation (r + steps) (BaseArithmetic.embedCode steps c) = interpretation r c := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Nat.add_succ, full_embed_succ, lift_original_value]
    exact ih

theorem embed_normal (r steps c : Nat)
    (hn : Normal r ((decode c).getD (.parameter 0))) :
    Normal (r + steps) ((decode (BaseArithmetic.embedCode steps c)).getD (.parameter 0)) := by
  induction steps with
  | zero => exact hn
  | succ steps ih =>
    rw [Nat.add_succ, full_embed_succ]
    exact lift_normal (r + steps) _ ih

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta
