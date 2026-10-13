import Alexander313.Wilken.HereditaryNativeIotaInverse
import Alexander313.Wilken.HereditaryNativeIotaBaseChange

/-!
# The inverse retains the smaller original source restriction

Actual target Par below gamma yields actual public gamma payloads. Every
genuine bounded returned atom has all its full theta-zero support bounded
by its own payload value, which is below gamma. The shifted theta inverse
creates no new theta-zero nodes. Thus ALL original support, including the
hidden support in returned atoms, lies below gamma. No restriction,
inverse-admission or image oracle is supplied.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange.Image

open NativePublicBridge (contextCode contextCode_checked)

theorem atom_restricted_gamma (s g a p : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hp : parameterCheck (alphaCode s a) p = true)
    (hpg : parameterCheck (alphaCode s g) p = true) :
    Restricted s g (Inverse.atomTerm s p) := by
  have hs := Inverse.atom_spec s a p ha hp
  intro u hu
  have hle := Inverse.fullList_value_le_low _ _ u hs.1 hs.2.1 hs.2.2.1 hu
  rw [hs.2.2.2] at hle
  exact hle.trans_lt (by simpa only [alpha_base s g hg] using parameter_sound _ p hpg)

/-- The bound is on the actual target payloads, and source restriction is
a conclusion. Both target raw sums and hidden target theta arguments remain. -/
theorem lift_restricted_gamma (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hp : Payloads (alphaCode s g) t) : Restricted s g (Inverse.lift s t) := by
  revert ht hp
  induction t with
  | parameter p =>
    intro ht hp
    exact atom_restricted_gamma s g a p hg ha (NativeContext.checked_admissible _ _ ht).1 hp
  | sum t u iht ihu =>
    intro ht hp
    have hc := BaseTransformation.sum_checks _ t u ht
    exact (restricted_sum s g _ _).mpr ⟨iht hc.1 hp.1, ihu hc.2 hp.2⟩
  | theta k t ih =>
    intro ht hp
    exact (restricted_theta_succ s g k _).mpr
      (ih (BaseTransformation.theta_argument_check _ k t ht) hp)

theorem lift_par_restricted_gamma (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hp : BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t) :
    Restricted s g (Inverse.lift s t) :=
  lift_restricted_gamma s g a hg ha t ht
    ((BaseTransformation.parBounded_iff_payloads _ _ t ht (alphaCode_baseCheck s g hg)).mp hp)

theorem lift_sourceStar_gamma (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t)
    (hp : BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t) :
    sourceStar (contextCode s) (Inverse.lift s t) < interpretation (contextCode s) g :=
  (restricted_iff_sourceStar s g hg _ (Inverse.lift_checked s a ha t ht)
    (Inverse.lift_normal s a ha t ht hn)).mp (lift_par_restricted_gamma s g a hg ha t ht hp)

/-- The actual finite pi admission is derived from original target alpha
admission and the true chosen-presentation Par bound. -/
theorem target_pi_caller (s g a : Nat)
    (hg : rootCheck s g = true) (ha : rootCheck s a = true)
    (hga : interpretation (contextCode s) g < interpretation (contextCode s) a)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hp : BaseTransformation.ParBounded (alphaCode s a) (alphaCode s g) t) :
    BaseTransformation.inputCheck (alphaCode s a) (alphaCode s g) t.code = true := by
  exact (BaseTransformation.inputCheck_exact _ _ _).mpr
    ⟨by simpa only [checkCode_code] using ht, alphaCode_baseCheck s g hg,
      by simpa only [alpha_base s g hg, alpha_base s a ha] using hga,
      by simpa only [ThetaCourse.rawTree_code] using hp⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.BaseChange.Image
