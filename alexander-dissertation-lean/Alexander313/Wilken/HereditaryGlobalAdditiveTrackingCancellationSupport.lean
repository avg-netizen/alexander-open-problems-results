import Alexander313.Wilken.HereditaryExactDivision
import Alexander313.Wilken.PublicEpsilonSourceDictionary

/-!
# Genuine lead-factor cancellation for global additive tracking

An epsilon gamma below a positive additive principal alpha really divides
alpha on the left. The proof constructs an ordinary omega-power quotient
from the actual exponent of alpha, using ordinal left subtraction. This
licenses the existing executing exact divider; no division witness or
quotient principal certificate is a supplied caller. Source-only, uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.CancellationSupport

universe u

/-- Ordinary omega powers and ordinal subtraction derive a genuine positive
additive-principal quotient before any numerical search runs. -/
theorem epsilon_principal_quotient {gamma alpha : Ordinal.{u}}
    (he : Ordinal.omega0 ^ gamma = gamma) (hp : 0 < alpha)
    (ha : Ordinal.IsPrincipal (· + ·) alpha) (hle : gamma ≤ alpha) :
    ∃ delta : Ordinal.{u}, 0 < delta ∧ Ordinal.IsPrincipal (· + ·) delta ∧
      gamma * delta = alpha := by
  obtain ⟨exponent, hexponent⟩ := positive_additivePrincipal_eq_omegaPower hp ha
  have hg : gamma ≤ exponent := omegaPower_strictMono.le_iff_le.mp
    (by simpa only [he] using hle.trans_eq hexponent)
  refine ⟨Ordinal.omega0 ^ (exponent - gamma),
    Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _, ?_⟩
  calc
    gamma * Ordinal.omega0 ^ (exponent - gamma) =
        Ordinal.omega0 ^ gamma * Ordinal.omega0 ^ (exponent - gamma) :=
      congrArg (fun x => x * Ordinal.omega0 ^ (exponent - gamma)) he.symm
    _ = Ordinal.omega0 ^ (gamma + (exponent - gamma)) := (Ordinal.opow_add _ _ _).symm
    _ = Ordinal.omega0 ^ exponent :=
      congrArg (fun x => Ordinal.omega0 ^ x) (Ordinal.add_sub_cancel_of_le hg)
    _ = alpha := hexponent.symm

def inputCheck (gamma alpha : Nat) : Bool := PublicEpsilonSourceDictionary.inputCheck gamma &&
  (Canonical.check alpha && (Principal.unionPrincipalCheck alpha && Canonical.less gamma alpha))

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (PublicEpsilonSourceDictionary.inputCheck_primrec.comp Primrec.fst)
    (Primrec.and.comp (Canonical.Effective.check_primrec.comp Primrec.snd)
      (Primrec.and.comp (Principal.unionPrincipalCheck_primrec.comp Primrec.snd)
        Canonical.Effective.less_primrec))).to₂

theorem inputCheck_exact (gamma alpha : Nat) : inputCheck gamma alpha = true ↔
    Canonical.check gamma = true ∧ Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
      Canonical.check alpha = true ∧ 0 < unionInterpretation alpha ∧
        Ordinal.IsPrincipal (· + ·) (unionInterpretation alpha) ∧
          unionInterpretation gamma < unionInterpretation alpha := by
  simp only [inputCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hg, hc, hp, hl⟩
    have hs := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hg
    have ha := (Principal.unionPrincipalCheck_exact alpha).mp hp
    exact ⟨hs.1, hs.2, hc, ha.2.1, ha.2.2, (Canonical.less_exact gamma alpha).mp hl |>.2.2⟩
  · rintro ⟨hg, he, hc, hp, ha, hl⟩
    exact ⟨(PublicEpsilonSourceDictionary.inputCheck_exact gamma).mpr ⟨hg, he⟩,
      hc, (Principal.unionPrincipalCheck_exact alpha).mpr ⟨Canonical.check_original hc, hp, ha⟩,
      (Canonical.less_exact gamma alpha).mpr ⟨hg, hc, hl⟩⟩

/-- The printed strict epsilon/principal caller supplies actual source
division existence and genuine positive divisor admission. -/
theorem division_caller (gamma alpha : Nat) (hi : inputCheck gamma alpha = true) :
    ExactDivision.SourceDomain gamma alpha := by
  obtain ⟨hg, he, hc, hp, ha, hl⟩ := (inputCheck_exact gamma alpha).mp hi
  obtain ⟨delta, hd, hprincipal, hproduct⟩ := epsilon_principal_quotient he hp ha hl.le
  exact ⟨Canonical.check_original hg, Canonical.check_original hc,
    (zero_lt_one : (0 : Ordinal.{0}) < 1).trans (EpsilonOffsets.epsilon_one_lt he), delta, hproduct⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.CancellationSupport
