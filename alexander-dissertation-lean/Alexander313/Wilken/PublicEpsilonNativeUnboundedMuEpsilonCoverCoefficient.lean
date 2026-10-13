import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSource
import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaOrderSupport

/-!
# Genuine epsilon covers detect the actual returned mu coefficient

The corrected finite tail in the real mu exponent cannot create a new
epsilon lower bound. Hence an epsilon covered by the independently
executing mu is already bounded by its actual returned LOW coefficient.
If that epsilon is above the root, genuine iota base-cut reflection also
forces the ORIGINAL coefficient to be at least the original root. This
supplies actual coefficient callers for a later comparison; no comparison
between two roots, noncrossing law or mts lexical optimum is asserted.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.EpsilonCoverCoefficient

theorem epsilon_le_add_nat_iff (epsilon coefficient : Ordinal.{0}) (n : Nat)
    (he : Ordinal.omega0 ^ epsilon = epsilon) :
    epsilon ≤ coefficient + (n : Ordinal.{0}) ↔ epsilon ≤ coefficient := by
  have hp := EpsilonOffsets.epsilon_pos_principal he
  have hw : Ordinal.omega0 ≤ epsilon := by
    calc
      Ordinal.omega0 = Ordinal.omega0 ^ (1 : Ordinal.{0}) := (Ordinal.opow_one _).symm
      _ ≤ Ordinal.omega0 ^ epsilon :=
        omegaPower_strictMono.monotone (EpsilonOffsets.epsilon_one_lt he).le
      _ = epsilon := he
  constructor
  · intro h
    apply le_of_not_gt
    intro hc
    exact (hp.2 hc ((Ordinal.natCast_lt_omega0 n).trans_le hw)).not_ge h
  · intro h
    exact h.trans le_self_add

theorem epsilon_le_power_add_nat_iff (epsilon coefficient : Ordinal.{0}) (n : Nat)
    (he : Ordinal.omega0 ^ epsilon = epsilon) :
    epsilon ≤ Ordinal.omega0 ^ (coefficient + (n : Ordinal.{0})) ↔
      epsilon ≤ coefficient := by
  constructor
  · intro h
    have hx : epsilon ≤ coefficient + (n : Ordinal.{0}) :=
      (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mp (by simpa only [he] using h)
    exact (epsilon_le_add_nat_iff epsilon coefficient n he).mp hx
  · intro h
    have hx : Ordinal.omega0 ^ epsilon ≤
        Ordinal.omega0 ^ (coefficient + (n : Ordinal.{0})) :=
      omegaPower_strictMono.monotone (h.trans le_self_add)
    simpa only [he] using hx

/-- The actual original-source LOW coefficient and actual finite tail,
with every producer caller derived from the unchanged original mu guard. -/
theorem sourceValue_power_returnedCoefficient (q root : Nat)
    (ha : Mu.inputCheck q root = true) :
    Mu.sourceValue q root = Ordinal.omega0 ^
      (interpretation q (MuSource.returnedCoefficient q root) +
        (MuSource.tail q root : Ordinal.{0})) := by
  have hc := MuSource.returnedCoefficient_low q root ha
  have ht := OmegaPowerHeight.finiteTailCode_spec q (MuSource.returnedCoefficient q root)
    (MuSource.tail q root) hc
  have he := MuSource.exponentCode_spec q root ha
  calc
    Mu.sourceValue q root = interpretation q (MuSource.sourceCode q root) :=
      (MuSource.source_definition_3_6 q root ha).symm
    _ = Ordinal.omega0 ^ interpretation q (MuSource.exponentCode q root) := by
      rw [MuSource.sourceCode_literal q root ha, (OmegaPowers.powerCode_spec q _ he.1).2.2]
    _ = Ordinal.omega0 ^
        (interpretation q (MuSource.returnedCoefficient q root) +
          (MuSource.tail q root : Ordinal.{0})) := by
      rw [MuSource.exponentCode, ht.2.2.1]

/-- A genuine epsilon mu-cover is exactly a lower bound on the actual
returned LOW coefficient; the corrected indicator and offset add none. -/
theorem epsilon_le_sourceValue_iff (q root : Nat) (epsilon : Ordinal.{0})
    (ha : Mu.inputCheck q root = true) (he : Ordinal.omega0 ^ epsilon = epsilon) :
    epsilon ≤ Mu.sourceValue q root ↔
      epsilon ≤ interpretation q (MuSource.returnedCoefficient q root) := by
  rw [sourceValue_power_returnedCoefficient q root ha]
  exact epsilon_le_power_add_nat_iff epsilon _ _ he

/-- A covered epsilon strictly above the root forces the ORIGINAL
coefficient into the nonparameter branch by actual iota cut reflection. -/
theorem original_coefficient_ge_root (q root : Nat) (epsilon : Ordinal.{0})
    (ha : Mu.inputCheck q root = true) (he : Ordinal.omega0 ^ epsilon = epsilon)
    (hr : interpretation q root < epsilon) (hc : epsilon ≤ Mu.sourceValue q root) :
    interpretation q root ≤ interpretation q (OmegaQuotient.coefficientCode q root) := by
  have hf := (epsilon_le_sourceValue_iff q root epsilon ha he).mp hc
  have hi := OmegaQuotient.coefficient_iota_input q root ha
  obtain ⟨_, t, hcode, ht, hn, hs⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q root _).mp hi
  have hrest := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  apply le_of_not_gt
  intro hsmall
  have hsmall' : denote q t < interpretation q root := by
    simpa only [hcode, interpretation_code] using hsmall
  have hmap := (transform_below_base_iff q root ha t ht hrest).mpr hsmall'
  have hvalue : interpretation q (MuSource.returnedCoefficient q root) =
      denote (betaCode q root) (transform q root t) := by
    rw [(MuSource.returnedCoefficient_spec q root ha).2, Mu.mappedCoefficient, hcode,
      literalCode_code q root ha t ht hn hrest, interpretation_code]
  have hbound : interpretation q (MuSource.returnedCoefficient q root) < interpretation q root := by
    rw [hvalue, ← beta_base q root ha]
    exact hmap
  exact (hf.trans_lt hbound).not_ge hr.le

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.EpsilonCoverCoefficient
