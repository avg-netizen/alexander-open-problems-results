import Alexander313.Wilken.HereditaryPublicMtsInfinity
import Alexander313.Wilken.HereditaryPublicMtsReachBound
import Alexander313.Wilken.HereditaryPublicMtsPositiveHat
import Alexander313.Wilken.HereditaryPublicMtsSourceOneHat

/-!
# The actual full-domain emitted covering and genuine singleton cut

The selected ORIGINAL source defines the previously proved semantic least
singleton boundary. Every independent public mu covering stays inside the
initial OWN interval, and that genuine singleton cut is at most OWN. These
two derived bounds reduce both directions of the full-domain actual emitted
covering criterion to literal equality with the earlier OWN execution.
The input target is genuinely multiplicative. No incoming-context mu identity
outside OWN, arbitrary-reach sufficiency or numerical minimum is asserted.
Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.InfinityHat

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open CoveringSupport (Covering)

def value (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true) : Ordinal.{0} :=
  if hl : PublicEpsilonSourceDictionary.level gamma = 0 then SourceOneHat.value gamma hg hl
  else PositiveHat.value gamma hg hl

/-- Both true original singleton candidates bound the semantic cut by
the starting original successor, without executing its minimum. -/
theorem value_le_own (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    value gamma hg ≤ ContextSupport.ownCeiling gamma := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · have ha := ContextSupport.source_one_base gamma hg hl
    have hs := SourceOneIota.GammaHat.value_le_sourceAlphaPlus _ ha.1
    simpa only [value, dif_pos hl, SourceOneHat.value, ContextSupport.ownCeiling,
      hl, beq_self_eq_true, Bool.cond_true] using hs
  · have ha := ContextSupport.positive_base gamma hg hl
    have hs := GammaHat.value_le_sourceAlphaPlus _ _ ha.1
    simpa only [value, dif_neg hl, PositiveHat.value, ContextSupport.ownCeiling,
      beq_eq_false_iff_ne.mpr hl, Bool.cond_false] using hs

theorem own_input_of_cut (gamma beta : Nat) (hi : Infinity.inputCheck gamma beta = true)
    (hcut : unionInterpretation beta < ContextSupport.ownCeiling gamma) :
    PublicMts.inputCheck gamma beta = true := by
  have hs := (Infinity.inputCheck_exact gamma beta).mp hi
  exact (PublicMts.inputCheck_exact gamma beta).mpr
    ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hcut⟩

/-- The exact original dictionary split combines the already proved true
OWN emitted-word criteria, keeping their genuine source guards. -/
theorem own_execute_covering_iff_lt_value (gamma beta d : Nat) (out : List Nat)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ho : out ∈ PublicMts.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta out ↔ unionInterpretation beta <
      value gamma ((PublicMts.inputCheck_exact gamma beta).mp (PublicMts.execute_spec gamma beta out ho).1).1 := by
  by_cases hl : PublicEpsilonSourceDictionary.level gamma = 0
  · simpa only [value, dif_pos hl] using
      SourceOneHat.execute_covering_iff_lt_value gamma beta d out hd ho hl hm hlt
  · simpa only [value, dif_neg hl] using
      PositiveHat.execute_covering_iff_lt_value gamma beta d out hd ho hl hm hlt

/-- For every actual full alpha-infinity execution at a strict M target,
the emitted word is a genuine independent covering exactly below the true
selected original semantic singleton cut. All outside-OWN cases are covered. -/
theorem execute_covering_iff_lt_value (gamma beta : Nat) (out : List Nat)
    (ho : out ∈ Infinity.execute gamma beta)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta out ↔ unionInterpretation beta <
      value gamma ((Infinity.inputCheck_exact gamma beta).mp (Infinity.execute_spec gamma beta out ho).1).1 := by
  obtain ⟨hi, d, hd, hw⟩ := Infinity.execute_spec gamma beta out ho
  have hg := ((Infinity.inputCheck_exact gamma beta).mp hi).1
  constructor
  · intro hc
    have hcut := ReachBound.covering_lt_own hc
    have hj := own_input_of_cut gamma beta hi hcut
    have ht : out ∈ PublicMts.execute gamma beta := by
      rw [← Infinity.execute_eq_own gamma beta hj]
      exact ho
    exact (own_execute_covering_iff_lt_value gamma beta d out hd ht hm hlt).mp hc
  · intro hcut
    have hj := own_input_of_cut gamma beta hi (hcut.trans_le (value_le_own gamma hg))
    have ht : out ∈ PublicMts.execute gamma beta := by
      rw [← Infinity.execute_eq_own gamma beta hj]
      exact ho
    exact (own_execute_covering_iff_lt_value gamma beta d out hd ht hm hlt).mpr hcut

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.InfinityHat
