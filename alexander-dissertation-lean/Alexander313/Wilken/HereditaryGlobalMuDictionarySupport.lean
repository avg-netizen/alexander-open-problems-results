import Alexander313.Wilken.HereditaryMuPublicDictionary
import Alexander313.Wilken.HereditaryPublicUpsilonSegment
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequencesSupport

/-!
# Genuine endpoint extension of the independently executing public mu

Definition3.15 extends mu at positive successor upsilon values to their
actual next grammar endpoint. The least finite endpoint scan derives the
index and every source caller. Proper epsilons keep the original independently
executing public mu. All canonical public values lie below upsilon omega;
its positive image values are therefore exactly finite successor endpoints.
No mu at a positive limit upsilon index or global tracker is postulated.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalMuDictionary.Support

abbrev inputCheck := PublicEpsilonSourceDictionary.inputCheck

theorem inputCheck_primrec : Primrec inputCheck := PublicEpsilonSourceDictionary.inputCheck_primrec

theorem inputCheck_exact (gamma : Nat) : inputCheck gamma = true ↔
    Canonical.check gamma = true ∧ Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma :=
  PublicEpsilonSourceDictionary.inputCheck_exact gamma

def nextEndpointCode (gamma : Nat) : Nat := PublicEpsilonSourceDictionary.endpointCode
  (PublicEpsilonSourceDictionary.level gamma + 1)

theorem nextEndpointCode_primrec : Primrec nextEndpointCode :=
  PublicEpsilonSourceDictionary.endpointCode_primrec.comp
    (Primrec.succ.comp PublicEpsilonSourceDictionary.level_primrec)

theorem nextEndpointCode_spec (gamma : Nat) : Canonical.check (nextEndpointCode gamma) = true ∧
    unionInterpretation (nextEndpointCode gamma) =
      sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0}) :=
  ⟨PublicEpsilonSourceDictionary.endpointCode_checked _,
    (PublicEpsilonSourceDictionary.endpointCode_value _).trans
      (PublicUpsilonSegment.successor_value _).symm⟩

theorem proper_caller (gamma : Nat) (hi : inputCheck gamma = true)
    (hb : PublicEpsilonSourceDictionary.basePoint gamma = false) :
    MuPublicDictionary.Support.inputCheck gamma = true :=
  (MuPublicDictionary.Support.inputCheck_exact gamma).mpr ⟨hi, hb⟩

/-- The actual finite dictionary supplies both the genuine successor
index and the original least-segment certificate at a base point. -/
theorem base_point_spec (gamma : Nat) (hi : inputCheck gamma = true)
    (hb : PublicEpsilonSourceDictionary.basePoint gamma = true) :
    0 < PublicEpsilonSourceDictionary.level gamma ∧
      unionInterpretation gamma = sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma : Nat) : Ordinal.{0}) ∧
        PublicUpsilonSegment.FirstSegment (unionInterpretation gamma) (PublicUpsilonSegment.segmentValue gamma) := by
  have hl := (PublicEpsilonSourceDictionary.base_point_spec gamma hi hb).1
  have hv := (PublicEpsilonSourceDictionary.basePoint_exact gamma ((inputCheck_exact gamma).mp hi).1).mp hb
  refine ⟨hl, ?_, PublicUpsilonSegment.segmentValue_first gamma ((inputCheck_exact gamma).mp hi).1⟩
  cases hm : PublicEpsilonSourceDictionary.level gamma with
  | zero => exact False.elim (by omega)
  | succ n => simpa only [hm, PublicUpsilonSegment.successor_value] using hv

theorem endpoint_input (n : Nat) : inputCheck (PublicEpsilonSourceDictionary.endpointCode (n + 1)) = true :=
  (inputCheck_exact _).mpr ⟨PublicEpsilonSourceDictionary.endpointCode_checked _,
    by rw [PublicEpsilonSourceDictionary.endpointCode_value]; exact finiteBase_succ_omegaPower_eq_self n⟩

theorem endpoint_level (n : Nat) :
    PublicEpsilonSourceDictionary.level (PublicEpsilonSourceDictionary.endpointCode (n + 1)) = n + 1 :=
  SkPublicDictionary.FiniteDomain.level_eq_of_finiteBase _ n (endpoint_input n)
    (PublicEpsilonSourceDictionary.endpointCode_value _)

theorem endpoint_basePoint (n : Nat) :
    PublicEpsilonSourceDictionary.basePoint (PublicEpsilonSourceDictionary.endpointCode (n + 1)) = true :=
  (PublicEpsilonSourceDictionary.basePoint_exact _ (PublicEpsilonSourceDictionary.endpointCode_checked _)).mpr
    (by rw [endpoint_level]; exact PublicEpsilonSourceDictionary.endpointCode_value _)

theorem proper_value_positive_principal (gamma : Nat)
    (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    0 < MuPublicDictionary.Support.sourceValue gamma ∧
      Ordinal.IsPrincipal (· + ·) (MuPublicDictionary.Support.sourceValue gamma) := by
  rw [MuPublicDictionary.Support.sourceValue]
  cases hz : PublicEpsilonSourceDictionary.level gamma == 0 with
  | true =>
    simp only [hz, Bool.cond_true, SourceOneIota.Mu.sourceValue]
    exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩
  | false =>
    simp only [hz, Bool.cond_false, NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue]
    exact ⟨Ordinal.opow_pos _ Ordinal.omega0_pos, Ordinal.isPrincipal_add_omega0_opow _⟩

theorem proper_value_omega_le (gamma : Nat)
    (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    Ordinal.omega0 ≤ MuPublicDictionary.Support.sourceValue gamma := by
  cases hz : PublicEpsilonSourceDictionary.level gamma == 0 with
  | true =>
    have hr := (MuPublicDictionary.Support.source_one_root gamma hi (beq_iff_eq.mp hz)).1
    simpa only [MuPublicDictionary.Support.sourceValue, hz, Bool.cond_true] using
      SourceOneIota.SourceTrackingSupport.omega_le_mu _ hr
  | false =>
    have hl : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by
      intro he
      have ht : (PublicEpsilonSourceDictionary.level gamma == 0) = true := beq_iff_eq.mpr he
      rw [hz] at ht
      cases ht
    have hr := (MuPublicDictionary.Support.native_root gamma hi hl).1
    simpa only [MuPublicDictionary.Support.sourceValue, hz, Bool.cond_false] using
      NativeContext.SourceTrackingSequences.Support.omega_le_mu _ _ hr

/-- Proper mu remains strictly below the actual selected grammar
endpoint. The source-one branch uses its OWN proved alpha-plus bound;
the positive branch uses the actual original-source LOW mu producer. -/
theorem proper_value_bound (gamma : Nat)
    (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    MuPublicDictionary.Support.sourceValue gamma < finiteBase (PublicEpsilonSourceDictionary.level gamma + 1) := by
  cases hz : PublicEpsilonSourceDictionary.level gamma == 0 with
  | true =>
    have hl := beq_iff_eq.mp hz
    have hr := (MuPublicDictionary.Support.source_one_root gamma hi hl).1
    have hs := SourceOneIota.Mu.muCode_spec _ hr
    have hb := (hs.2.2.symm.trans_lt (SourceOneIota.Mu.Bounds.muCode_lt_source_alphaPlus _ hr)).trans
      (SourceOneIota.BoundedPublicReturn.sourceAlphaPlus_lt_public_endpoint _ hr)
    simpa only [MuPublicDictionary.Support.sourceValue, hz, Bool.cond_true, hl] using hb
  | false =>
    have hl : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by
      intro he
      have ht : (PublicEpsilonSourceDictionary.level gamma == 0) = true := beq_iff_eq.mpr he
      rw [hz] at ht
      cases ht
    have hr := (MuPublicDictionary.Support.native_root gamma hi hl).1
    have hm := NativeContext.PublicEpsilonUnboundedIota.MuSource.sourceCode_spec _ _ hr
    have hb := NativeContext.checked_low_bound _ _ hm.1
    rw [NativeContext.PublicEpsilonUnboundedIota.MuSource.source_definition_3_6 _ _ hr] at hb
    cases hs : PublicEpsilonSourceDictionary.level gamma with
    | zero => exact False.elim (hl hs)
    | succ s =>
      have hindex : PublicEpsilonSourceDictionary.sourceIndex gamma = s := by
        simp only [PublicEpsilonSourceDictionary.sourceIndex, hs, Nat.add_sub_cancel]
      have hboundary : globalBoundary (NativeContext.base (MuPublicDictionary.Support.nativeContext gamma)) 0 =
          finiteBase (PublicEpsilonSourceDictionary.level gamma + 1) := by
        simpa only [MuPublicDictionary.Support.nativeContext, hindex, NativePublicBridge.contextCode_value, hs]
          using (finiteBase_succ (s + 1)).symm
      rw [hboundary] at hb
      simpa only [MuPublicDictionary.Support.sourceValue, hz, Bool.cond_false] using hb

noncomputable def sourceValue (gamma : Nat) : Ordinal.{0} :=
  cond (PublicEpsilonSourceDictionary.basePoint gamma)
    (sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0}))
    (MuPublicDictionary.Support.sourceValue gamma)

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalMuDictionary.Support
