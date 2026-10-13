import Alexander313.Wilken.SourceOneNativeAdditiveTrackingAssignment
import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingAssignment
import Alexander313.Wilken.HereditaryPublicUpsilonSegment
import Alexander313.Wilken.HereditaryNativeLowArithmetic

/-!
# Genuine finite-stage original dictionaries for all public principals

The least actual upsilon segment supplies a source-one or positive original
grammar. The existing real finite source return constructs the relative input
at that segment, including non-epsilon principals. Every original full assignment
caller derives from canonical admission, genuine positivity and the segment
bounds. This is preparation for global Definition3.24, not an assigned tracking
word or a certificate supplied by a caller. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.Source

open NativeContext.SourceTrackingSequences (lastCode)

def inputCheck (alpha : Nat) : Bool := Canonical.check alpha && Principal.unionPrincipalCheck alpha

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp Canonical.Effective.check_primrec Principal.unionPrincipalCheck_primrec

theorem inputCheck_exact (alpha : Nat) : inputCheck alpha = true ↔
    Canonical.check alpha = true ∧ 0 < unionInterpretation alpha ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation alpha) := by
  simp only [inputCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hp⟩
    have hs := (Principal.unionPrincipalCheck_exact alpha).mp hp
    exact ⟨hc, hs.2⟩
  · rintro ⟨hc, hp, ha⟩
    exact ⟨hc, (Principal.unionPrincipalCheck_exact alpha).mpr ⟨Canonical.check_original hc, hp, ha⟩⟩

abbrev level := PublicEpsilonSourceDictionary.level
abbrev sourceIndex := PublicEpsilonSourceDictionary.sourceIndex
abbrev endpointCode := PublicEpsilonSourceDictionary.endpointCode

def contextCode (alpha : Nat) : Nat := NativePublicBridge.contextCode (sourceIndex alpha)

theorem contextCode_primrec : Primrec contextCode :=
  NativePublicBridge.contextCode_primrec.comp PublicEpsilonSourceDictionary.sourceIndex_primrec

theorem sourceIndex_succ (alpha s : Nat) (hl : level alpha = s + 1) : sourceIndex alpha = s := by
  simp only [PublicEpsilonSourceDictionary.sourceIndex, hl, Nat.add_sub_cancel]

theorem segment_spec (alpha : Nat) (hi : inputCheck alpha = true) :
    PublicUpsilonSegment.FirstSegment (unionInterpretation alpha) (PublicUpsilonSegment.segmentValue alpha) :=
  PublicUpsilonSegment.segmentValue_first alpha ((inputCheck_exact alpha).mp hi).1

def sourceOneCode (alpha : Nat) : Nat := SourceZeta.Transport.returnCode 0 alpha

theorem sourceOneCode_primrec : Primrec sourceOneCode :=
  SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0) Primrec.id

theorem sourceOneCode_spec (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha = 0) :
    lowCheckCode 0 (sourceOneCode alpha) = true ∧
      interpretation 0 (sourceOneCode alpha) = unionInterpretation alpha := by
  have hc := (inputCheck_exact alpha).mp hi
  have hb : unionInterpretation alpha < finiteBase (0 + 1) := by
    simpa only [hl] using (PublicEpsilonSourceDictionary.level_bound alpha hc.1).2.1
  have hs := SourceZeta.Transport.returnCode_spec 0 alpha hc.1 hb
  exact ⟨((Theta.acceptedLowCode_iff 0 _).mp hs.1).1, hs.2⟩

theorem sourceOne_caller (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha = 0) :
    SourceOneIota.SourceAdditiveTracking.Assignment.inputCheck (sourceOneCode alpha) = true := by
  have hs := sourceOneCode_spec alpha hi hl
  have hc := (inputCheck_exact alpha).mp hi
  exact (SourceOneIota.SourceAdditiveTracking.Assignment.inputCheck_exact _).mpr
    ⟨hs.1, by rw [hs.2]; exact Order.one_le_iff_pos.mpr hc.2.1,
      by rw [hs.2]; exact hc.2.2⟩

def nativeCode (alpha : Nat) : Nat := NativeContext.LowArithmetic.returnCode (sourceIndex alpha) alpha

theorem nativeCode_primrec : Primrec nativeCode :=
  NativeContext.LowArithmetic.returnCode_primrec.comp PublicEpsilonSourceDictionary.sourceIndex_primrec Primrec.id

theorem nativeCode_spec (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha ≠ 0) :
    NativeContext.lowCheckCode (contextCode alpha) (nativeCode alpha) = true ∧
      NativeContext.interpretation (contextCode alpha) (nativeCode alpha) = unionInterpretation alpha := by
  have hc := (inputCheck_exact alpha).mp hi
  cases hm : level alpha with
  | zero => exact False.elim (hl hm)
  | succ s =>
    have hb : unionInterpretation alpha < finiteBase ((s + 1) + 1) := by
      simpa only [hm] using (PublicEpsilonSourceDictionary.level_bound alpha hc.1).2.1
    have hs := NativeContext.LowArithmetic.returnCode_spec s alpha hc.1 hb
    simpa only [contextCode, nativeCode, sourceIndex_succ alpha s hm] using And.intro hs.1 hs.2.2

theorem native_base_le (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha ≠ 0) :
    NativeContext.base (contextCode alpha) ≤ unionInterpretation alpha := by
  have hc := (inputCheck_exact alpha).mp hi
  cases hm : level alpha with
  | zero => exact False.elim (hl hm)
  | succ s =>
    have hs := (PublicEpsilonSourceDictionary.level_bound alpha hc.1).2.2 s
      (by rw [hm]; exact Nat.lt_succ_self s)
    simpa only [contextCode, sourceIndex_succ alpha s hm, NativePublicBridge.contextCode_value] using hs

theorem native_caller (alpha : Nat) (hi : inputCheck alpha = true) (hl : level alpha ≠ 0) :
    NativeContext.SourceAdditiveTracking.Assignment.inputCheck (contextCode alpha) (nativeCode alpha) = true := by
  have hs := nativeCode_spec alpha hi hl
  have hc := (inputCheck_exact alpha).mp hi
  exact (NativeContext.SourceAdditiveTracking.Assignment.inputCheck_exact _ _).mpr
    ⟨hs.1, by rw [hs.2]; exact native_base_le alpha hi hl, by rw [hs.2]; exact hc.2.2⟩

def cutoffCode (alpha : Nat) : Nat := NativeContext.UniformPublicReturn.publicCode (contextCode alpha)
  (NativeContext.SourceAdditiveTracking.FactorSupport.cutoffCode (contextCode alpha))

theorem cutoffCode_primrec : Primrec cutoffCode :=
  NativeContext.UniformPublicReturn.publicCode_primrec.comp contextCode_primrec
    (NativeContext.SourceAdditiveTracking.FactorSupport.cutoffCode_primrec.comp contextCode_primrec)

theorem cutoffCode_spec (alpha : Nat) : Canonical.check (cutoffCode alpha) = true ∧
    unionInterpretation (cutoffCode alpha) = NativeContext.base (contextCode alpha) ^ Ordinal.omega0 := by
  have hq := NativePublicBridge.contextCode_checked (sourceIndex alpha)
  have hs := NativeContext.SourceAdditiveTracking.FactorSupport.cutoffCode_spec (contextCode alpha) hq
  have hp := NativeContext.UniformPublicReturn.publicCode_spec _ _
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ _).mpr hs.1)
  exact ⟨hp.1, hp.2.trans hs.2.2⟩

def baseWord (m : Nat) : List Nat := (List.range m).map (fun i => endpointCode (i + 1))

theorem baseWord_primrec : Primrec baseWord :=
  Primrec.list_map Primrec.list_range
    (PublicEpsilonSourceDictionary.endpointCode_primrec.comp (Primrec.succ.comp Primrec.snd)).to₂

theorem baseWord_canonical (m : Nat) : ∀ c ∈ baseWord m, Canonical.check c = true := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact PublicEpsilonSourceDictionary.endpointCode_checked _

theorem baseWord_values (m : Nat) : (baseWord m).map unionInterpretation =
    (List.range m).map (fun i => sourceUpsilon ((i + 1 : Nat) : Ordinal.{0})) := by
  rw [baseWord, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact (PublicEpsilonSourceDictionary.endpointCode_value _).trans
    (PublicUpsilonSegment.successor_value i).symm

theorem endpoint_context (alpha : Nat) (hl : level alpha ≠ 0) :
    unionInterpretation (endpointCode (level alpha)) = NativeContext.base (contextCode alpha) := by
  cases hm : level alpha with
  | zero => exact False.elim (hl hm)
  | succ s =>
    simp only [PublicEpsilonSourceDictionary.endpointCode_value, contextCode,
      sourceIndex_succ alpha s hm, NativePublicBridge.contextCode_value, hm]

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.Source
