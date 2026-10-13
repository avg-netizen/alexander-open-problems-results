import Alexander313.Wilken.HereditarySkPublicDictionary
import Alexander313.Wilken.PublicEpsilonNativeSkRaw

/-!
# Selected public sk agrees with every proper positive original source

The actual original positive source is retained literally. Its RAW LOW
epsilon bound lies strictly between finiteBase(s+1) and finiteBase(s+2),
so the genuine finite endpoint scan selects exactly source level s+1.
The independently executed original-source and selected dictionary sk
words then agree by the proved SAME-source maximal recurrence. No
arbitrary cross-source mu, global Im(upsilon), assigned tracker or Par
claim is used. Uncompiled source candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.PositiveAgreement

def publicCode (s raw : Nat) : Nat :=
  NativeContext.UniformPublicReturn.publicCode (NativePublicBridge.contextCode s) raw

theorem publicCode_primrec : Primrec₂ publicCode :=
  NativeContext.UniformPublicReturn.publicCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst) Primrec.snd

theorem dictionary_spec (s raw : Nat)
    (hr : NativeContext.SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) raw = true) :
    PublicEpsilonSourceDictionary.inputCheck (publicCode s raw) = true ∧
      PublicEpsilonSourceDictionary.level (publicCode s raw) = s + 1 ∧
        PublicEpsilonSourceDictionary.basePoint (publicCode s raw) = false := by
  have hs := (NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ raw).mp hr
  have hp := NativeContext.UniformPublicReturn.publicCode_spec _ raw
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ raw).mpr hs.1)
  have hq := (PublicEpsilonSourceDictionary.inputCheck_exact (publicCode s raw)).mpr
    ⟨hp.1, by rw [hp.2]; exact hs.2.2⟩
  have hlow : finiteBase (s + 1) < unionInterpretation (publicCode s raw) := by
    rw [hp.2]
    simpa only [NativePublicBridge.contextCode_value] using hs.2.1
  have hupper : unionInterpretation (publicCode s raw) < finiteBase ((s + 1) + 1) := by
    rw [hp.2, finiteBase_succ]
    simpa only [NativePublicBridge.contextCode_value] using
      NativeContext.checked_low_bound (NativePublicBridge.contextCode s) raw hs.1
  have hscan := PublicEpsilonSourceDictionary.level_bound (publicCode s raw) hp.1
  have hlevel : PublicEpsilonSourceDictionary.level (publicCode s raw) = s + 1 := by
    have hlo : s + 1 ≤ PublicEpsilonSourceDictionary.level (publicCode s raw) := by
      have hlt := finiteBase_strictMono.lt_iff_lt.mp (hlow.trans hscan.2.1)
      omega
    have hhi : PublicEpsilonSourceDictionary.level (publicCode s raw) ≤ s + 1 := by
      by_contra hn
      have hm : s + 1 < PublicEpsilonSourceDictionary.level (publicCode s raw) := by omega
      exact hupper.not_ge (hscan.2.2 (s + 1) hm)
    omega
  have hbase : PublicEpsilonSourceDictionary.basePoint (publicCode s raw) = false := by
    cases hb : PublicEpsilonSourceDictionary.basePoint (publicCode s raw) with
    | false => rfl
    | true =>
      have he := (PublicEpsilonSourceDictionary.basePoint_exact (publicCode s raw) hp.1).mp hb
      rw [hlevel] at he
      exact False.elim (hlow.ne' he)
  exact ⟨hq, hlevel, hbase⟩

theorem selected_caller (s raw cutoff : Nat)
    (hi : NativeContext.PublicEpsilonUnboundedIota.SkRaw.inputCheck
      (NativePublicBridge.contextCode s) raw cutoff = true) :
    Support.inputCheck (publicCode s raw) cutoff = true := by
  have hs := Bool.and_eq_true.mp hi
  have hd := dictionary_spec s raw hs.1
  exact (Support.inputCheck_exact _ cutoff).mpr ⟨hd.1, hd.2.2, hs.2⟩

/-- The real least scan selects the SAME literal original positive source;
the independent HIGH representatives need only have their proved SAME value. -/
theorem executePublic_eq_selected (s raw cutoff : Nat) (codes selected : List Nat)
    (ho : codes ∈ NativeContext.PublicEpsilonUnboundedIota.SkRaw.executePublic
      ((NativePublicBridge.contextCode s, raw), cutoff))
    (ht : selected ∈ SkPublicDictionary.execute (publicCode s raw, cutoff)) : codes = selected := by
  obtain ⟨hi, hm⟩ := NativeContext.PublicEpsilonUnboundedIota.SkRaw.executePublic_member _ raw cutoff codes ho
  have hr := (Bool.and_eq_true.mp hi).1
  have hd := dictionary_spec s raw hr
  obtain ⟨hinput, hcases⟩ := SkPublicDictionary.execute_cases (publicCode s raw) cutoff selected ht
  have hselected : selected ∈ NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic
      (Support.nativeQuery (publicCode s raw) cutoff) := by
    rcases hcases with ⟨hl, hm⟩ | ⟨hl, hm⟩
    · exact False.elim (by rw [hd.2.1] at hl; omega)
    · exact hm
  have hp := PublicEpsilonSourceDictionary.positive_spec (publicCode s raw) s hd.1 hd.2.1 hd.2.2
  have hquery : Support.nativeQuery (publicCode s raw) cutoff =
      ((NativePublicBridge.contextCode s, PublicEpsilonSourceDictionary.positiveRootCode (publicCode s raw)), cutoff) := by
    simp only [Support.nativeQuery, hp.1]
  rw [hquery] at hselected
  have hroot := (NativeContext.SourceTrackingRaw.Support.rootCode_spec _ raw hr).2.2
  have hpublic := (NativeContext.UniformPublicReturn.publicCode_spec _ raw
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ raw).mpr
      (NativeContext.SourceTrackingRaw.Support.rootCode_spec _ raw hr).1)).2
  exact NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.executePublic_eq
    (NativePublicBridge.contextCode s) _ _ cutoff cutoff codes selected hm hselected
    (hroot.trans (hpublic.symm.trans hp.2.2.1.symm)) rfl

theorem executePublic_eq_dictionary (s raw cutoff : Nat)
    (hi : NativeContext.PublicEpsilonUnboundedIota.SkRaw.inputCheck
      (NativePublicBridge.contextCode s) raw cutoff = true) :
    NativeContext.PublicEpsilonUnboundedIota.SkRaw.executePublic
      ((NativePublicBridge.contextCode s, raw), cutoff) =
        SkPublicDictionary.execute (publicCode s raw, cutoff) := by
  obtain ⟨codes, ho⟩ := NativeContext.PublicEpsilonUnboundedIota.SkRaw.executePublic_returns _ raw cutoff hi
  obtain ⟨selected, ht⟩ := SkPublicDictionary.execute_returns _ cutoff (selected_caller s raw cutoff hi)
  have he := executePublic_eq_selected s raw cutoff codes selected ho ht
  apply Part.ext
  intro word
  constructor
  · intro hw
    have hwcodes := Part.mem_unique hw ho
    simpa only [hwcodes, he] using ht
  · intro hw
    have hwselected := Part.mem_unique hw ht
    simpa only [hwselected, ← he] using ho

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.PositiveAgreement
