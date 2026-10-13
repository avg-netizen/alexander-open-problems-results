import Alexander313.Wilken.SourceOneNativeSkRaw
import Alexander313.Wilken.HereditarySkPublicDictionary

/-!
# Actual selected-public sk agrees with the entire original source-one raw domain

Original source-zero LOW is strictly below finiteBase one. The genuine
finite dictionary scan therefore selects level zero for its canonical
epsilon emission, and the actual epsilon greater-than-one test excludes
the finite base point. The independent original maximal recurrence and
canonical public injection identify both entire executing public words.
No Native base-one, global Im(upsilon) classification, cross-source mu,
chosen source, recurrence or output equality oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkRaw.DictionaryAgreement

abbrev publicCode := SourceTrackingRaw.Support.publicCode

/-- The actual original LOW bound forces the genuine finite scan to
select source zero; epsilon strictly above one excludes its base point. -/
theorem dictionary_spec (raw : Nat)
    (hr : SourceTrackingRaw.Support.inputCheck raw = true) :
    PublicEpsilonSourceDictionary.inputCheck (publicCode raw) = true ∧
      PublicEpsilonSourceDictionary.level (publicCode raw) = 0 ∧
        PublicEpsilonSourceDictionary.basePoint (publicCode raw) = false := by
  have hs := (SourceTrackingRaw.Support.inputCheck_exact raw).mp hr
  have hp := SourceTrackingRaw.Support.publicCode_spec raw hs.1
  have hq := (PublicEpsilonSourceDictionary.inputCheck_exact (publicCode raw)).mpr
    ⟨hp.1, by rw [hp.2]; exact hs.2.2⟩
  have hupper : unionInterpretation (publicCode raw) < finiteBase 1 :=
    hp.2.trans_lt (SourceTrackingRaw.Support.original_bound raw hs.1)
  have hlevel : PublicEpsilonSourceDictionary.level (publicCode raw) = 0 := by
    by_contra hz
    have hpos := Nat.pos_of_ne_zero hz
    have hbound := (PublicEpsilonSourceDictionary.level_bound (publicCode raw) hp.1).2.2 0 hpos
    exact hupper.not_ge hbound
  have hbase : PublicEpsilonSourceDictionary.basePoint (publicCode raw) = false := by
    cases hb : PublicEpsilonSourceDictionary.basePoint (publicCode raw) with
    | false => rfl
    | true =>
      have he := (PublicEpsilonSourceDictionary.basePoint_exact (publicCode raw) hp.1).mp hb
      rw [hlevel, finiteBase_zero, hp.2] at he
      exact False.elim (hs.2.1.ne' he)
  exact ⟨hq, hlevel, hbase⟩

theorem selected_caller (raw cutoff : Nat) (hi : Support.inputCheck raw cutoff = true) :
    SkPublicDictionary.Support.inputCheck (publicCode raw) cutoff = true := by
  have hs := Bool.and_eq_true.mp hi
  have hd := dictionary_spec raw hs.1
  exact (SkPublicDictionary.Support.inputCheck_exact _ cutoff).mpr ⟨hd.1, hd.2.2, hs.2⟩

/-- Both actual procedures execute independently. Their genuine original
raw mu recurrence gives equal values, then canonical syntax gives equality. -/
theorem executePublic_eq_selected (raw cutoff : Nat) (codes selected : List Nat)
    (ho : codes ∈ SkRaw.executePublic (raw, cutoff))
    (ht : selected ∈ SkPublicDictionary.execute (publicCode raw, cutoff)) : codes = selected := by
  obtain ⟨hi, hc, source, hs, hv⟩ := SkRaw.executePublic_spec raw cutoff codes ho
  have hr := (Bool.and_eq_true.mp hi).1
  have hd := dictionary_spec raw hr
  obtain ⟨hinput, hcases⟩ := SkPublicDictionary.execute_cases (publicCode raw) cutoff selected ht
  have hselected : selected ∈ SkPublicDictionary.Support.sourceOneExecute
      (PublicEpsilonSourceDictionary.sourceRootCode (publicCode raw), cutoff) := by
    rcases hcases with ⟨hl, hm⟩ | ⟨hl, hm⟩
    · exact hm
    · exact False.elim (hl hd.2.1)
  obtain ⟨hcaller, hcan, target, hm, he, hvalue⟩ :=
    SkPublicDictionary.Support.sourceOneExecute_spec _ cutoff selected hselected
  have hp := SkRaw.execute_source raw cutoff source hs
  have htarget := SkSourceRecurrence.execute_source _ cutoff target hm
  obtain ⟨hraw, xs, hhead, hnormal, hlow, hpos⟩ := SkRaw.execute_spec raw cutoff source hs
  obtain ⟨ys, htargetHead⟩ := (SkSourceWord.execute_spec _ cutoff target hm).2.2.1
  have hrootValue := (PublicEpsilonSourceDictionary.source_one_spec (publicCode raw) hd.1 hd.2.1).2.1
  have hpublicValue := (SourceTrackingRaw.Support.publicCode_spec raw
    ((SourceTrackingRaw.Support.inputCheck_exact raw).mp hr).1).2
  have hroot : interpretation 0 raw =
      interpretation 0 (PublicEpsilonSourceDictionary.sourceRootCode (publicCode raw)) :=
    hpublicValue.symm.trans hrootValue.symm
  have hvalues : source.map (interpretation 0) = target.map (interpretation 0) := by
    rw [hhead] at hp ⊢
    rw [htargetHead] at htarget ⊢
    exact hp.values_eq htarget rfl hroot
  exact NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.canonical_words_eq
    codes selected hc hcan (hv.trans (hvalues.trans hvalue.symm))

/-- The actual selected dictionary output is precisely the canonical
public output of the whole original raw source-one initialized execution. -/
theorem executePublic_eq_dictionary (raw cutoff : Nat)
    (hi : Support.inputCheck raw cutoff = true) :
    SkRaw.executePublic (raw, cutoff) = SkPublicDictionary.execute (publicCode raw, cutoff) := by
  obtain ⟨codes, ho⟩ := SkRaw.executePublic_returns raw cutoff hi
  obtain ⟨selected, ht⟩ := SkPublicDictionary.execute_returns _ cutoff (selected_caller raw cutoff hi)
  have he := executePublic_eq_selected raw cutoff codes selected ho ht
  apply Part.ext
  intro word
  constructor
  · intro hw
    have hwcodes := Part.mem_unique hw ho
    simpa only [hwcodes, he] using ht
  · intro hw
    have hwselected := Part.mem_unique hw ht
    simpa only [hwselected, ← he] using ho

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkRaw.DictionaryAgreement
