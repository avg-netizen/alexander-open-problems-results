import Alexander313.Wilken.PublicEpsilonSourceDictionary
import Alexander313.Wilken.PublicEpsilonNativeSkPublicValueInvariance
import Alexander313.Wilken.SourceOneNativeSkSourceValueInvariance

/-!
# Actual original-source branches of a public sk dispatcher

The genuine canonical epsilon dictionary distinguishes a proper original
source-one HIGH root from a proper positive original-source HIGH root.
Its actual finite-base endpoint test is retained explicitly. Original
source-one outputs are returned through their genuine source-zero public
tags and canonicalization; no Native base-one grammar is used. All root
and cutoff callers follow from the concrete original input guard. Global
Im(upsilon) classification and cross-source mu identification remain open.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.Support

abbrev Query := Nat × Nat

def inputCheck (gamma cutoff : Nat) : Bool := PublicEpsilonSourceDictionary.inputCheck gamma &&
  (!PublicEpsilonSourceDictionary.basePoint gamma && unionCheck cutoff)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (PublicEpsilonSourceDictionary.inputCheck_primrec.comp Primrec.fst)
    (Primrec.and.comp (Primrec.not.comp (PublicEpsilonSourceDictionary.basePoint_primrec.comp Primrec.fst))
      (Canonical.Effective.unionCheck_primrec.comp Primrec.snd))).to₂

/-- The literal original domain uses the actual canonical epsilon and
proper-dictionary tests, rather than an unproved Im(upsilon) classifier. -/
theorem inputCheck_exact (gamma cutoff : Nat) : inputCheck gamma cutoff = true ↔
    PublicEpsilonSourceDictionary.inputCheck gamma = true ∧
      PublicEpsilonSourceDictionary.basePoint gamma = false ∧ unionCheck cutoff = true := by
  simp only [inputCheck, Bool.and_eq_true, Bool.not_eq_true']

abbrev sourceOnePublicCode := SourceOneIota.SourceTrackingRaw.Support.publicCode

theorem sourceOnePublicCode_primrec : Primrec sourceOnePublicCode :=
  SourceOneIota.SourceTrackingRaw.Support.publicCode_primrec

theorem sourceOnePublicCode_spec (c : Nat) (hc : Theta.acceptedLowCode 0 c = true) :
    Canonical.check (sourceOnePublicCode c) = true ∧
      unionInterpretation (sourceOnePublicCode c) = interpretation 0 c :=
  SourceOneIota.SourceTrackingRaw.Support.publicCode_spec c ((Theta.acceptedLowCode_iff 0 c).mp hc).1

def sourceOnePublicWord (word : List Nat) : List Nat := word.map sourceOnePublicCode

theorem sourceOnePublicWord_primrec : Primrec sourceOnePublicWord :=
  Primrec.list_map Primrec.id (sourceOnePublicCode_primrec.comp Primrec.snd).to₂

theorem sourceOnePublicWord_spec (word : List Nat)
    (hw : ∀ c ∈ word, Theta.acceptedLowCode 0 c = true) :
    (∀ c ∈ sourceOnePublicWord word, Canonical.check c = true) ∧
      (sourceOnePublicWord word).map unionInterpretation = word.map (interpretation 0) := by
  constructor
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (sourceOnePublicCode_spec d (hw d hd)).1
  · rw [sourceOnePublicWord, List.map_map]
    exact List.map_congr_left (fun c hc => (sourceOnePublicCode_spec c (hw c hc)).2)

def sourceOneExecute (p : Query) : Part (List Nat) :=
  (SourceOneIota.SkSourceWord.execute p).map sourceOnePublicWord

theorem sourceOneExecute_partrec : Partrec sourceOneExecute :=
  Partrec.map SourceOneIota.SkSourceWord.execute_partrec
    (sourceOnePublicWord_primrec.comp Primrec.snd).to_comp.to₂

theorem sourceOneExecute_domain (root cutoff : Nat) : (sourceOneExecute (root, cutoff)).Dom ↔
    SourceOneIota.SkSourceWord.inputCheck root cutoff = true :=
  SourceOneIota.SkSourceWord.execute_domain root cutoff

theorem sourceOneExecute_spec (root cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ sourceOneExecute (root, cutoff)) :
    SourceOneIota.SkSourceWord.inputCheck root cutoff = true ∧
      (∀ c ∈ codes, Canonical.check c = true) ∧ ∃ source,
        source ∈ SourceOneIota.SkSourceWord.execute (root, cutoff) ∧
          codes = sourceOnePublicWord source ∧
          codes.map unionInterpretation = source.map (interpretation 0) := by
  obtain ⟨source, hs, rfl⟩ := (Part.mem_map_iff sourceOnePublicWord).mp ho
  have ht := SourceOneIota.SkSourceWord.execute_spec root cutoff source hs
  have hp := sourceOnePublicWord_spec source ht.2.2.2
  exact ⟨ht.1, hp.1, source, hs, rfl, hp.2⟩

theorem sourceOneExecute_eq (root other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ sourceOneExecute (root, cutoff))
    (ht : otherCodes ∈ sourceOneExecute (other, otherCutoff))
    (hroot : interpretation 0 root = interpretation 0 other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) : codes = otherCodes := by
  obtain ⟨hi, hc, source, hs, he, hv⟩ := sourceOneExecute_spec root cutoff codes ho
  obtain ⟨hj, hd, otherSource, hother, hcode, hw⟩ := sourceOneExecute_spec other otherCutoff otherCodes ht
  exact NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.canonical_words_eq
    codes otherCodes hc hd (hv.trans
      ((SourceOneIota.SkSourceRecurrence.execute_values_eq root other cutoff otherCutoff source otherSource
        hs hother hroot hcut).trans hw.symm))

def nativeQuery (gamma cutoff : Nat) : NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support.Query :=
  ((NativePublicBridge.contextCode (PublicEpsilonSourceDictionary.sourceIndex gamma),
    PublicEpsilonSourceDictionary.positiveRootCode gamma), cutoff)

theorem nativeQuery_primrec : Primrec (fun p : Query => nativeQuery p.1 p.2) :=
  ((NativePublicBridge.contextCode_primrec.comp
    (PublicEpsilonSourceDictionary.sourceIndex_primrec.comp Primrec.fst)).pair
      (PublicEpsilonSourceDictionary.positiveRootCode_primrec.comp Primrec.fst)).pair Primrec.snd

theorem sourceOne_caller (gamma cutoff : Nat) (hi : inputCheck gamma cutoff = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    SourceOneIota.SkSourceWord.inputCheck (PublicEpsilonSourceDictionary.sourceRootCode gamma) cutoff = true := by
  have hs := (inputCheck_exact gamma cutoff).mp hi
  exact (SourceOneIota.SkSourceWord.inputCheck_exact _ cutoff).mpr
    ⟨(PublicEpsilonSourceDictionary.source_one_spec gamma hs.1 hl).1, hs.2.2⟩

/-- The positive original-source root is converted to the unrestricted
HIGH guard by its actual original theta/Normal/sort witness. -/
theorem native_root (gamma cutoff : Nat) (hi : inputCheck gamma cutoff = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    NativeContext.RootLowCollapse.rootCheck
      (NativePublicBridge.contextCode (PublicEpsilonSourceDictionary.sourceIndex gamma))
      (PublicEpsilonSourceDictionary.positiveRootCode gamma) = true ∧
    NativeContext.interpretation
      (NativePublicBridge.contextCode (PublicEpsilonSourceDictionary.sourceIndex gamma))
      (PublicEpsilonSourceDictionary.positiveRootCode gamma) = unionInterpretation gamma := by
  have hs := (inputCheck_exact gamma cutoff).mp hi
  cases hlevel : PublicEpsilonSourceDictionary.level gamma with
  | zero => exact False.elim (hl hlevel)
  | succ s =>
    have hp := PublicEpsilonSourceDictionary.positive_spec gamma s hs.1 hlevel hs.2.1
    obtain ⟨t, he, ht, hn, hh⟩ := (NativeContext.Iota.rootCheck_exact s _).mp hp.2.1
    have hr := (NativeContext.RootLowCollapse.rootCheck_exact (NativePublicBridge.contextCode s) _).mpr
      ⟨t, he, ht, hn, hh⟩
    simpa only [hp.1] using And.intro hr hp.2.2.1

theorem native_caller (gamma cutoff : Nat) (hi : inputCheck gamma cutoff = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    NativeContext.PublicEpsilonUnboundedIota.SkIteration.inputCheck
      (nativeQuery gamma cutoff).1.1 (nativeQuery gamma cutoff).1.2 cutoff = true :=
  (NativeContext.PublicEpsilonUnboundedIota.SkIteration.inputCheck_exact _ _ cutoff).mpr
    ⟨(native_root gamma cutoff hi hl).1, ((inputCheck_exact gamma cutoff).mp hi).2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.Support
