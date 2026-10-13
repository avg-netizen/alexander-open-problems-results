import Alexander313.Wilken.HereditarySkUpsilonDomain
import Alexander313.Wilken.SourceOneNativeMuPublic
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuSource

/-!
# Actual selected original-source public mu branches

The genuine canonical epsilon dictionary selects an original source-one
or positive original source. Both branches execute the actual mu code
and its proved SAME-value canonical public return. Every root and return
caller derives from the original proper dictionary guard. Actual ordinal
upsilon image exclusion specifies that guard; no arbitrary cross-source
mu equality, output representative or endpoint is supplied. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuPublicDictionary.Support

def inputCheck (gamma : Nat) : Bool :=
  PublicEpsilonSourceDictionary.inputCheck gamma && !PublicEpsilonSourceDictionary.basePoint gamma

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp PublicEpsilonSourceDictionary.inputCheck_primrec
    (Primrec.not.comp PublicEpsilonSourceDictionary.basePoint_primrec)

theorem inputCheck_exact (gamma : Nat) : inputCheck gamma = true ↔
    PublicEpsilonSourceDictionary.inputCheck gamma = true ∧ PublicEpsilonSourceDictionary.basePoint gamma = false := by
  simp only [inputCheck, Bool.and_eq_true, Bool.not_eq_true']

theorem inputCheck_image (gamma : Nat) : inputCheck gamma = true ↔
    Canonical.check gamma = true ∧
      Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
        ¬ SourceUpsilonImage (unionInterpretation gamma) := by
  constructor
  · intro hi
    have hs := (inputCheck_exact gamma).mp hi
    have he := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hs.1
    exact ⟨he.1, he.2, (SkPublicDictionary.UpsilonDomain.basePoint_false_iff_not_image gamma hs.1).mp hs.2⟩
  · rintro ⟨hc, he, hn⟩
    have hg := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mpr ⟨hc, he⟩
    exact (inputCheck_exact gamma).mpr
      ⟨hg, (SkPublicDictionary.UpsilonDomain.basePoint_false_iff_not_image gamma hg).mpr hn⟩

def nativeContext (gamma : Nat) : Nat :=
  NativePublicBridge.contextCode (PublicEpsilonSourceDictionary.sourceIndex gamma)

theorem nativeContext_primrec : Primrec nativeContext :=
  NativePublicBridge.contextCode_primrec.comp PublicEpsilonSourceDictionary.sourceIndex_primrec

abbrev nativeRoot := PublicEpsilonSourceDictionary.positiveRootCode

theorem nativeRoot_primrec : Primrec nativeRoot := PublicEpsilonSourceDictionary.positiveRootCode_primrec

/-- The original positive-source theta witness derives the complete
endpoint-free root guard; its selected source is retained literally. -/
theorem native_root (gamma : Nat) (hi : inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    NativeContext.RootLowCollapse.rootCheck (nativeContext gamma) (nativeRoot gamma) = true ∧
      NativeContext.interpretation (nativeContext gamma) (nativeRoot gamma) = unionInterpretation gamma := by
  have hs := (inputCheck_exact gamma).mp hi
  cases hlevel : PublicEpsilonSourceDictionary.level gamma with
  | zero => exact False.elim (hl hlevel)
  | succ s =>
    have hp := PublicEpsilonSourceDictionary.positive_spec gamma s hs.1 hlevel hs.2
    obtain ⟨t, he, ht, hn, hh⟩ := (NativeContext.Iota.rootCheck_exact s _).mp hp.2.1
    have hr := (NativeContext.RootLowCollapse.rootCheck_exact (NativePublicBridge.contextCode s) _).mpr
      ⟨t, he, ht, hn, hh⟩
    simpa only [nativeContext, nativeRoot, hp.1] using And.intro hr hp.2.2.1

theorem source_one_root (gamma : Nat) (hi : inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    SourceOneIota.Mu.inputCheck (PublicEpsilonSourceDictionary.sourceRootCode gamma) = true ∧
      interpretation 0 (PublicEpsilonSourceDictionary.sourceRootCode gamma) = unionInterpretation gamma := by
  have hs := PublicEpsilonSourceDictionary.source_one_spec gamma ((inputCheck_exact gamma).mp hi).1 hl
  exact ⟨hs.1, hs.2.1⟩

def sourceOneCode (gamma : Nat) : Nat :=
  SourceOneIota.BoundedPublicReturn.publicCode (PublicEpsilonSourceDictionary.sourceRootCode gamma)
    (SourceOneIota.Mu.muCode (PublicEpsilonSourceDictionary.sourceRootCode gamma))

theorem sourceOneCode_primrec : Primrec sourceOneCode :=
  SourceOneIota.BoundedPublicReturn.publicCode_primrec.comp PublicEpsilonSourceDictionary.sourceRootCode_primrec
    (SourceOneIota.Mu.muCode_primrec.comp PublicEpsilonSourceDictionary.sourceRootCode_primrec)

theorem sourceOneCode_spec (gamma : Nat) (hi : inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    Canonical.check (sourceOneCode gamma) = true ∧
      unionInterpretation (sourceOneCode gamma) =
        SourceOneIota.Mu.sourceValue (PublicEpsilonSourceDictionary.sourceRootCode gamma) := by
  have hr := (source_one_root gamma hi hl).1
  have hn : SourceOneIota.Mu.muCode (PublicEpsilonSourceDictionary.sourceRootCode gamma) ∈
      SourceOneIota.Mu.execute (PublicEpsilonSourceDictionary.sourceRootCode gamma) :=
    (SourceOneIota.Mu.execute_graph _ _).mpr ⟨hr, rfl⟩
  have hp := SourceOneIota.BoundedPublicReturn.mu_public_spec _ _ hn
  exact ⟨hp.1, hp.2.trans (SourceOneIota.Mu.muCode_spec _ hr).2.2⟩

def nativeCode (gamma : Nat) : Nat :=
  NativeContext.UniformPublicReturn.publicCode (nativeContext gamma)
    (NativeContext.PublicEpsilonUnboundedIota.MuSource.sourceCode (nativeContext gamma) (nativeRoot gamma))

theorem nativeCode_primrec : Primrec nativeCode :=
  NativeContext.UniformPublicReturn.publicCode_primrec.comp nativeContext_primrec
    (Primrec.comp NativeContext.PublicEpsilonUnboundedIota.MuSource.sourceCode_primrec
      (nativeContext_primrec.pair nativeRoot_primrec))

theorem nativeCode_spec (gamma : Nat) (hi : inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    Canonical.check (nativeCode gamma) = true ∧ unionInterpretation (nativeCode gamma) =
      NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue (nativeContext gamma) (nativeRoot gamma) := by
  have hr := (native_root gamma hi hl).1
  have hm := NativeContext.PublicEpsilonUnboundedIota.MuSource.sourceCode_spec _ _ hr
  have hp := NativeContext.UniformPublicReturn.publicCode_spec _ _
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ _).mpr hm.1)
  exact ⟨hp.1, hp.2.trans
    (NativeContext.PublicEpsilonUnboundedIota.MuSource.source_definition_3_6 _ _ hr)⟩

noncomputable def sourceValue (gamma : Nat) : Ordinal.{0} :=
  cond (PublicEpsilonSourceDictionary.level gamma == 0)
    (SourceOneIota.Mu.sourceValue (PublicEpsilonSourceDictionary.sourceRootCode gamma))
    (NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue (nativeContext gamma) (nativeRoot gamma))

end Alexander313.Wilken.RelativeTerm.Hereditary.MuPublicDictionary.Support
