import Alexander313.Wilken.HereditaryNativeUnboundedPublicReturn
import Alexander313.Wilken.PublicEpsilonNativeContextSupport

/-!
# Genuine canonical-base callers for uniform unbounded public return

Canonicalizing the original coded epsilon changes its spelling only.
The actual original base check derives canonical classifier admission,
literal RAW LOW check agreement and SAME value at every input code.
Positive proper classification then supplies the actual unbounded source
producer without an endpoint bound. Original source-one dispatch is supplied
by its separate original parser construction, never a native base-one parser.
No classifier, base equality or return oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UniformPublicReturn

def canonicalBase (q : Nat) : Nat := Canonical.canonicalize q

theorem canonicalBase_primrec : Primrec canonicalBase := Canonical.Effective.canonicalize_primrec

theorem canonicalBase_value (q : Nat) (hq : baseCheck q = true) :
    base (canonicalBase q) = base q :=
  Canonical.canonicalize_value q ((baseCheck_exact q).mp hq).1

theorem canonicalBase_check (q : Nat) (hq : baseCheck q = true) :
    baseCheck (canonicalBase q) = true := by
  have hs := (baseCheck_exact q).mp hq
  apply (baseCheck_exact _).mpr
  exact ⟨Canonical.check_original (Canonical.canonicalize_check q hs.1),
    by rw [canonicalBase_value q hq]; exact hs.2⟩

theorem canonicalBase_dictionary (q : Nat) (hq : baseCheck q = true) :
    PublicEpsilonSourceDictionary.inputCheck (canonicalBase q) = true := by
  exact Bool.and_eq_true.mpr
    ⟨Canonical.canonicalize_check q ((baseCheck_exact q).mp hq).1, canonicalBase_check q hq⟩

theorem canonicalBase_lowCheck (q c : Nat) (hq : baseCheck q = true) :
    lowCheckCode (canonicalBase q) c = lowCheckCode q c :=
  lowCheckCode_invariant _ q c (canonicalBase_check q hq) hq (canonicalBase_value q hq)

theorem canonicalBase_interpretation (q c : Nat) (hq : baseCheck q = true) :
    interpretation (canonicalBase q) c = interpretation q c :=
  interpretation_invariant _ q c (canonicalBase_value q hq)

/-- Actual positive proper classification supplies the exact unbounded
return caller on the WHOLE original RAW LOW interval. -/
theorem positive_return_guard (q s c : Nat)
    (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hl : PublicEpsilonSourceDictionary.level q = s + 1)
    (hb : PublicEpsilonSourceDictionary.basePoint q = false) :
    UnboundedPublicReturn.inputCheck s (PublicEpsilonSourceDictionary.positiveRootCode q) c = true ↔
      lowCheckCode q c = true := by
  have hs := PublicEpsilonSourceDictionary.positive_spec q s hq hl hb
  simp only [UnboundedPublicReturn.inputCheck_exact, hs.2.1, ← hs.2.2.2, true_and]

theorem positive_return_spec (q s c : Nat)
    (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hl : PublicEpsilonSourceDictionary.level q = s + 1)
    (hb : PublicEpsilonSourceDictionary.basePoint q = false)
    (hc : lowCheckCode q c = true) :
    Canonical.check (UnboundedPublicReturn.publicCode s (PublicEpsilonSourceDictionary.positiveRootCode q) c) = true ∧
      unionInterpretation (UnboundedPublicReturn.publicCode s
        (PublicEpsilonSourceDictionary.positiveRootCode q) c) = interpretation q c := by
  have hs := UnboundedPublicReturn.publicCode_spec s _ c
    ((positive_return_guard q s c hq hl hb).mpr hc)
  simpa only [← (PublicEpsilonSourceDictionary.positive_spec q s hq hl hb).2.2.2] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UniformPublicReturn
