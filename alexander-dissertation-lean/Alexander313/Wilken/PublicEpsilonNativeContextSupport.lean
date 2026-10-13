import Alexander313.Wilken.PublicEpsilonSourceDictionary
import Alexander313.Wilken.HereditaryNativeBoundedPublicReturnCodes
import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnCodes

/-!
# Genuine original native context callers from the public epsilon dictionary

Existing source spelling invariance already proves numerical admission and
denotation agreement. Weak Normality, accepted codes and the actual raw
comparator also agree. The finite classifier selects the genuine original
public context at base points; proper cases retain their literal canonical
alpha code. This supplies original parser/return callers, not mu invariance
or an unbounded arbitrary-q SAME-value translator. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary

theorem input_baseCheck (q : Nat) (hq : inputCheck q = true) : NativeContext.baseCheck q = true :=
  (Bool.and_eq_true.mp hq).2

theorem native_check_invariant (q v : Nat) (hq : NativeContext.baseCheck q = true)
    (hv : NativeContext.baseCheck v = true) (he : NativeContext.base q = NativeContext.base v)
    (t : RelativeTerm Nat) : NativeContext.check q t = NativeContext.check v t := by
  simpa only [NativeContext.checkCode_code] using NativeContext.checkCode_invariant q v t.code hq hv he

theorem native_normal_iff (q v : Nat) (he : NativeContext.base q = NativeContext.base v)
    (t : RelativeTerm Nat) :
    NativeContext.Comparison.Normal q t ↔ NativeContext.Comparison.Normal v t := by
  induction t <;> simp_all only [NativeContext.Comparison.Normal, NativeContext.denote_invariant q v he]

theorem native_acceptedCode_invariant (q v c : Nat) (hq : NativeContext.baseCheck q = true)
    (hv : NativeContext.baseCheck v = true) (he : NativeContext.base q = NativeContext.base v) :
    NativeContext.Comparison.acceptedCode q c = NativeContext.Comparison.acceptedCode v c := by
  apply Bool.eq_iff_iff.mpr
  simp only [NativeContext.Comparison.acceptedCode_exact,
    NativeContext.checkCode_invariant q v c hq hv he, native_normal_iff q v he]

theorem native_lessRawCode_invariant (q v c d : Nat) (hq : NativeContext.baseCheck q = true)
    (hv : NativeContext.baseCheck v = true) (he : NativeContext.base q = NativeContext.base v) :
    NativeContext.Normalization.lessRawCode q c d = NativeContext.Normalization.lessRawCode v c d := by
  apply Bool.eq_iff_iff.mpr
  simp only [NativeContext.Normalization.lessRawCode_exact,
    NativeContext.checkCode_invariant q v c hq hv he, NativeContext.checkCode_invariant q v d hq hv he,
    NativeContext.interpretation_invariant q v c he, NativeContext.interpretation_invariant q v d he]

def referenceContext (q : Nat) : Nat := cond (basePoint q)
  (NativePublicBridge.contextCode (sourceIndex q)) q

theorem referenceContext_primrec : Primrec referenceContext :=
  basePoint_primrec.cond (NativePublicBridge.contextCode_primrec.comp sourceIndex_primrec) Primrec.id

theorem referenceContext_spec (q : Nat) (hq : inputCheck q = true) :
    NativeContext.baseCheck (referenceContext q) = true ∧
      NativeContext.base (referenceContext q) = NativeContext.base q := by
  cases hb : basePoint q with
  | false => simp only [referenceContext, hb, Bool.cond_false]; exact ⟨input_baseCheck q hq, rfl⟩
  | true =>
    have hs := base_point_spec q hq hb
    simp only [referenceContext, hb, Bool.cond_true]
    exact ⟨hs.2.1, hs.2.2⟩

theorem referenceContext_checkCode (q c : Nat) (hq : inputCheck q = true) :
    NativeContext.checkCode (referenceContext q) c = NativeContext.checkCode q c := by
  have hs := referenceContext_spec q hq
  exact NativeContext.checkCode_invariant _ q c hs.1 (input_baseCheck q hq) hs.2

theorem referenceContext_lowCheckCode (q c : Nat) (hq : inputCheck q = true) :
    NativeContext.lowCheckCode (referenceContext q) c = NativeContext.lowCheckCode q c := by
  have hs := referenceContext_spec q hq
  exact NativeContext.lowCheckCode_invariant _ q c hs.1 (input_baseCheck q hq) hs.2

theorem referenceContext_normal (q : Nat) (hq : inputCheck q = true) (t : RelativeTerm Nat) :
    NativeContext.Comparison.Normal (referenceContext q) t ↔ NativeContext.Comparison.Normal q t :=
  native_normal_iff _ q (referenceContext_spec q hq).2 t

theorem referenceContext_acceptedCode (q c : Nat) (hq : inputCheck q = true) :
    NativeContext.Comparison.acceptedCode (referenceContext q) c = NativeContext.Comparison.acceptedCode q c := by
  have hs := referenceContext_spec q hq
  exact native_acceptedCode_invariant _ q c hs.1 (input_baseCheck q hq) hs.2

theorem referenceContext_interpretation (q c : Nat) (hq : inputCheck q = true) :
    NativeContext.interpretation (referenceContext q) c = NativeContext.interpretation q c :=
  NativeContext.interpretation_invariant _ q c (referenceContext_spec q hq).2

theorem referenceContext_lessRawCode (q c d : Nat) (hq : inputCheck q = true) :
    NativeContext.Normalization.lessRawCode (referenceContext q) c d =
      NativeContext.Normalization.lessRawCode q c d := by
  have hs := referenceContext_spec q hq
  exact native_lessRawCode_invariant _ q c d hs.1 (input_baseCheck q hq) hs.2

/-- Basepoint classification is about the reference base q. A separate
original checked Normal high theta-zero root at that base supplies the real
legacy root guard; q itself is never presented as a proper mu root. -/
theorem base_point_high_root (q a : Nat) (hq : inputCheck q = true) (hb : basePoint q = true)
    (t : RelativeTerm Nat) (ha : a = (.theta 0 t).code)
    (hc : NativeContext.check q (.theta 0 t) = true)
    (hn : NativeContext.Comparison.Normal q t) (hh : 1 < t.outerSort) :
    NativeContext.Iota.rootCheck (sourceIndex q) a = true := by
  have hs := base_point_spec q hq hb
  apply (NativeContext.Iota.rootCheck_exact _ _).mpr
  exact ⟨t, ha, (native_check_invariant _ q hs.2.1 (input_baseCheck q hq) hs.2.2 _).trans hc,
    (native_normal_iff _ q hs.2.2 t).mpr hn, hh⟩

/-- At a base point the actual whole original raw LOW interval returns to
the public carrier through the existing original-context LOW producer. -/
def base_point_publicCode (q c : Nat) : Nat := Canonical.canonicalize
  (NativeContext.LowArithmetic.publicCode (sourceIndex q) c)

theorem base_point_publicCode_primrec : Primrec₂ base_point_publicCode :=
  Canonical.Effective.canonicalize_primrec.comp
    (NativeContext.LowArithmetic.publicCode_primrec.comp
      (sourceIndex_primrec.comp Primrec.fst) Primrec.snd)

theorem base_point_publicCode_spec (q c : Nat) (hq : inputCheck q = true)
    (hb : basePoint q = true) (hc : NativeContext.lowCheckCode q c = true) :
    Canonical.check (base_point_publicCode q c) = true ∧
      unionInterpretation (base_point_publicCode q c) = NativeContext.interpretation q c := by
  have hs := base_point_spec q hq hb
  have hl : NativeContext.lowCheckCode (NativePublicBridge.contextCode (sourceIndex q)) c = true :=
    (NativeContext.lowCheckCode_invariant _ q c hs.2.1 (input_baseCheck q hq) hs.2.2).trans hc
  have hp := NativeContext.LowArithmetic.publicCode_spec _ c hl
  exact ⟨Canonical.canonicalize_check _ hp.1,
    (Canonical.canonicalize_value _ hp.1).trans
      (hp.2.trans (NativeContext.interpretation_invariant _ q c hs.2.2))⟩

/-- Exact canonical alpha identity transports the actual source-one return
guard literally. The real selected source alpha-plus bound remains explicit. -/
theorem source_one_return_guard (q c : Nat) (hq : inputCheck q = true) (hl : level q = 0) :
    SourceOneIota.BoundedPublicReturn.inputCheck (sourceRootCode q) c = true ↔
      NativeContext.lowCheckCode q c = true ∧ NativeContext.interpretation q c <
        SourceOneIota.Enclosure.sourceAlphaPlus (sourceRootCode q) := by
  have hs := source_one_spec q hq hl
  simp only [SourceOneIota.BoundedPublicReturn.inputCheck_exact, hs.1, ← hs.2.2, true_and]

theorem positive_return_guard (q s c : Nat) (hq : inputCheck q = true)
    (hl : level q = s + 1) (hb : basePoint q = false) :
    NativeContext.BoundedPublicReturn.inputCheck s (positiveRootCode q) c = true ↔
      NativeContext.lowCheckCode q c = true ∧ NativeContext.interpretation q c <
        NativeContext.Iota.AlphaPlus.sourceValue s (positiveRootCode q) := by
  have hs := positive_spec q s hq hl hb
  simp only [NativeContext.BoundedPublicReturn.inputCheck_exact, hs.2.1, ← hs.2.2.2, true_and]

theorem source_one_return_spec (q c : Nat) (hq : inputCheck q = true) (hl : level q = 0)
    (hc : NativeContext.lowCheckCode q c = true)
    (hb : NativeContext.interpretation q c < SourceOneIota.Enclosure.sourceAlphaPlus (sourceRootCode q)) :
    Canonical.check (SourceOneIota.BoundedPublicReturn.publicCode (sourceRootCode q) c) = true ∧
      unionInterpretation (SourceOneIota.BoundedPublicReturn.publicCode (sourceRootCode q) c) =
        NativeContext.interpretation q c := by
  have hs := SourceOneIota.BoundedPublicReturn.publicCode_spec _ c
    ((source_one_return_guard q c hq hl).mpr ⟨hc, hb⟩)
  simpa only [← (source_one_spec q hq hl).2.2] using hs

theorem positive_return_spec (q s c : Nat) (hq : inputCheck q = true)
    (hl : level q = s + 1) (hb : basePoint q = false)
    (hc : NativeContext.lowCheckCode q c = true)
    (hbound : NativeContext.interpretation q c < NativeContext.Iota.AlphaPlus.sourceValue s (positiveRootCode q)) :
    Canonical.check (NativeContext.BoundedPublicReturn.publicCode s (positiveRootCode q) c) = true ∧
      unionInterpretation (NativeContext.BoundedPublicReturn.publicCode s (positiveRootCode q) c) =
        NativeContext.interpretation q c := by
  have hs := NativeContext.BoundedPublicReturn.publicCode_spec s _ c
    ((positive_return_guard q s c hq hl hb).mpr ⟨hc, hbound⟩)
  simpa only [← (positive_spec q s hq hl hb).2.2.2] using hs

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary
