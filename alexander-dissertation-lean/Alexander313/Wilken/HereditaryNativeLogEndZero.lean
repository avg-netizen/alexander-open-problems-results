import Alexander313.Wilken.HereditaryNativeFixedPoint
import Alexander313.Wilken.HereditaryLogEndZero

/-!
# Actual zero-last-exponent decision at native coded epsilon bases

The genuine native ANF word supplies its last principal component at every
cardinal sort. A literal native parameter for the original public unit is
admitted because the actual epsilon base is strictly above one. Native
comparison and the real empty-ANF test therefore decide zero last exponent
on exactly the original weak-normal domain. The actual normalizer supplies
the full original raw domain. No native logarithm producer, public return
conversion or support/spelling oracle is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEndZero

theorem one_lt_base (q : Nat) (hq : baseCheck q = true) : 1 < base q :=
  lt_of_le_of_ne (Order.one_le_iff_pos.mpr (base_pos q hq)) (FixedPoint.base_ne_one q hq).symm

/-- A literal native leaf for the genuinely admitted public unit. -/
def unitCode : Nat := (RelativeTerm.parameter CanonicalArithmetic.oneCode : RelativeTerm Nat).code

theorem unitCode_value (q : Nat) : interpretation q unitCode = 1 := by
  simpa only [unitCode, interpretation_code, denote, RelativeTerm.eval, parameters] using
    CanonicalArithmetic.oneCode_value

theorem unitCode_accepted (q : Nat) (hq : baseCheck q = true) :
    Decomposition.inputCheck q unitCode = true := by
  have hp : parameterCheck q CanonicalArithmetic.oneCode = true :=
    (parameterCheck_exact q _).mpr ⟨CanonicalArithmetic.oneCode_checked,
      ((baseCheck_exact q).mp hq).1, by
        rw [parameters, CanonicalArithmetic.oneCode_value]
        exact one_lt_base q hq⟩
  have ht : check q (.parameter CanonicalArithmetic.oneCode) = true := by
    simp only [check, hq, finiteCheck_parameter, hp, Bool.true_and]
  exact (Decomposition.inputCheck_exact q unitCode).mpr ⟨by
    simpa only [unitCode, checkCode_code] using ht, by
    simp only [unitCode, ThetaCourse.rawTree_code, Comparison.Normal]⟩

def endAtom (c : Nat) : RelativeTerm Nat :=
  ((Decomposition.word c).reverse[0]?).getD Normalization.zeroTree

theorem endAtom_primrec : Primrec endAtom :=
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.list_reverse.comp Decomposition.word_primrec)
      (Primrec.const 0)) (Primrec.const Normalization.zeroTree)

private theorem first_map {alpha : Type} (f : alpha → Ordinal.{0})
    (as : List alpha) (z : alpha) :
    f (as[0]?.getD z) = (as.map f)[0]?.getD (f z) := by
  cases as <;> rfl

theorem endAtom_value (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    denote q (endAtom c) = Hereditary.LogEnd.endValue (interpretation q c) := by
  rw [endAtom, first_map, Normalization.zeroTree_denote, List.map_reverse,
    (Decomposition.word_spec q c hc).2]
  rfl

theorem endAtom_checked (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    check q (endAtom c) = true ∧ Comparison.Normal q (endAtom c) := by
  cases hw : (Decomposition.word c).reverse with
  | nil =>
    have hq := (Bool.and_eq_true.mp (Decomposition.input_tree q c hc).1).1
    simpa only [endAtom, hw, List.getElem?_nil, Option.getD_none] using
      And.intro (Normalization.zeroTree_checked q hq) (Normalization.zeroTree_normal q)
  | cons a as =>
    have ha : a ∈ Decomposition.word c := by
      have h : a ∈ (Decomposition.word c).reverse := by rw [hw]; exact List.mem_cons_self
      simpa only [List.mem_reverse] using h
    have hs := (Decomposition.word_spec q c hc).1 a ha
    simpa only [endAtom, hw, List.getElem?_cons_zero, Option.getD_some] using
      And.intro hs.1 hs.2.1

def endCode (c : Nat) : Nat := (endAtom c).code

theorem endCode_primrec : Primrec endCode := code_primrec.comp endAtom_primrec

theorem endCode_accepted (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    Decomposition.inputCheck q (endCode c) = true := by
  have hs := endAtom_checked q c hc
  apply (Decomposition.inputCheck_exact q _).mpr
  refine ⟨(checkCode_exact q _).mpr ⟨endAtom c, rfl, hs.1⟩, ?_⟩
  simpa only [endCode, ThetaCourse.rawTree_code] using hs.2

theorem endCode_value (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    interpretation q (endCode c) = Hereditary.LogEnd.endValue (interpretation q c) := by
  simpa only [endCode, interpretation_code] using endAtom_value q c hc

theorem endCode_unit_iff (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    Comparison.equalCode q (endCode c) unitCode = true ↔
      Hereditary.LogEnd.endValue (interpretation q c) = 1 := by
  have hq := (Bool.and_eq_true.mp (Decomposition.input_tree q c hc).1).1
  have hs := (Decomposition.inputCheck_exact q _).mp (endCode_accepted q c hc)
  have hu := (Decomposition.inputCheck_exact q _).mp (unitCode_accepted q hq)
  simpa only [hs.1, hs.2, hu.1, hu.2, endCode_value q c hc, unitCode_value,
    true_and] using Comparison.equalCode_exact q (endCode c) unitCode

def zeroCheck (q c : Nat) : Bool := Decomposition.inputCheck q c &&
  (FixedPoint.zeroCheck c || Comparison.equalCode q (endCode c) unitCode)

theorem zeroCheck_primrec : Primrec₂ zeroCheck :=
  (Primrec.and.comp Decomposition.inputCheck_primrec
    (Primrec.or.comp (FixedPoint.zeroCheck_primrec.comp Primrec.snd)
      (Comparison.equalCode_primrec.comp (Primrec.fst.pair
        ((endCode_primrec.comp Primrec.snd).pair (Primrec.const unitCode)))))).to₂

theorem zeroCheck_exact (q c : Nat) : zeroCheck q c = true ↔
    Decomposition.inputCheck q c = true ∧
      Hereditary.LogEndZero.SourceZero (interpretation q c) := by
  rw [zeroCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, by simpa only [Bool.or_eq_true, FixedPoint.zeroCheck_exact q c hc,
      endCode_unit_iff q c hc, Hereditary.LogEndZero.SourceZero] using h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, by simpa only [Bool.or_eq_true, FixedPoint.zeroCheck_exact q c hc,
      endCode_unit_iff q c hc, Hereditary.LogEndZero.SourceZero] using h⟩

theorem zeroCheck_correct (q c : Nat) (hc : Decomposition.inputCheck q c = true) :
    zeroCheck q c = true ↔ Hereditary.LogEndZero.SourceZero (interpretation q c) := by
  simp only [zeroCheck_exact, hc, true_and]

theorem zeroCheck_source (q c : Nat) : zeroCheck q c = true ↔
    checkCode q c = true ∧ Comparison.Normal q (ThetaCourse.rawTree c) ∧
      Hereditary.LogEndZero.SourceZero (interpretation q c) := by
  rw [zeroCheck_exact, Decomposition.inputCheck_exact, and_assoc]

theorem zeroCheck_exponent (q c : Nat) (hc : Decomposition.inputCheck q c = true)
    (eta : Ordinal.{0}) (hs : Hereditary.LogEnd.SourceLogSpec true (interpretation q c) eta) :
    zeroCheck q c = true ↔ eta = 0 :=
  (zeroCheck_correct q c hc).trans (Hereditary.LogEndZero.sourceLogSpec_zero_iff _ _ hs).symm

theorem zeroCheck_invariant (q c v d : Nat)
    (hc : Decomposition.inputCheck q c = true) (hd : Decomposition.inputCheck v d = true)
    (he : interpretation q c = interpretation v d) : zeroCheck q c = zeroCheck v d := by
  have h : zeroCheck q c = true ↔ zeroCheck v d = true := by
    simp only [zeroCheck_exact, hc, hd, true_and, he]
  cases hleft : zeroCheck q c <;> cases hright : zeroCheck v d <;> simp_all

def rawZeroCheck (q c : Nat) : Bool := checkCode q c &&
  zeroCheck q (Normalization.normalizeCode q c)

theorem rawZeroCheck_primrec : Primrec₂ rawZeroCheck :=
  (Primrec.and.comp checkCode_primrec
    (zeroCheck_primrec.comp Primrec.fst Normalization.Effective.normalizeCode_primrec)).to₂

theorem rawZeroCheck_exact (q c : Nat) : rawZeroCheck q c = true ↔
    checkCode q c = true ∧ Hereditary.LogEndZero.SourceZero (interpretation q c) := by
  rw [rawZeroCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, h⟩
    have hn := Normalization.normalizeCode_accepted q c hc
    have hs := (zeroCheck_exact q _).mp h
    exact ⟨hc, by simpa only [hn.2] using hs.2⟩
  · rintro ⟨hc, h⟩
    have hn := Normalization.normalizeCode_accepted q c hc
    exact ⟨hc, (zeroCheck_exact q _).mpr ⟨hn.1, by simpa only [hn.2] using h⟩⟩

theorem rawZeroCheck_correct (q c : Nat) (hc : checkCode q c = true) :
    rawZeroCheck q c = true ↔ Hereditary.LogEndZero.SourceZero (interpretation q c) := by
  simp only [rawZeroCheck_exact, hc, true_and]

theorem rawZeroCheck_exponent (q c : Nat) (hc : checkCode q c = true)
    (eta : Ordinal.{0}) (hs : Hereditary.LogEnd.SourceLogSpec true (interpretation q c) eta) :
    rawZeroCheck q c = true ↔ eta = 0 :=
  (rawZeroCheck_correct q c hc).trans (Hereditary.LogEndZero.sourceLogSpec_zero_iff _ _ hs).symm

theorem rawZeroCheck_invariant (q c v d : Nat)
    (hc : checkCode q c = true) (hd : checkCode v d = true)
    (he : interpretation q c = interpretation v d) : rawZeroCheck q c = rawZeroCheck v d := by
  have h : rawZeroCheck q c = true ↔ rawZeroCheck v d = true := by
    simp only [rawZeroCheck_exact, hc, hd, true_and, he]
  cases hleft : rawZeroCheck q c <;> cases hright : rawZeroCheck v d <;> simp_all

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.LogEndZero
