import Alexander313.Wilken.HereditaryAddition
import Alexander313.Wilken.HereditaryBaseArithmeticCodes
import Alexander313.Wilken.HereditaryDifference
import Alexander313.Effective.HereditaryOrdinalLabels

/-!
# Canonical addition, subtraction, genuine successors and finite numerals

The actual source sum is canonicalized by the proved bounded search. Its
unchanged ordinal interpretation determines unique output codes. The small
label operation has actual ordinal addition, with derived zero, associativity
and left cancellation. A literal theta-zero code at base one constructs one,
then actual sums construct successors and every finite numeral. Canonicalizing
the constructed full subtraction gives actual small-label right difference,
including zero on reversed admitted inputs. All raw code algorithms are
uniformly primitive recursive. Correctness retains original
admission; no code order or supplied arithmetic oracle is used. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.CanonicalArithmetic

open Alexander313.HereditaryOrdinalLabels (Label value labelOf zeroLabel
  zeroCode zeroCode_checked zeroLabel_value label_lt_iff value_injective)

def canonicalSum (q v : Nat) : Nat := Canonical.canonicalize (Addition.unionAdd q v)

theorem canonicalSum_primrec : Primrec₂ canonicalSum :=
  (Canonical.Effective.canonicalize_primrec.comp Addition.unionAdd_primrec).to₂

theorem canonicalSum_checked (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    Canonical.check (canonicalSum q v) = true :=
  Canonical.canonicalize_check _ (Addition.unionAdd_checked q v hq hv).1

theorem canonicalSum_original (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionCheck (canonicalSum q v) = true :=
  Canonical.check_original (canonicalSum_checked q v hq hv)

theorem canonicalSum_value (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionInterpretation (canonicalSum q v) = unionInterpretation q + unionInterpretation v :=
  (Canonical.canonicalize_value _ (Addition.unionAdd_checked q v hq hv).1).trans
    (Addition.unionAdd_checked q v hq hv).2.2

theorem canonicalSum_unique (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (c : Nat) (hc : Canonical.check c = true)
    (hvalue : unionInterpretation c = unionInterpretation q + unionInterpretation v) :
    c = canonicalSum q v :=
  Canonical.check_value_injective c _ hc (canonicalSum_checked q v hq hv)
    (hvalue.trans (canonicalSum_value q v hq hv).symm)

theorem canonicalSum_invariant (q v q' v' : Nat)
    (hq : unionCheck q = true) (hv : unionCheck v = true)
    (hq' : unionCheck q' = true) (hv' : unionCheck v' = true)
    (hleft : unionInterpretation q = unionInterpretation q')
    (hright : unionInterpretation v = unionInterpretation v') :
    canonicalSum q v = canonicalSum q' v' := by
  apply canonicalSum_unique q' v' hq' hv' _ (canonicalSum_checked q v hq hv)
  rw [canonicalSum_value q v hq hv, hleft, hright]

def labelAdd (μ ν : Label) : Label :=
  ⟨canonicalSum μ.1 ν.1, canonicalSum_checked μ.1 ν.1
    (Canonical.check_original μ.2) (Canonical.check_original ν.2)⟩

theorem labelAdd_value (μ ν : Label) : value (labelAdd μ ν) = value μ + value ν :=
  canonicalSum_value μ.1 ν.1 (Canonical.check_original μ.2) (Canonical.check_original ν.2)

theorem labelAdd_zero (μ : Label) : labelAdd μ zeroLabel = μ := by
  apply value_injective
  simp only [labelAdd_value, zeroLabel_value, add_zero]

theorem zero_labelAdd (μ : Label) : labelAdd zeroLabel μ = μ := by
  apply value_injective
  simp only [labelAdd_value, zeroLabel_value, zero_add]

theorem labelAdd_assoc (μ ν ξ : Label) :
    labelAdd (labelAdd μ ν) ξ = labelAdd μ (labelAdd ν ξ) := by
  apply value_injective
  simp only [labelAdd_value, add_assoc]

theorem labelAdd_left_cancel {μ ν ξ : Label} (h : labelAdd μ ν = labelAdd μ ξ) : ν = ξ := by
  apply value_injective
  exact add_left_cancel (by simpa only [labelAdd_value] using congrArg value h)

private theorem canonical_arithmetic_ord_add_right_lt (α β γ : Ordinal.{0}) :
    α + β < α + γ ↔ β < γ := by
  constructor
  · intro h
    by_contra hn
    exact h.not_ge (add_le_add_right (le_of_not_gt hn) α)
  · intro h
    exact lt_of_le_of_ne (add_le_add_right h.le α) (fun he => h.ne (add_left_cancel he))

theorem labelAdd_right_lt_iff (μ ν ξ : Label) :
    labelAdd μ ν < labelAdd μ ξ ↔ ν < ξ := by
  simp only [label_lt_iff, labelAdd_value, canonical_arithmetic_ord_add_right_lt]

def oneCode : Nat := Nat.pair 0 (BaseArithmetic.freshCode 0)

theorem oneCode_checked : unionCheck oneCode = true := by
  simpa only [oneCode, unionCheck_pair] using
    BaseArithmetic.checkCode_old 0 _ (BaseArithmetic.fresh_checked 0)

theorem oneCode_value : unionInterpretation oneCode = 1 := by
  simpa only [oneCode, unionInterpretation_pair, finiteBase_zero] using BaseArithmetic.fresh_value 0

def oneLabel : Label :=
  ⟨Canonical.canonicalize oneCode, Canonical.canonicalize_check oneCode oneCode_checked⟩

theorem oneLabel_value : value oneLabel = 1 :=
  (Canonical.canonicalize_value oneCode oneCode_checked).trans oneCode_value

def successorCode (q : Nat) : Nat := canonicalSum q oneCode

theorem successorCode_primrec : Primrec successorCode :=
  canonicalSum_primrec.comp Primrec.id (Primrec.const oneCode)

theorem successorCode_checked (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (successorCode q) = true := canonicalSum_checked q oneCode hq oneCode_checked

theorem successorCode_value (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation (successorCode q) = unionInterpretation q + 1 := by
  simpa only [successorCode, oneCode_value] using canonicalSum_value q oneCode hq oneCode_checked

def labelSuccessor (μ : Label) : Label := labelAdd μ oneLabel

theorem labelSuccessor_value (μ : Label) : value (labelSuccessor μ) = value μ + 1 := by
  simpa only [labelSuccessor, oneLabel_value] using labelAdd_value μ oneLabel

theorem label_lt_successor (μ : Label) : μ < labelSuccessor μ := by
  rw [label_lt_iff, labelSuccessor_value]
  exact lt_add_one _

theorem label_below_successor_iff (μ ν : Label) :
    ν < labelSuccessor μ ↔ value ν ≤ value μ := by
  rw [label_lt_iff, labelSuccessor_value]
  exact Order.lt_add_one_iff

def numeralCode : Nat → Nat
  | 0 => Canonical.canonicalize zeroCode
  | n + 1 => successorCode (numeralCode n)

theorem numeralCode_primrec : Primrec numeralCode := by
  have h : Primrec₂ (fun (_ : Unit) n => Nat.rec (motive := fun _ => Nat)
      (Canonical.canonicalize zeroCode) (fun _ c => successorCode c) n) :=
    Primrec.nat_rec (Primrec.const (Canonical.canonicalize zeroCode))
      ((successorCode_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂)
  exact (h.comp (Primrec.const ()) Primrec.id).of_eq (by
    intro n
    induction n <;> simp_all [numeralCode])

theorem numeralCode_checked (n : Nat) : Canonical.check (numeralCode n) = true := by
  induction n with
  | zero => exact Canonical.canonicalize_check zeroCode zeroCode_checked
  | succ n ih => exact successorCode_checked _ (Canonical.check_original ih)

theorem numeralCode_value (n : Nat) : unionInterpretation (numeralCode n) = (n : Ordinal.{0}) := by
  induction n with
  | zero =>
    change unionInterpretation (Canonical.canonicalize zeroCode) = 0
    exact (Canonical.canonicalize_value zeroCode zeroCode_checked).trans
      Alexander313.HereditaryOrdinalLabels.zeroCode_value
  | succ n ih =>
    rw [numeralCode, successorCode_value _ (Canonical.check_original (numeralCode_checked n)), ih]
    simp only [Nat.cast_succ]

def numeralLabel (n : Nat) : Label := ⟨numeralCode n, numeralCode_checked n⟩

theorem numeralLabel_value (n : Nat) : value (numeralLabel n) = (n : Ordinal.{0}) :=
  numeralCode_value n

theorem numeralLabel_zero : numeralLabel 0 = zeroLabel := rfl

theorem numeralLabel_succ (n : Nat) : numeralLabel (n + 1) = labelSuccessor (numeralLabel n) := by
  apply value_injective
  rw [numeralLabel_value, labelSuccessor_value, numeralLabel_value]
  simp only [Nat.cast_succ]

theorem successor_below_limit (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation q + 1 < finiteBaseLimit :=
  (Hereditary.lt_finiteBaseLimit_iff_code _).mpr
    ⟨successorCode q, Canonical.check_original (successorCode_checked q hq),
      successorCode_value q hq⟩

/-- The argument order agrees with the original right-difference algorithm:
the first value is removed from the second. Reversed admitted inputs yield
the unique canonical zero. -/
def canonicalSubtraction (q v : Nat) : Nat :=
  Canonical.canonicalize (Difference.unionSubtraction q v)

theorem canonicalSubtraction_primrec : Primrec₂ canonicalSubtraction :=
  (Canonical.Effective.canonicalize_primrec.comp Difference.unionSubtraction_primrec).to₂

theorem canonicalSubtraction_checked (q v : Nat)
    (hq : unionCheck q = true) (hv : unionCheck v = true) :
    Canonical.check (canonicalSubtraction q v) = true :=
  Canonical.canonicalize_check _ (Difference.unionSubtraction_checked q v hq hv).1

theorem canonicalSubtraction_value (q v : Nat)
    (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionInterpretation (canonicalSubtraction q v) = unionInterpretation v - unionInterpretation q :=
  (Canonical.canonicalize_value _ (Difference.unionSubtraction_checked q v hq hv).1).trans
    (Difference.unionSubtraction_checked q v hq hv).2.2

def labelDifference (μ ν : Label) : Label :=
  ⟨canonicalSubtraction μ.1 ν.1, canonicalSubtraction_checked μ.1 ν.1
    (Canonical.check_original μ.2) (Canonical.check_original ν.2)⟩

theorem labelDifference_value (μ ν : Label) : value (labelDifference μ ν) = value ν - value μ :=
  canonicalSubtraction_value μ.1 ν.1 (Canonical.check_original μ.2) (Canonical.check_original ν.2)

theorem labelAdd_difference (μ ν : Label) (h : value μ ≤ value ν) :
    labelAdd μ (labelDifference μ ν) = ν := by
  apply value_injective
  rw [labelAdd_value, labelDifference_value]
  exact Ordinal.add_sub_cancel_of_le h

theorem labelDifference_zero_iff (μ ν : Label) :
    labelDifference μ ν = zeroLabel ↔ value ν ≤ value μ := by
  constructor
  · intro h
    have hz : value ν - value μ = 0 := by
      simpa only [labelDifference_value, zeroLabel_value] using congrArg value h
    have hb : value ν ≤ value μ + 0 := Ordinal.sub_le.mp (show value ν - value μ ≤ 0 by rw [hz])
    simpa only [add_zero] using hb
  · intro h
    apply value_injective
    rw [labelDifference_value, zeroLabel_value]
    have hb : value ν - value μ ≤ 0 := Ordinal.sub_le.mpr (by simpa only [add_zero] using h)
    exact le_antisymm hb (zero_le)

end Alexander313.Wilken.RelativeTerm.Hereditary.CanonicalArithmetic
