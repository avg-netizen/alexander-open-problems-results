import Alexander313.Wilken.HereditaryCanonicalArithmetic

/-!
# Actual right multiplication by a natural coefficient

A literal natural recursion starts at an admitted canonical zero and performs
the actual source addition at every successor. Its value is α * n, with the
coefficient on the right and cast to the actual finite ordinal. Canonicalizing
each constructed sum gives genuine unique normal outputs throughout.

The public total operation guards the unchanged original union domain and
returns raw zero on malformed source inputs, including at coefficient zero.
Every natural coefficient is a raw Nat; no ordinal coefficient decoder,
general ordinal multiplication algorithm or arithmetic oracle is used.
All proof terms are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FiniteMultiplication

open CanonicalArithmetic
open Alexander313.HereditaryOrdinalLabels (Label value zeroLabel zeroCode zeroCode_checked
  zeroCode_value zeroLabel_value value_injective)

/-- The executing finite recursion uses real source addition at each step. -/
def product (q : Nat) : Nat → Nat
  | 0 => Canonical.canonicalize zeroCode
  | n + 1 => canonicalSum (product q n) q

theorem product_primrec : Primrec₂ product := by
  have h := Primrec.nat_rec (Primrec.const (Canonical.canonicalize zeroCode))
    ((canonicalSum_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂)
  exact h.of_eq (by intro q n; induction n <;> simp_all [product])

theorem product_checked (q n : Nat) (hq : unionCheck q = true) :
    Canonical.check (product q n) = true := by
  induction n with
  | zero => exact Canonical.canonicalize_check zeroCode zeroCode_checked
  | succ n ih => exact canonicalSum_checked _ q (Canonical.check_original ih) hq

theorem product_value (q n : Nat) (hq : unionCheck q = true) :
    unionInterpretation (product q n) = unionInterpretation q * (n : Ordinal.{0}) := by
  induction n with
  | zero =>
    simpa only [product, Nat.cast_zero, mul_zero] using
      (Canonical.canonicalize_value zeroCode zeroCode_checked).trans zeroCode_value
  | succ n ih =>
    rw [product, canonicalSum_value _ q
      (Canonical.check_original (product_checked q n hq)) hq, ih]
    simp only [Nat.cast_succ, mul_add_one]

def multiplyCode (q n : Nat) : Nat := cond (unionCheck q) (product q n) 0

theorem multiplyCode_primrec : Primrec₂ multiplyCode :=
  ((Uniform.unionCheck_primrec.comp Primrec.fst).cond product_primrec (Primrec.const 0)).to₂

theorem multiplyCode_rejected (q n : Nat) (hq : unionCheck q = false) :
    multiplyCode q n = 0 := by simp only [multiplyCode, hq, Bool.cond_false]

theorem multiplyCode_checked (q n : Nat) (hq : unionCheck q = true) :
    Canonical.check (multiplyCode q n) = true := by
  simpa only [multiplyCode, hq, Bool.cond_true] using product_checked q n hq

theorem multiplyCode_original (q n : Nat) (hq : unionCheck q = true) :
    unionCheck (multiplyCode q n) = true := Canonical.check_original (multiplyCode_checked q n hq)

theorem multiplyCode_normal (q n : Nat) (hq : unionCheck q = true) :
    Theta.Normal (multiplyCode q n).unpair.1 (ThetaCourse.rawTree (multiplyCode q n).unpair.2) :=
  Canonical.check_normal (multiplyCode_checked q n hq)

theorem multiplyCode_value (q n : Nat) (hq : unionCheck q = true) :
    unionInterpretation (multiplyCode q n) = unionInterpretation q * (n : Ordinal.{0}) := by
  simpa only [multiplyCode, hq, Bool.cond_true] using product_value q n hq

/-- Canonical output uniqueness is derived from the original value map. -/
theorem multiplyCode_unique (q n : Nat) (hq : unionCheck q = true) (c : Nat)
    (hc : Canonical.check c = true)
    (hvalue : unionInterpretation c = unionInterpretation q * (n : Ordinal.{0})) :
    c = multiplyCode q n :=
  Canonical.check_value_injective c _ hc (multiplyCode_checked q n hq)
    (hvalue.trans (multiplyCode_value q n hq).symm)

theorem multiplyCode_invariant (q v n : Nat) (hq : unionCheck q = true)
    (hv : unionCheck v = true) (he : unionInterpretation q = unionInterpretation v) :
    multiplyCode q n = multiplyCode v n := by
  apply multiplyCode_unique v n hv _ (multiplyCode_checked q n hq)
  rw [multiplyCode_value q n hq, he]

theorem multiplyCode_zero (q : Nat) (hq : unionCheck q = true) :
    multiplyCode q 0 = Canonical.canonicalize zeroCode := by
  simp only [multiplyCode, hq, Bool.cond_true, product]

theorem multiplyCode_one (q : Nat) (hq : unionCheck q = true) :
    multiplyCode q 1 = Canonical.canonicalize q := by
  apply Canonical.check_value_injective _ _ (multiplyCode_checked q 1 hq)
    (Canonical.canonicalize_check q hq)
  rw [multiplyCode_value q 1 hq, Canonical.canonicalize_value q hq]
  simp only [Nat.cast_one, mul_one]

theorem multiplyCode_succ (q n : Nat) (hq : unionCheck q = true) :
    multiplyCode q (n + 1) = canonicalSum (multiplyCode q n) q := by
  simp only [multiplyCode, hq, Bool.cond_true, product]

private theorem finite_multiplication_ordinal_coefficient_add (α : Ordinal.{0}) (m n : Nat) :
    α * ((m + n : Nat) : Ordinal.{0}) = α * (m : Ordinal.{0}) + α * (n : Ordinal.{0}) := by
  induction n with
  | zero => simp only [Nat.add_zero, Nat.cast_zero, mul_zero, add_zero]
  | succ n ih =>
    calc
      α * ((m + (n + 1) : Nat) : Ordinal.{0}) = α * ((m + n : Nat) : Ordinal.{0}) + α := by
        simp only [Nat.add_succ, Nat.cast_succ, mul_add_one]
      _ = (α * (m : Ordinal.{0}) + α * (n : Ordinal.{0})) + α := by rw [ih]
      _ = α * (m : Ordinal.{0}) + (α * (n : Ordinal.{0}) + α) := add_assoc _ _ _
      _ = α * (m : Ordinal.{0}) + α * ((n + 1 : Nat) : Ordinal.{0}) := by
        simp only [Nat.cast_succ, mul_add_one]

/-- Coefficient addition gives the exact canonical sum of the two products. -/
theorem multiplyCode_add (q m n : Nat) (hq : unionCheck q = true) :
    multiplyCode q (m + n) = canonicalSum (multiplyCode q m) (multiplyCode q n) := by
  apply Canonical.check_value_injective _ _ (multiplyCode_checked q (m + n) hq)
    (canonicalSum_checked _ _ (multiplyCode_original q m hq) (multiplyCode_original q n hq))
  rw [multiplyCode_value q (m + n) hq,
    canonicalSum_value _ _ (multiplyCode_original q m hq) (multiplyCode_original q n hq),
    multiplyCode_value q m hq, multiplyCode_value q n hq]
  exact finite_multiplication_ordinal_coefficient_add _ m n

theorem multiplyCode_below_limit (q n : Nat) (hq : unionCheck q = true) :
    unionInterpretation q * (n : Ordinal.{0}) < finiteBaseLimit :=
  (Hereditary.lt_finiteBaseLimit_iff_code _).mpr
    ⟨multiplyCode q n, multiplyCode_original q n hq, multiplyCode_value q n hq⟩

theorem multiplyCode_computable : Computable₂ multiplyCode := multiplyCode_primrec.to_comp

def labelMultiply (μ : Label) (n : Nat) : Label :=
  ⟨multiplyCode μ.1 n, multiplyCode_checked μ.1 n (Canonical.check_original μ.2)⟩

theorem labelMultiply_value (μ : Label) (n : Nat) :
    value (labelMultiply μ n) = value μ * (n : Ordinal.{0}) :=
  multiplyCode_value μ.1 n (Canonical.check_original μ.2)

theorem labelMultiply_zero (μ : Label) : labelMultiply μ 0 = zeroLabel := by
  apply value_injective
  simp only [labelMultiply_value, zeroLabel_value, Nat.cast_zero, mul_zero]

theorem labelMultiply_one (μ : Label) : labelMultiply μ 1 = μ := by
  apply value_injective
  simp only [labelMultiply_value, Nat.cast_one, mul_one]

theorem labelMultiply_succ (μ : Label) (n : Nat) :
    labelMultiply μ (n + 1) = labelAdd (labelMultiply μ n) μ := by
  apply value_injective
  simp only [labelMultiply_value, labelAdd_value, Nat.cast_succ, mul_add_one]

theorem labelMultiply_add (μ : Label) (m n : Nat) :
    labelMultiply μ (m + n) = labelAdd (labelMultiply μ m) (labelMultiply μ n) := by
  apply value_injective
  simp only [labelMultiply_value, labelAdd_value]
  exact finite_multiplication_ordinal_coefficient_add _ m n

end Alexander313.Wilken.RelativeTerm.Hereditary.FiniteMultiplication
