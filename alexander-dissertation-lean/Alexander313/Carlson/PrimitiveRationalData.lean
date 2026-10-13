import Mathlib.Computability.RE
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Encodable

/-!
# Primitive-recursive arithmetic on the existing rational codes

The executable Carlson construction stores rational numbers in finite
presentations. This module proves genuine `Primrec` results for that
arithmetic foundation. It retains mathlib's existing `Encodable ℚ`:
the code pairs the integer numerator code with its positive, coprime
denominator. Invalid normalized codes remain absent under decoding.

The integer and greatest-common-divisor lemmas below justify that code's
normalization test and arithmetic. They introduce no assumptions about
computability of a supplied Lean function. Finite-set operations and the
recursive certificate checker are separate components.
-/

namespace Alexander313.Carlson.PrimitiveRationalData

open Encodable

private theorem encode_int_ofNat (n : ℕ) :
    encode (Int.ofNat n) = 2 * n := rfl

private theorem encode_int_negSucc (n : ℕ) :
    encode (Int.negSucc n) = 2 * n + 1 := rfl

/-- The standard nonnegative integer constructor is primitive recursive. -/
theorem int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp (Primrec.nat_double.of_eq fun n => (encode_int_ofNat n).symm)

/-- The standard negative integer constructor is primitive recursive. -/
theorem int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp
    (Primrec.nat_double_succ.of_eq fun n => (encode_int_negSucc n).symm)

private theorem int_view : Primrec Equiv.intEquivNatSumNat := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq fun z => by cases z <;> rfl

/-- Case analysis on a coded integer, retaining a primitive-recursive
parameter in both branches. -/
theorem int_casesOn {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec fun a : α => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a) :=
  (Primrec.sumCasesOn (int_view.comp hf) hg hh).of_eq fun a => by
    cases f a <;> rfl

/-- Absolute numerator magnitudes use the usual integer code. -/
theorem int_natAbs : Primrec Int.natAbs := by
  exact (int_casesOn Primrec.id Primrec₂.right
    (Primrec.succ.comp Primrec.snd).to₂).of_eq fun z => by cases z <;> rfl

theorem int_negOfNat : Primrec Int.negOfNat :=
  (Primrec.nat_casesOn Primrec.id (Primrec.const (0 : ℤ))
    (int_negSucc.comp Primrec.snd).to₂).of_eq fun n => by cases n <;> rfl

theorem int_neg : Primrec (fun z : ℤ => -z) :=
  (int_casesOn Primrec.id (int_negOfNat.comp Primrec.snd).to₂
    (int_ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq fun z => by
      cases z <;> rfl

theorem int_subNatNat : Primrec₂ Int.subNatNat :=
  (Primrec.nat_casesOn (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
    (int_ofNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (int_negSucc.comp Primrec.snd).to₂).of_eq fun p => by
      unfold Int.subNatNat
      cases p.2 - p.1 <;> rfl

theorem int_add : Primrec₂ (fun a b : ℤ => a + b) := by
  refine (int_casesOn (f := fun p : ℤ × ℤ => p.1)
    (g := fun p n => Int.casesOn (motive := fun _ => ℤ) p.2
      (fun m => Int.ofNat (n + m)) (fun m => Int.subNatNat n (m + 1)))
    (h := fun p n => Int.casesOn (motive := fun _ => ℤ) p.2
      (fun m => Int.subNatNat m (n + 1)) (fun m => Int.negSucc (n + m + 1)))
    Primrec.fst ?_ ?_).of_eq ?_
  · exact (int_casesOn (Primrec.snd.comp Primrec.fst)
      (int_ofNat.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
      (int_subNatNat.comp (Primrec.snd.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).to₂).to₂
  · exact (int_casesOn (Primrec.snd.comp Primrec.fst)
      (int_subNatNat.comp Primrec.snd (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).to₂
      (int_negSucc.comp (Primrec.succ.comp
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂).to₂
  · rintro ⟨a, b⟩
    cases a <;> cases b <;> rfl

theorem int_sub : Primrec₂ (fun a b : ℤ => a - b) :=
  (int_add.comp Primrec.fst (int_neg.comp Primrec.snd)).of_eq fun p => by
    exact (sub_eq_add_neg p.1 p.2).symm

theorem int_mul : Primrec₂ (fun a b : ℤ => a * b) := by
  refine (int_casesOn (f := fun p : ℤ × ℤ => p.1)
    (g := fun p n => Int.casesOn (motive := fun _ => ℤ) p.2
      (fun m => Int.ofNat (n * m)) (fun m => Int.negOfNat (n * (m + 1))))
    (h := fun p n => Int.casesOn (motive := fun _ => ℤ) p.2
      (fun m => Int.negOfNat ((n + 1) * m)) (fun m => Int.ofNat ((n + 1) * (m + 1))))
    Primrec.fst ?_ ?_).of_eq ?_
  · exact (int_casesOn (Primrec.snd.comp Primrec.fst)
      (int_ofNat.comp (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
      (int_negOfNat.comp
        (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))).to₂).to₂
  · exact (int_casesOn (Primrec.snd.comp Primrec.fst)
      (int_negOfNat.comp
        (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂
      (int_ofNat.comp
        (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.succ.comp Primrec.snd))).to₂).to₂
  · rintro ⟨a, b⟩
    cases a <;> cases b <;> rfl

theorem int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, ?_⟩
  exact (int_casesOn Primrec.id (Primrec₂.const true) (Primrec₂.const false)).of_eq
    fun z => by
      cases z <;> simp
      rfl

theorem int_le : PrimrecRel (fun a b : ℤ => a ≤ b) :=
  (int_nonneg.comp (int_sub.comp Primrec.snd Primrec.fst)).of_eq fun p => by
    exact sub_nonneg

theorem int_lt : PrimrecRel (fun a b : ℤ => a < b) :=
  int_le.swap.not.of_eq fun _ _ => not_le

theorem int_sign : Primrec Int.sign :=
  (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const (0 : ℤ)))
    (Primrec.const (0 : ℤ))
    (Primrec.ite int_nonneg (Primrec.const (1 : ℤ)) (Primrec.const (-1 : ℤ)))).of_eq
    fun z => by
      cases z with
      | ofNat n =>
          cases n <;> simp
          omega
      | negSucc n => simp

/-- Euclidean division by a natural denominator, including denominator zero. -/
theorem int_edivNat : Primrec₂ (fun z : ℤ => fun d : ℕ => z / (d : ℤ)) := by
  refine (int_casesOn (f := fun p : ℤ × ℕ => p.1)
    (g := fun p n => Int.ofNat (n / p.2))
    (h := fun p n => if p.2 = 0 then 0 else Int.negSucc (n / p.2))
    Primrec.fst ?_ ?_).of_eq ?_
  · exact (int_ofNat.comp
      (Primrec.nat_div.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
  · exact (Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0))
      (Primrec.const (0 : ℤ))
      (int_negSucc.comp (Primrec.nat_div.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))).to₂
  · rintro ⟨z, d⟩
    cases z <;> cases d <;> simp
    rfl

theorem nat_dvd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst)
    (Primrec.const 0)).of_eq fun _ => Nat.dvd_iff_mod_eq_zero.symm

/-- Greatest common divisor is a bounded search for the greatest common
divisor, with the zero-zero case handled by the same total bound. -/
theorem nat_gcd : Primrec₂ Nat.gcd := by
  have hc : PrimrecRel (fun p : ℕ × ℕ => fun d : ℕ => d ∣ p.1 ∧ d ∣ p.2) :=
    (nat_dvd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (nat_dvd.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  apply (Primrec.nat_findGreatest Primrec.nat_add hc).of_eq
  rintro ⟨a, b⟩
  have hbound : Nat.gcd a b ≤ a + b := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha)).trans (Nat.le_add_right _ _)
  have hdiv := Nat.findGreatest_spec (P := fun d => d ∣ a ∧ d ∣ b)
    hbound ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩
  apply le_antisymm
  · by_cases hab : a = 0 ∧ b = 0
    · simp [hab.1, hab.2]
    · have hg : 0 < Nat.gcd a b := Nat.gcd_pos_iff.mpr (by omega)
      exact Nat.le_of_dvd hg (Nat.dvd_gcd hdiv.1 hdiv.2)
  · exact Nat.le_findGreatest hbound ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩

theorem nat_coprime : PrimrecRel Nat.Coprime :=
  (Primrec.eq.comp nat_gcd (Primrec.const 1)).of_eq fun _ => Iff.rfl

/-- Keep the exact rational encoding already used by stored certificates. -/
@[reducible] def rationalEncodable : Encodable ℚ := inferInstance

theorem encode_rat (q : ℚ) :
    @encode ℚ rationalEncodable q = Nat.pair (encode q.num) q.den := rfl

/-- Validity of a raw code uses the ordinary signed numerator encoding and
requires a positive denominator relatively prime to its magnitude. -/
def validCode (n : ℕ) : Prop :=
  0 < n.unpair.2 ∧ (Denumerable.ofNat ℤ n.unpair.1).natAbs.Coprime n.unpair.2

instance : DecidablePred validCode := fun n => by
  unfold validCode
  infer_instance

theorem validCode_primrec : PrimrecPred validCode :=
  (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.snd.comp Primrec.unpair)).and
    (nat_coprime.comp
      (int_natAbs.comp ((Primrec.ofNat ℤ).comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))

theorem encode_decode_rat (n : ℕ) :
    @encode (Option ℚ) (@Option.encodable ℚ rationalEncodable)
      (@decode ℚ rationalEncodable n) = if validCode n then n + 1 else 0 := by
  by_cases h : validCode n
  · simp only [h, if_true]
    let q : ℚ := ⟨Denumerable.ofNat ℤ n.unpair.1, n.unpair.2,
      Nat.ne_of_gt h.1, h.2⟩
    have hq : @encode ℚ rationalEncodable q = n := by
      rw [encode_rat]
      change Nat.pair (encode (Denumerable.ofNat ℤ n.unpair.1)) n.unpair.2 = n
      rw [Denumerable.encode_ofNat, Nat.pair_unpair]
    rw [← hq, Encodable.encodek, Encodable.encode_some]
  · simp only [h, if_false]
    simp only [Encodable.decode_ofEquiv, Encodable.decode_sigma_val,
      Denumerable.decode_eq_ofNat]
    dsimp only [Encodable.decode, Subtype.encodable, Encodable.decodeSubtype]
    simp only [Option.map_some, Option.bind_some, Denumerable.ofNat_nat]
    change ¬ (0 < n.unpair.2 ∧
      (Equiv.intEquivNat.symm n.unpair.1).natAbs.Coprime n.unpair.2) at h
    simp only [h, dite_false, Option.map_none, Encodable.encode_none]

/-- The existing rational encoding has a primitive-recursive round trip.
This instance adds a certificate, without changing any stored code. -/
instance instPrimcodableRat : Primcodable ℚ where
  toEncodable := rationalEncodable
  prim := (Primrec.nat_iff.mp
    (Primrec.ite validCode_primrec Primrec.succ (Primrec.const 0))).of_eq
      fun n => (encode_decode_rat n).symm

@[simp] theorem rational_encoding_unchanged :
    instPrimcodableRat.toEncodable = Rat.instEncodable := rfl

theorem rat_num : Primrec Rat.num :=
  ((Primrec.ofNat ℤ).comp
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.encode))).of_eq fun q => by
      rw [encode_rat, Nat.unpair_pair, Denumerable.ofNat_encode]

theorem rat_den : Primrec Rat.den :=
  (Primrec.snd.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    rw [encode_rat, Nat.unpair_pair]

/-- To certify rational output, it suffices to certify its normalized
numerator and denominator under the unchanged encoding. -/
theorem rat_of_components {α : Type*} [Primcodable α] {f : α → ℚ}
    (hn : Primrec fun a => (f a).num) (hd : Primrec fun a => (f a).den) : Primrec f :=
  Primrec.encode_iff.mp
    ((Primrec₂.natPair.comp (Primrec.encode.comp hn) hd).of_eq
      fun a => (encode_rat (f a)).symm)

/-- Normalizing an arbitrary integer numerator and natural denominator is
primitive recursive, including the standard zero-denominator convention. -/
theorem rat_mkRat : Primrec₂ mkRat := by
  apply rat_of_components
  · exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const (0 : ℤ))
      (int_edivNat.comp Primrec.fst
        (nat_gcd.comp Primrec.snd (int_natAbs.comp Primrec.fst)))).of_eq
      fun p => (Rat.num_mkRat p.1 p.2).symm
  · exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const 1)
      (Primrec.nat_div.comp Primrec.snd
        (nat_gcd.comp Primrec.snd (int_natAbs.comp Primrec.fst)))).of_eq
      fun p => (Rat.den_mkRat p.1 p.2).symm

theorem rat_neg : Primrec (fun q : ℚ => -q) :=
  rat_of_components ((int_neg.comp rat_num).of_eq fun q => (Rat.neg_num q).symm)
    (rat_den.of_eq fun q => (Rat.neg_den q).symm)

theorem rat_add : Primrec₂ (fun q r : ℚ => q + r) :=
  (rat_mkRat.comp
    (int_add.comp
      (int_mul.comp (rat_num.comp Primrec.fst) (int_ofNat.comp (rat_den.comp Primrec.snd)))
      (int_mul.comp (rat_num.comp Primrec.snd) (int_ofNat.comp (rat_den.comp Primrec.fst))))
    (Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd))).of_eq
      fun p => (Rat.add_def' p.1 p.2).symm

theorem rat_sub : Primrec₂ (fun q r : ℚ => q - r) :=
  (rat_add.comp Primrec.fst (rat_neg.comp Primrec.snd)).of_eq fun p => by
    exact (sub_eq_add_neg p.1 p.2).symm

theorem rat_mul : Primrec₂ (fun q r : ℚ => q * r) :=
  (rat_mkRat.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (rat_num.comp Primrec.snd))
    (Primrec.nat_mul.comp (rat_den.comp Primrec.fst) (rat_den.comp Primrec.snd))).of_eq
      fun p => (Rat.mul_eq_mkRat p.1 p.2).symm

theorem rat_inv : Primrec (fun q : ℚ => q⁻¹) :=
  rat_of_components
    ((int_mul.comp (int_sign.comp rat_num) (int_ofNat.comp rat_den)).of_eq
      fun q => (Rat.num_inv q).symm)
    ((Primrec.ite (Primrec.eq.comp rat_num (Primrec.const (0 : ℤ)))
      (Primrec.const 1) (int_natAbs.comp rat_num)).of_eq
      fun q => (Rat.den_inv q).symm)

theorem rat_div : Primrec₂ (fun q r : ℚ => q / r) :=
  (rat_mul.comp Primrec.fst (rat_inv.comp Primrec.snd)).of_eq
    fun p => (Rat.div_def p.1 p.2).symm

theorem rat_le : PrimrecRel (fun q r : ℚ => q ≤ r) :=
  (int_le.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_ofNat.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_ofNat.comp (rat_den.comp Primrec.fst)))).of_eq
      fun p => (Rat.le_iff p.1 p.2).symm

theorem rat_lt : PrimrecRel (fun q r : ℚ => q < r) :=
  (int_lt.comp
    (int_mul.comp (rat_num.comp Primrec.fst) (int_ofNat.comp (rat_den.comp Primrec.snd)))
    (int_mul.comp (rat_num.comp Primrec.snd) (int_ofNat.comp (rat_den.comp Primrec.fst)))).of_eq
      fun p => (Rat.lt_iff p.1 p.2).symm

/-- A primitive-recursive rational operation is represented by an actual
partial-recursive machine code on the unchanged input and output encodings. -/
theorem exists_code {α : Type*} [Primcodable α] {f : α → ℚ} (hf : Primrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a,
      c.eval (encode a) = Part.some (encode (f a)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  refine ⟨c, fun a => ?_⟩
  rw [hc]
  simp

/-- Addition of arbitrary rational inputs has a `Program`-language implementation. -/
theorem rat_add_program : ∃ c : Nat.Partrec.Code, ∀ q r : ℚ,
    c.eval (Nat.pair (encode q) (encode r)) = Part.some (encode (q + r)) := by
  obtain ⟨c, hc⟩ := exists_code rat_add
  exact ⟨c, fun q r => hc (q, r)⟩

/-- Subtraction of arbitrary rational inputs has a `Program`-language implementation. -/
theorem rat_sub_program : ∃ c : Nat.Partrec.Code, ∀ q r : ℚ,
    c.eval (Nat.pair (encode q) (encode r)) = Part.some (encode (q - r)) := by
  obtain ⟨c, hc⟩ := exists_code rat_sub
  exact ⟨c, fun q r => hc (q, r)⟩

/-- Multiplication of arbitrary rational inputs has a `Program`-language implementation. -/
theorem rat_mul_program : ∃ c : Nat.Partrec.Code, ∀ q r : ℚ,
    c.eval (Nat.pair (encode q) (encode r)) = Part.some (encode (q * r)) := by
  obtain ⟨c, hc⟩ := exists_code rat_mul
  exact ⟨c, fun q r => hc (q, r)⟩

/-- Rational division, with the ordinary total zero-denominator convention,
has a `Program`-language implementation. -/
theorem rat_div_program : ∃ c : Nat.Partrec.Code, ∀ q r : ℚ,
    c.eval (Nat.pair (encode q) (encode r)) = Part.some (encode (q / r)) := by
  obtain ⟨c, hc⟩ := exists_code rat_div
  exact ⟨c, fun q r => hc (q, r)⟩

/-- The actual strict rational order is the domain of a machine code on
paired rational codes. This is a concrete positive recognizer. -/
theorem rat_lt_program : ∃ c : Nat.Partrec.Code, ∀ q r : ℚ,
    (c.eval (Nat.pair (encode q) (encode r))).Dom ↔ q < r := by
  let evaluation : (ℚ × ℚ) → Part ℕ := fun p =>
    cond (decide (p.1 < p.2)) (Part.some 0) Part.none
  have heval : Partrec evaluation :=
    Partrec.cond rat_lt.decide.to_comp (Computable.const 0).partrec Partrec.none
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp heval
  refine ⟨c, fun q r => ?_⟩
  change (c.eval (encode (q, r))).Dom ↔ q < r
  rw [hc]
  simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
  change (evaluation (q, r)).Dom ↔ q < r
  by_cases h : q < r <;> simp [evaluation, h]

end Alexander313.Carlson.PrimitiveRationalData
