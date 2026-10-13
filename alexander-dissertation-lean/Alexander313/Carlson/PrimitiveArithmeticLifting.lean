import Alexander313.Carlson.ComputableArithmeticLifting
import Alexander313.Carlson.PrimitiveFiniteExtrema
import Alexander313.Carlson.PrimitiveFiniteOperations
import Alexander313.Carlson.PrimitiveRationalData

/-!
# Primitive-recursive rational arithmetic lifting

Finite filtering and extrema certify the original upper-anchor and lower-bound
operations, including their fallback branches. Rational arithmetic then
certifies the affine placement and the existing arithmetic lifting map and
target carrier on all typed inputs.

The family combinators use an ordinary coded parameter and a certified
two-argument evaluation function. No coding of a function space is introduced.
No pattern, monotonicity, boundedness, or nonemptiness hypothesis is required
to certify these total data operations. Their geometric correctness remains
the separate specification in `ComputableArithmeticLifting`.
-/

namespace Alexander313.Carlson.PrimitiveArithmeticLifting

open Encodable PrimitiveFiniteData PrimitiveFiniteOperations
  PrimitiveRationalData PrimitiveFiniteExtrema

/-- The original finite upper-anchor lookup is primitive recursive whenever
the ambient order comparison is primitive recursive. -/
theorem computableUp_primrec {α : Type*} [Primcodable α] [LinearOrder α]
    (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec₂ (@Str.computableUp α _) :=
  ((minD_primrec hle).comp
    ((finset_filter hle).comp Primrec.snd Primrec.fst) Primrec.snd).of_eq fun _ => rfl

/-- Rational upper-anchor lookup has a closed primitive-recursive certificate. -/
theorem rat_computableUp_primrec : Primrec₂ (@Str.computableUp ℚ _) :=
  computableUp_primrec rat_le

/-- The greatest old point below an anchor, or the original `a - 1` fallback. -/
theorem computablePredBound_primrec : Primrec₂ Str.computablePredBound :=
  ((maxD_primrec rat_le).comp (rational_below.comp Primrec.snd Primrec.fst)
    (rat_sub.comp Primrec.snd (Primrec.const 1))).of_eq fun _ => rfl

variable {σ : Type*} [Primcodable σ]

/-- The original affine placement is primitive recursive in every supplied
finite carrier, anchor, and query, including an empty source carrier. -/
theorem computablePlaceBelow_primrec
    {B X : σ → Finset ℚ} {a x : σ → ℚ}
    (hB : Primrec B) (hX : Primrec X) (ha : Primrec a) (hx : Primrec x) :
    Primrec (fun s => Str.computablePlaceBelow (B s) (X s) (a s) (x s)) := by
  let c : σ → ℚ := fun s => Str.computablePredBound (B s) (a s)
  let l : σ → ℚ := fun s => minD (X s) 0
  let u : σ → ℚ := fun s => maxD (X s) 0
  have hc : Primrec c := computablePredBound_primrec.comp hB ha
  have hl : Primrec l := (minD_primrec rat_le).comp hX (Primrec.const 0)
  have hu : Primrec u := (maxD_primrec rat_le).comp hX (Primrec.const 0)
  refine (Primrec.ite (finset_nonempty.comp hX)
    (rat_add.comp hc
      (rat_mul.comp
        (rat_div.comp (rat_sub.comp ha hc)
          (rat_add.comp (rat_sub.comp hu hl) (Primrec.const 2)))
        (rat_add.comp (rat_sub.comp hx hl) (Primrec.const 1)))) hx).of_eq ?_
  intro s
  by_cases hs : (X s).Nonempty
  · simp [Str.computablePlaceBelow, c, l, u, minD, maxD, hs]
  · simp [Str.computablePlaceBelow, hs]

/-- Uniform evaluation of a supplied primitive-recursive family of base maps.
The source, extended source, target, and evaluation point are arbitrary data. -/
theorem computableMap_primrec
    {A Aplus B : σ → Finset ℚ} {h : σ → ℚ → ℚ} {x : σ → ℚ}
    (hA : Primrec A) (hAplus : Primrec Aplus) (hB : Primrec B)
    (hh : Primrec₂ h) (hx : Primrec x) :
    Primrec (fun s => ArithmeticLifting.computableMap
      (A s) (Aplus s) (B s) (h s) (x s)) :=
  Primrec.ite (finset_mem.comp hx hA) (hh.comp Primrec.id hx)
    (computablePlaceBelow_primrec hB hAplus
      (hh.comp Primrec.id (rat_computableUp_primrec.comp hA hx)) hx)

/-- Uniform finite target construction for a certified family of base maps. -/
theorem computableTarget_primrec
    {A Aplus B : σ → Finset ℚ} {h : σ → ℚ → ℚ}
    (hA : Primrec A) (hAplus : Primrec Aplus) (hB : Primrec B)
    (hh : Primrec₂ h) :
    Primrec (fun s => ArithmeticLifting.computableTarget
      (A s) (Aplus s) (B s) (h s)) := by
  have hf : Primrec₂ (fun s x => ArithmeticLifting.computableMap
      (A s) (Aplus s) (B s) (h s) x) :=
    computableMap_primrec (hA.comp Primrec.fst) (hAplus.comp Primrec.fst)
      (hB.comp Primrec.fst)
      (hh.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂ Primrec.snd
  exact finset_union.comp hB ((finset_image hf).comp Primrec.id hAplus)

/-- The source, extended source, and old target, in that order. -/
abbrev Carriers := Finset ℚ × Finset ℚ × Finset ℚ

/-- Placement uses the input tuple `((B, X), (a, x))`. -/
theorem computablePlaceBelow_eval_primrec :
    Primrec (fun p : (Finset ℚ × Finset ℚ) × (ℚ × ℚ) =>
      Str.computablePlaceBelow p.1.1 p.1.2 p.2.1 p.2.2) :=
  computablePlaceBelow_primrec (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)

/-- A fixed certified base map, with carrier tuple `(A, Aplus, B)` and
a separate rational evaluation argument. -/
theorem computableMap_fixed_primrec {h : ℚ → ℚ} (hh : Primrec h) :
    Primrec₂ (fun (p : Carriers) x =>
      ArithmeticLifting.computableMap p.1 p.2.1 p.2.2 h x) :=
  computableMap_primrec (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (hh.comp Primrec.snd).to₂ Primrec.snd

/-- A fixed certified base map yields a primitive-recursive target carrier. -/
theorem computableTarget_fixed_primrec {h : ℚ → ℚ} (hh : Primrec h) :
    Primrec (fun p : Carriers =>
      ArithmeticLifting.computableTarget p.1 p.2.1 p.2.2 h) :=
  computableTarget_primrec Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd) (hh.comp Primrec.snd).to₂

/-- The identity base map used by the fair sequence needs no extra input. -/
theorem computableMap_id_primrec :
    Primrec₂ (fun (p : Carriers) x =>
      ArithmeticLifting.computableMap p.1 p.2.1 p.2.2 id x) :=
  computableMap_fixed_primrec Primrec.id

theorem computableTarget_id_primrec :
    Primrec (fun p : Carriers =>
      ArithmeticLifting.computableTarget p.1 p.2.1 p.2.2 id) :=
  computableTarget_fixed_primrec Primrec.id

/-- An upper-anchor program on the ordinary typed finite-set and rational codes. -/
theorem computableUp_program : ∃ c : Nat.Partrec.Code,
    ∀ (S : Finset ℚ) (x : ℚ),
      c.eval (Nat.pair (encode S) (encode x)) =
        Part.some (encode (Str.computableUp S x)) := by
  obtain ⟨c, hc⟩ := exists_program rat_computableUp_primrec
  exact ⟨c, fun S x => hc (S, x)⟩

/-- A lower-bound program includes the empty-filter fallback. -/
theorem computablePredBound_program : ∃ c : Nat.Partrec.Code,
    ∀ (B : Finset ℚ) (a : ℚ),
      c.eval (Nat.pair (encode B) (encode a)) =
        Part.some (encode (Str.computablePredBound B a)) := by
  obtain ⟨c, hc⟩ := exists_program computablePredBound_primrec
  exact ⟨c, fun B a => hc (B, a)⟩

/-- The affine-placement program accepts the tuple `((B, X), (a, x))`. -/
theorem computablePlaceBelow_program : ∃ c : Nat.Partrec.Code,
    ∀ (B X : Finset ℚ) (a x : ℚ),
      c.eval (encode ((B, X), (a, x))) =
        Part.some (encode (Str.computablePlaceBelow B X a x)) := by
  obtain ⟨c, hc⟩ := exists_program computablePlaceBelow_eval_primrec
  exact ⟨c, fun B X a x => hc ((B, X), (a, x))⟩

/-- A fixed primitive-recursive base map has a machine implementation for
lifting-map evaluation on input `((A, Aplus, B), x)`. -/
theorem computableMap_program {h : ℚ → ℚ} (hh : Primrec h) :
    ∃ c : Nat.Partrec.Code, ∀ (A Aplus B : Finset ℚ) (x : ℚ),
      c.eval (encode ((A, Aplus, B), x)) =
        Part.some (encode (ArithmeticLifting.computableMap A Aplus B h x)) := by
  obtain ⟨c, hc⟩ := exists_program (computableMap_fixed_primrec hh)
  exact ⟨c, fun A Aplus B x => hc ((A, Aplus, B), x)⟩

/-- The corresponding target program accepts the carrier tuple `(A, Aplus, B)`. -/
theorem computableTarget_program {h : ℚ → ℚ} (hh : Primrec h) :
    ∃ c : Nat.Partrec.Code, ∀ A Aplus B : Finset ℚ,
      c.eval (encode (A, Aplus, B)) =
        Part.some (encode (ArithmeticLifting.computableTarget A Aplus B h)) := by
  obtain ⟨c, hc⟩ := exists_program (computableTarget_fixed_primrec hh)
  exact ⟨c, fun A Aplus B => hc (A, Aplus, B)⟩

/-- Closed machine representation of identity-base lifting-map evaluation. -/
theorem computableMap_id_program :
    ∃ c : Nat.Partrec.Code, ∀ (A Aplus B : Finset ℚ) (x : ℚ),
      c.eval (encode ((A, Aplus, B), x)) =
        Part.some (encode (ArithmeticLifting.computableMap A Aplus B id x)) :=
  computableMap_program Primrec.id

/-- Closed machine representation of the identity-base target carrier. -/
theorem computableTarget_id_program :
    ∃ c : Nat.Partrec.Code, ∀ A Aplus B : Finset ℚ,
      c.eval (encode (A, Aplus, B)) =
        Part.some (encode (ArithmeticLifting.computableTarget A Aplus B id)) :=
  computableTarget_program Primrec.id

end Alexander313.Carlson.PrimitiveArithmeticLifting
