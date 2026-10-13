import Alexander313.Carlson.PrimitiveFiniteOperations
import Alexander313.Carlson.PrimitiveRationalPresentation
import Alexander313.Carlson.PrimitiveArithmeticLifting
import Alexander313.Carlson.ComputablePatternLifting

/-!
# Primitive recursive rational pattern-lifting data

The existing presentation map and lifting constructor act on uniformly
coded finite data. Supplied rational maps are first-order parameter families:
their evaluation on the coded parameter and a rational argument must be
primitive recursive. The finite relation tables use the actual carrier
filters and the bounded source search of the executable constructor.

Primitive recursiveness and the machine specifications are total on their
typed inputs. Pattern, continuity, and embedding hypotheses enter only the
separate semantic lifting specification.
-/

namespace Alexander313.Carlson.PrimitivePatternLifting

open Encodable Finite
open PrimitiveFiniteOperations

variable {σ : Type*} [Primcodable σ]

/-- Mapping a uniformly supplied presentation under a certified family of
rational maps is primitive recursive. The original carrier filters discard
off-carrier edges before taking images, and the map may identify labels. -/
theorem map_primrec {P : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hh : Primrec₂ h) :
    Primrec (fun s => (P s).map (h s)) := by
  have hU := PrimitiveRationalPresentation.carrier_primrec.comp hP
  have hsquare := finset_product.comp hU hU
  have h₁ : PrimrecRel (fun s (xy : ℚ × ℚ) => xy ∈ (P s).r₁) :=
    PrimitiveRationalPresentation.relation₁_mem.comp (hP.comp Primrec.fst) Primrec.snd
  have h₂ : PrimrecRel (fun s (xy : ℚ × ℚ) => xy ∈ (P s).r₂) :=
    PrimitiveRationalPresentation.relation₂_mem.comp (hP.comp Primrec.fst) Primrec.snd
  have hedge : Primrec₂ (fun s (xy : ℚ × ℚ) => (h s xy.1, h s xy.2)) :=
    (hh.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (hh.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  exact PrimitiveRationalPresentation.mk_primrec
    ((finset_image hh).comp Primrec.id hU)
    ((finset_image hedge).comp Primrec.id ((finset_filter h₁).comp Primrec.id hsquare))
    ((finset_image hedge).comp Primrec.id ((finset_filter h₂).comp Primrec.id hsquare))

/-- A single machine maps all presentations and rational maps supplied by
the same coded parameter family. -/
theorem map_program {P : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hh : Primrec₂ h) :
    ∃ c : Nat.Partrec.Code, ∀ s,
      c.eval (encode s) = Part.some (encode ((P s).map (h s))) :=
  exists_program (map_primrec hP hh)

private theorem predicate_ite {p q r : σ → Prop} [DecidablePred p]
    (hp : PrimrecPred p) (hq : PrimrecPred q) (hr : PrimrecPred r) :
    PrimrecPred (fun s => if p s then q s else r s) := by
  refine ((hp.and hq).or (hp.not.and hr)).of_eq ?_
  intro s
  by_cases hs : p s <;> simp [hs]

private theorem firstRelation_primrec {P : σ → RationalPresentation} {x y : σ → ℚ}
    (hP : Primrec P) (hx : Primrec x) (hy : Primrec y) :
    PrimrecPred (fun s => (P s).toStr.r₁ (x s) (y s)) :=
  PrimitiveRationalPresentation.relation₁_mem.comp hP (hx.pair hy)

private theorem secondRelation_primrec {P : σ → RationalPresentation} {x y : σ → ℚ}
    (hP : Primrec P) (hx : Primrec x) (hy : Primrec y) :
    PrimrecPred (fun s => (P s).toStr.r₂ (x s) (y s)) :=
  PrimitiveRationalPresentation.relation₂_mem.comp hP (hx.pair hy)

private abbrev firstEdge (A : Finset ℚ) (S Q : RationalPresentation) (xy : ℚ × ℚ) : Prop :=
  if xy.1 ∈ Q.U then
    if xy.2 ∈ Q.U then Q.toStr.r₁ xy.1 xy.2
    else xy.1 ≤ xy.2 ∧ Q.toStr.r₁ xy.1 (Str.computableUp A xy.2)
  else
    if xy.2 ∈ Q.U then
      S.toStr.r₁ xy.1 (Str.computableUp A xy.1) ∧
        Q.toStr.r₁ (Str.computableUp A xy.1) xy.2
    else S.toStr.r₁ xy.1 xy.2

private abbrev incomingSecond (A : Finset ℚ) (S Q : RationalPresentation) (x y : ℚ) : Prop :=
  ∃ a ∈ S.U, x ≤ a ∧ S.toStr.r₁ a (Str.computableUp A a) ∧
    Q.toStr.r₂ x (Str.computableUp A a) ∧ S.toStr.r₂ a y

private abbrev secondEdge (A : Finset ℚ) (S Q : RationalPresentation) (xy : ℚ × ℚ) : Prop :=
  if xy.1 ∈ Q.U then
    if xy.2 ∈ Q.U then Q.toStr.r₂ xy.1 xy.2
    else incomingSecond A S Q xy.1 xy.2
  else
    if xy.2 ∈ Q.U then
      S.toStr.r₂ xy.1 (Str.computableUp A xy.1) ∧
        Q.toStr.r₂ (Str.computableUp A xy.1) xy.2
    else S.toStr.r₂ xy.1 xy.2

private theorem firstEdge_primrec {A : σ → Finset ℚ} {S Q : σ → RationalPresentation}
    (hA : Primrec A) (hS : Primrec S) (hQ : Primrec Q) :
    PrimrecRel (fun s xy => firstEdge (A s) (S s) (Q s) xy) := by
  have hA' : Primrec (fun p : σ × (ℚ × ℚ) => A p.1) := hA.comp Primrec.fst
  have hS' : Primrec (fun p : σ × (ℚ × ℚ) => S p.1) := hS.comp Primrec.fst
  have hQ' : Primrec (fun p : σ × (ℚ × ℚ) => Q p.1) := hQ.comp Primrec.fst
  have hx : Primrec (fun p : σ × (ℚ × ℚ) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : σ × (ℚ × ℚ) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hupx := PrimitiveArithmeticLifting.rat_computableUp_primrec.comp hA' hx
  have hupy := PrimitiveArithmeticLifting.rat_computableUp_primrec.comp hA' hy
  have hxold := PrimitiveRationalPresentation.carrier_mem.comp hQ' hx
  have hyold := PrimitiveRationalPresentation.carrier_mem.comp hQ' hy
  unfold firstEdge
  exact predicate_ite hxold
    (predicate_ite hyold (firstRelation_primrec hQ' hx hy)
      ((PrimitiveRationalData.rat_le.comp hx hy).and (firstRelation_primrec hQ' hx hupy)))
    (predicate_ite hyold
      ((firstRelation_primrec hS' hx hupx).and (firstRelation_primrec hQ' hupx hy))
      (firstRelation_primrec hS' hx hy))

private theorem incomingSecond_primrec {A : σ → Finset ℚ}
    {S Q : σ → RationalPresentation} {x y : σ → ℚ}
    (hA : Primrec A) (hS : Primrec S) (hQ : Primrec Q) (hx : Primrec x) (hy : Primrec y) :
    PrimrecPred (fun s => incomingSecond (A s) (S s) (Q s) (x s) (y s)) := by
  have hup : Primrec (fun p : ℚ × σ => Str.computableUp (A p.2) p.1) :=
    PrimitiveArithmeticLifting.rat_computableUp_primrec.comp (hA.comp Primrec.snd) Primrec.fst
  have hp : PrimrecRel (fun (a : ℚ) s =>
      x s ≤ a ∧ (S s).toStr.r₁ a (Str.computableUp (A s) a) ∧
        (Q s).toStr.r₂ (x s) (Str.computableUp (A s) a) ∧ (S s).toStr.r₂ a (y s)) :=
    (PrimitiveRationalData.rat_le.comp (hx.comp Primrec.snd) Primrec.fst).and
      ((firstRelation_primrec (hS.comp Primrec.snd) Primrec.fst hup).and
        ((secondRelation_primrec (hQ.comp Primrec.snd) (hx.comp Primrec.snd) hup).and
          (secondRelation_primrec (hS.comp Primrec.snd) Primrec.fst (hy.comp Primrec.snd))))
  exact (exists_mem hp).comp (PrimitiveRationalPresentation.carrier_primrec.comp hS) Primrec.id

private theorem secondEdge_primrec {A : σ → Finset ℚ} {S Q : σ → RationalPresentation}
    (hA : Primrec A) (hS : Primrec S) (hQ : Primrec Q) :
    PrimrecRel (fun s xy => secondEdge (A s) (S s) (Q s) xy) := by
  have hA' : Primrec (fun p : σ × (ℚ × ℚ) => A p.1) := hA.comp Primrec.fst
  have hS' : Primrec (fun p : σ × (ℚ × ℚ) => S p.1) := hS.comp Primrec.fst
  have hQ' : Primrec (fun p : σ × (ℚ × ℚ) => Q p.1) := hQ.comp Primrec.fst
  have hx : Primrec (fun p : σ × (ℚ × ℚ) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : σ × (ℚ × ℚ) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hupx := PrimitiveArithmeticLifting.rat_computableUp_primrec.comp hA' hx
  have hxold := PrimitiveRationalPresentation.carrier_mem.comp hQ' hx
  have hyold := PrimitiveRationalPresentation.carrier_mem.comp hQ' hy
  unfold secondEdge
  exact predicate_ite hxold
    (predicate_ite hyold (secondRelation_primrec hQ' hx hy)
      (incomingSecond_primrec hA' hS' hQ' hx hy))
    (predicate_ite hyold
      ((secondRelation_primrec hS' hx hupx).and (secondRelation_primrec hQ' hupx hy))
      (secondRelation_primrec hS' hx hy))

/-- Construct the actual normalized lifting tables from uniformly coded
finite data. The incoming second relation searches precisely the supplied
finite source carrier, and the output filters both tables to `U ×ˢ U`. -/
theorem liftingCandidate_primrec {A U : σ → Finset ℚ} {S Q : σ → RationalPresentation}
    (hA : Primrec A) (hS : Primrec S) (hQ : Primrec Q) (hU : Primrec U) :
    Primrec (fun s => RationalPresentation.liftingCandidate (A s) (S s) (Q s) (U s)) := by
  have hsquare := finset_product.comp hU hU
  exact PrimitiveRationalPresentation.mk_primrec hU
    ((finset_filter (firstEdge_primrec hA hS hQ)).comp Primrec.id hsquare)
    ((finset_filter (secondEdge_primrec hA hS hQ)).comp Primrec.id hsquare)

theorem liftingCandidate_program {A U : σ → Finset ℚ} {S Q : σ → RationalPresentation}
    (hA : Primrec A) (hS : Primrec S) (hQ : Primrec Q) (hU : Primrec U) :
    ∃ c : Nat.Partrec.Code, ∀ s,
      c.eval (encode s) = Part.some
        (encode (RationalPresentation.liftingCandidate (A s) (S s) (Q s) (U s))) :=
  exists_program (liftingCandidate_primrec hA hS hQ hU)

/-- Evaluate the actual total lifting map at a uniformly coded rational
query. Every finite carrier and the base-map parameter remains explicit. -/
theorem liftMap_eval_primrec {P Pplus Q : σ → RationalPresentation}
    {h : σ → ℚ → ℚ} {x : σ → ℚ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q)
    (hh : Primrec₂ h) (hx : Primrec x) :
    Primrec (fun s => RationalPresentation.liftMap (P s) (Pplus s) (Q s) (h s) (x s)) :=
  PrimitiveArithmeticLifting.computableMap_primrec
    (PrimitiveRationalPresentation.carrier_primrec.comp hP)
    (PrimitiveRationalPresentation.carrier_primrec.comp hPplus)
    (PrimitiveRationalPresentation.carrier_primrec.comp hQ) hh hx

/-- Joint primitive recursiveness in the coded parameter and query point. -/
theorem liftMap_primrec {P Pplus Q : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hh : Primrec₂ h) :
    Primrec₂ (fun s x => RationalPresentation.liftMap (P s) (Pplus s) (Q s) (h s) x) := by
  have hbase : Primrec₂ (fun (p : σ × ℚ) y => h p.1 y) :=
    hh.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact liftMap_eval_primrec (hP.comp Primrec.fst) (hPplus.comp Primrec.fst)
    (hQ.comp Primrec.fst) hbase Primrec.snd

/-- The actual finite lifting target is primitive recursive for every
certified parameter family, including empty and semantically invalid data. -/
theorem liftTarget_primrec {P Pplus Q : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hh : Primrec₂ h) :
    Primrec (fun s => RationalPresentation.liftTarget (P s) (Pplus s) (Q s) (h s)) :=
  liftingCandidate_primrec
    ((finset_image hh).comp Primrec.id (PrimitiveRationalPresentation.carrier_primrec.comp hP))
    (map_primrec hPplus (liftMap_primrec hP hPplus hQ hh)) hQ
    (PrimitiveArithmeticLifting.computableTarget_primrec
      (PrimitiveRationalPresentation.carrier_primrec.comp hP)
      (PrimitiveRationalPresentation.carrier_primrec.comp hPplus)
      (PrimitiveRationalPresentation.carrier_primrec.comp hQ) hh)

/-- A single machine evaluates the actual lifting-map family on paired
parameter and rational-query encodings. -/
theorem liftMap_program {P Pplus Q : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hh : Primrec₂ h) :
    ∃ c : Nat.Partrec.Code, ∀ s x,
      c.eval (Nat.pair (encode s) (encode x)) = Part.some
        (encode (RationalPresentation.liftMap (P s) (Pplus s) (Q s) (h s) x)) := by
  obtain ⟨c, hc⟩ := exists_program (liftMap_primrec hP hPplus hQ hh)
  exact ⟨c, fun s x => hc (s, x)⟩

/-- A single machine produces the actual finite lifting target throughout
the coded parameter family. -/
theorem liftTarget_program {P Pplus Q : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hh : Primrec₂ h) :
    ∃ c : Nat.Partrec.Code, ∀ s,
      c.eval (encode s) = Part.some
        (encode (RationalPresentation.liftTarget (P s) (Pplus s) (Q s) (h s))) :=
  exists_program (liftTarget_primrec hP hPplus hQ hh)

/-- The same uniform target machine realizes the existing continuous
minimal-lifting specification whenever its input satisfies the semantic
pattern, continuity, and embedding hypotheses. These hypotheses certify
the result separately from the primitive recursive family assumptions. -/
theorem liftTarget_program_spec {P Pplus Q : σ → RationalPresentation} {h : σ → ℚ → ℚ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hh : Primrec₂ h) :
    ∃ c : Nat.Partrec.Code,
      (∀ s, c.eval (encode s) = Part.some
        (encode (RationalPresentation.liftTarget (P s) (Pplus s) (Q s) (h s)))) ∧
      ∀ s, (Pplus s).toStr.IsPattern → (Q s).toStr.IsPattern →
        Str.Continuous (P s).toStr (Pplus s).toStr →
        Str.ContinuousEmbedding (P s).toStr (Q s).toStr (h s) →
        PatternLifting (P s).toStr (Pplus s).toStr (Q s).toStr
          (RationalPresentation.liftTarget (P s) (Pplus s) (Q s) (h s)).toStr
          (h s) (RationalPresentation.liftMap (P s) (Pplus s) (Q s) (h s)) ∧
        PatternLifting.IsMinimal (P s).toStr (Pplus s).toStr (Q s).toStr
          (RationalPresentation.liftTarget (P s) (Pplus s) (Q s) (h s)).toStr (h s) ∧
        Str.Continuous (Q s).toStr
          (RationalPresentation.liftTarget (P s) (Pplus s) (Q s) (h s)).toStr := by
  obtain ⟨c, hc⟩ := liftTarget_program hP hPplus hQ hh
  refine ⟨c, hc, ?_⟩
  intro s hS hQpattern hC hE
  exact RationalPresentation.lift_spec hS hQpattern hC hE

/-- Three presentation records, associated as `(P, (Pplus, Q))`. -/
abbrev LiftInput := RationalPresentation × RationalPresentation × RationalPresentation

theorem identity_liftTarget_primrec : Primrec (fun p : LiftInput =>
    RationalPresentation.liftTarget p.1 p.2.1 p.2.2 id) :=
  liftTarget_primrec Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd) Primrec₂.right

/-- The identity-base lifting target used by the fair construction has one
machine for all three supplied presentation records. -/
theorem identity_liftTarget_program : ∃ c : Nat.Partrec.Code,
    ∀ P Pplus Q : RationalPresentation,
      c.eval (encode (P, Pplus, Q)) = Part.some
        (encode (RationalPresentation.liftTarget P Pplus Q id)) := by
  obtain ⟨c, hc⟩ := exists_program identity_liftTarget_primrec
  exact ⟨c, fun P Pplus Q => hc (P, Pplus, Q)⟩

/-- The identity-base lifting map is evaluated on an explicit presentation
triple and rational query; the output is a rational code. -/
theorem identity_liftMap_program : ∃ c : Nat.Partrec.Code,
    ∀ (P Pplus Q : RationalPresentation) (x : ℚ),
      c.eval (encode ((P, Pplus, Q), x)) = Part.some
        (encode (RationalPresentation.liftMap P Pplus Q id x)) := by
  obtain ⟨c, hc⟩ := liftMap_program (σ := LiftInput) Primrec.fst
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd) Primrec₂.right
  exact ⟨c, fun P Pplus Q x => hc (P, Pplus, Q) x⟩

end Alexander313.Carlson.PrimitivePatternLifting
