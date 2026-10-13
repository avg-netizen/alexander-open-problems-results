import Alexander313.Carlson.PrimitiveFiniteEnumeration
import Alexander313.Carlson.PrimitiveLiftingChecks

/-!
# Uniform primitive-recursive exhaustive finite minimality

Minimality ranges over every complete pair of target relation tables on the
fixed candidate carrier and every total competitor map. Both enumerations
are primitive recursive in the ambient dimensions. Each competitor is
decoded with the original codecs before the certified lifting predicate is
tested. Completeness of the enumeration supplies every original competitor;
decoding supplies soundness for every entry that is tested.

The candidate itself is not required to be a lifting by the original
minimality predicate. That remains the separate `checkLifting` condition.
Malformed external inputs reject, while a failed competitor decode imposes
no obligation. The final machine is total on all natural inputs.
-/

namespace Alexander313.Carlson.PrimitiveMinimalityChecks

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks
open PrimitiveFiniteEnumeration
open PrimitiveLiftingChecks (LiftingData liftingData_primrec liftingData_dataView_iff
  pairDecoded pairDecoded_primrec)

/-- Dimensions, old/extended source, old/candidate target, and the base map. -/
abbrev SearchInput := (ℕ × ℕ) × (Data × Data) × (Data × Data) × List ℕ

/-- A decoded competitor with the required carrier must receive the identity
covering from the proposed minimal target whenever it is a lifting. -/
def CompetitorData (x : SearchInput) (S : Data) (G : List ℕ) : Prop :=
  S.1 = x.2.2.1.2.1 →
    LiftingData x.2.1.1 x.2.1.2 x.2.2.1.1 S x.2.2.2 G →
      CoversIntoData x.2.2.1.2 S (List.range x.1.2)

instance (x : SearchInput) (S : Data) (G : List ℕ) : Decidable (CompetitorData x S G) := by
  unfold CompetitorData
  infer_instance

variable {σ : Type*} [Primcodable σ]

private theorem imp_primrec {p q : σ → Prop} (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred (fun s => p s → q s) :=
  (hp.not.or hq).of_eq fun _ => imp_iff_not_or.symm

theorem competitorData_primrec {x : σ → SearchInput} {S : σ → Data} {G : σ → List ℕ}
    (hx : Primrec x) (hS : Primrec S) (hG : Primrec G) :
    PrimrecPred (fun s => CompetitorData (x s) (S s) (G s)) := by
  have hP := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hx))
  have hPplus := Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hx))
  have hQ := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hx)))
  have hQplus := Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hx)))
  have hH := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hx))
  have hm := Primrec.snd.comp (Primrec.fst.comp hx)
  exact (imp_primrec (Primrec.eq.comp (Primrec.fst.comp hS) (Primrec.fst.comp hQplus))
    (imp_primrec (liftingData_primrec hP hPplus hQ hS hH hG)
      (coversIntoData_primrec hQplus hS (Primrec.list_range.comp hm)))).of_eq
        fun _ => Iff.rfl

/-- Invalid competitor encodings are skipped. External input validation is
performed by `decodeInput` and uses the opposite default. -/
def checkCompetitor (x : SearchInput) (s g : ℕ) : Bool :=
  ((decodeData x.1.2 s).bind fun S =>
    (decodeMap x.1.1 x.1.2 g).map fun G => decide (CompetitorData x S G)).getD true

theorem checkCompetitor_primrec {x : σ → SearchInput} {s g : σ → ℕ}
    (hx : Primrec x) (hs : Primrec s) (hg : Primrec g) :
    Primrec (fun a => checkCompetitor (x a) (s a) (g a)) := by
  have hn := Primrec.fst.comp (Primrec.fst.comp hx)
  have hm := Primrec.snd.comp (Primrec.fst.comp hx)
  unfold checkCompetitor
  refine Primrec.option_getD.comp ?_ (Primrec.const true)
  refine Primrec.option_bind (decodeData_primrec.comp hm hs) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (decodeMap_primrec (hn.comp Primrec.fst) (hm.comp Primrec.fst) (hg.comp Primrec.fst)) ?_
  exact (competitorData_primrec (hx.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp Primrec.fst) Primrec.snd).decide.to₂

/-- Exhaustive comparison over the original encoded finite competitors. -/
def MinimalData (x : SearchInput) : Prop :=
  ∀ s ∈ patternCodes x.1.2 x.2.2.1.2.1,
    ∀ g ∈ mapCodes x.1.1 x.1.2, checkCompetitor x s g = true

instance (x : SearchInput) : Decidable (MinimalData x) := by
  unfold MinimalData
  infer_instance

/-- The two unbounded-looking finite-type quantifiers have explicit uniform
primitive-recursive list enumerations. -/
theorem minimalData_primrec : PrimrecPred MinimalData := by
  have htest : PrimrecRel (fun (g : ℕ) (p : ℕ × SearchInput) =>
      checkCompetitor p.2 p.1 g = true) :=
    Primrec.eq.comp
      (checkCompetitor_primrec (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd) Primrec.fst) (Primrec.const true)
  have hinner : PrimrecRel (fun (s : ℕ) (x : SearchInput) =>
      ∀ g ∈ mapCodes x.1.1 x.1.2, checkCompetitor x s g = true) :=
    htest.forall_mem_list.comp
      (mapCodes_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) Primrec.id
  have hm : Primrec (fun x : SearchInput => x.1.2) := Primrec.snd.comp Primrec.fst
  have hU : Primrec (fun x : SearchInput => x.2.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  exact (hinner.forall_mem_list.comp (patternCodes_primrec.comp hm hU) Primrec.id).of_eq
    fun _ => Iff.rfl

theorem mapView_id (n : ℕ) : mapView (id : Fin n → Fin n) = List.range n := by
  apply List.ext_getElem
  · simp [mapView]
  · intro i hi hj
    simp [mapView]

/-- The compared carrier, lifting antecedent and identity covering are
exactly the original finite criterion. -/
theorem competitorData_dataView_iff {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus S : PatternCode m) (h g : Fin n → Fin m) :
    CompetitorData ((n, m), (dataView P, dataView Pplus),
      (dataView Q, dataView Qplus), mapView h) (dataView S) (mapView g) ↔
      (S.U = Qplus.U →
        PatternLifting P.toStr Pplus.toStr Q.toStr S.toStr h g →
          Str.CoversInto Qplus.toStr S.toStr id) := by
  simp only [CompetitorData, ← mapView_id m, liftingData_dataView_iff,
    coversIntoData_dataView_iff]
  change (carrierView S.U = carrierView Qplus.U → _) ↔ _
  rw [carrierView_eq_iff]

@[simp] theorem decide_competitorData {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus S : PatternCode m) (h g : Fin n → Fin m) :
    decide (CompetitorData ((n, m), (dataView P, dataView Pplus),
      (dataView Q, dataView Qplus), mapView h) (dataView S) (mapView g)) =
    decide (S.U = Qplus.U →
      PatternLifting P.toStr Pplus.toStr Q.toStr S.toStr h g →
        Str.CoversInto Qplus.toStr S.toStr id) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  exact competitorData_dataView_iff P Pplus Q Qplus S h g

theorem checkCompetitor_eq {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h : Fin n → Fin m) (s g : ℕ) :
    checkCompetitor ((n, m), (dataView P, dataView Pplus),
      (dataView Q, dataView Qplus), mapView h) s g =
    match decode (α := PatternCode m) s, decode (α := Fin n → Fin m) g with
    | some S, some G => decide (S.U = Qplus.U →
        PatternLifting P.toStr Pplus.toStr Q.toStr S.toStr h G →
          Str.CoversInto Qplus.toStr S.toStr id)
    | _, _ => true := by
  cases hS : decode (α := PatternCode m) s <;>
    cases hG : decode (α := Fin n → Fin m) g <;>
    simp [checkCompetitor, decodeData_eq, decodeMap_eq, hS, hG]

/-- Every original competitor occurs in the search. Conversely, successful
decoding makes every tested entry an original competitor. -/
theorem minimalData_dataView_iff {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    MinimalData ((n, m), (dataView P, dataView Pplus),
      (dataView Q, dataView Qplus), mapView h) ↔
      PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr Qplus.toStr h := by
  unfold MinimalData
  constructor
  · intro hmin
    apply (PatternCode.minimalCriterion_iff P Pplus Q Qplus h).mp
    intro S g hU hL
    have hs : encode S ∈ patternCodes m (dataView Qplus).1 := by
      simpa only [dataView, hU] using encode_mem_patternCodes S
    have hc := hmin (encode S) hs (encode g) (encode_mem_mapCodes g)
    rw [checkCompetitor_eq, Encodable.encodek, Encodable.encodek] at hc
    exact (of_decide_eq_true hc) hU hL
  · intro hmin s _ g _
    rw [checkCompetitor_eq]
    cases hS : decode (α := PatternCode m) s with
    | none => rfl
    | some S =>
      cases hG : decode (α := Fin n → Fin m) g with
      | none => rfl
      | some G =>
        apply decide_eq_true
        intro hU hL
        exact hmin S.toStr G hU hL

@[simp] theorem decide_minimalData {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    decide (MinimalData ((n, m), (dataView P, dataView Pplus),
      (dataView Q, dataView Qplus), mapView h)) = P.checkMinimal Pplus Q Qplus h := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkMinimal_eq_true]
  exact minimalData_dataView_iff P Pplus Q Qplus h

/-- Preserve all four original pattern decodes and the entire base-map decode. -/
def decodeInput (n m p pplus q qplus h : ℕ) : Option SearchInput :=
  pairDecoded (some (n, m))
    (pairDecoded (pairDecoded (decodeData n p) (decodeData n pplus))
      (pairDecoded (pairDecoded (decodeData m q) (decodeData m qplus)) (decodeMap n m h)))

theorem decodeInput_primrec {n m p pplus q qplus h : σ → ℕ}
    (hn : Primrec n) (hm : Primrec m) (hp : Primrec p) (hpplus : Primrec pplus)
    (hq : Primrec q) (hqplus : Primrec qplus) (hh : Primrec h) :
    Primrec (fun s => decodeInput (n s) (m s) (p s) (pplus s) (q s) (qplus s) (h s)) :=
  pairDecoded_primrec (Primrec.option_some.comp (hn.pair hm))
    (pairDecoded_primrec
      (pairDecoded_primrec (decodeData_primrec.comp hn hp) (decodeData_primrec.comp hn hpplus))
      (pairDecoded_primrec
        (pairDecoded_primrec (decodeData_primrec.comp hm hq) (decodeData_primrec.comp hm hqplus))
        (decodeMap_primrec hn hm hh)))

/-- Total raw-code minimality checking, including malformed external inputs. -/
def checkMinimal (n m p pplus q qplus h : ℕ) : Bool :=
  ((decodeInput n m p pplus q qplus h).map fun x => decide (MinimalData x)).getD false

theorem checkMinimal_primrec {n m p pplus q qplus h : σ → ℕ}
    (hn : Primrec n) (hm : Primrec m) (hp : Primrec p) (hpplus : Primrec pplus)
    (hq : Primrec q) (hqplus : Primrec qplus) (hh : Primrec h) :
    Primrec (fun s => checkMinimal (n s) (m s) (p s) (pplus s) (q s) (qplus s) (h s)) :=
  (Primrec.option_getD.comp
    ((Primrec.option_map₁ minimalData_primrec.decide).comp
      (decodeInput_primrec hn hm hp hpplus hq hqplus hh)) (Primrec.const false)).of_eq
        fun _ => rfl

/-- The exhaustive algorithm returns exactly the original Boolean checker
on every successful decode and rejects every failed external decode. -/
theorem checkMinimal_eq (n m p pplus q qplus h : ℕ) :
    checkMinimal n m p pplus q qplus h =
    match decode (α := PatternCode n) p, decode (α := PatternCode n) pplus,
      decode (α := PatternCode m) q, decode (α := PatternCode m) qplus,
      decode (α := Fin n → Fin m) h with
    | some P, some Pplus, some Q, some Qplus, some H => P.checkMinimal Pplus Q Qplus H
    | _, _, _, _, _ => false := by
  cases hP : decode (α := PatternCode n) p <;>
    cases hPplus : decode (α := PatternCode n) pplus <;>
    cases hQ : decode (α := PatternCode m) q <;>
    cases hQplus : decode (α := PatternCode m) qplus <;>
    cases hH : decode (α := Fin n → Fin m) h <;>
    simp [checkMinimal, decodeInput, pairDecoded, decodeData_eq, decodeMap_eq,
      hP, hPplus, hQ, hQplus, hH]

@[simp] theorem checkMinimal_encode {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h : Fin n → Fin m) :
    checkMinimal n m (encode P) (encode Pplus) (encode Q) (encode Qplus) (encode h) =
      P.checkMinimal Pplus Q Qplus h := by
  rw [checkMinimal_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek]

theorem checkMinimal_eq_true (n m p pplus q qplus h : ℕ) :
    checkMinimal n m p pplus q qplus h = true ↔
    ∃ (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (H : Fin n → Fin m),
      decode p = some P ∧ decode pplus = some Pplus ∧
      decode q = some Q ∧ decode qplus = some Qplus ∧ decode h = some H ∧
      PatternLifting.IsMinimal P.toStr Pplus.toStr Q.toStr Qplus.toStr H := by
  rw [checkMinimal_eq]
  cases hP : decode (α := PatternCode n) p <;>
    cases hPplus : decode (α := PatternCode n) pplus <;>
    cases hQ : decode (α := PatternCode m) q <;>
    cases hQplus : decode (α := PatternCode m) qplus <;>
    cases hH : decode (α := Fin n → Fin m) h <;>
    simp [PatternCode.checkMinimal_eq_true]

abbrev RawInput := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × ℕ

/-- One total machine checks exhaustive minimality with both dimensions
and every original external code supplied as natural inputs. -/
theorem checkMinimal_program : ∃ machine : Nat.Partrec.Code, ∀ n m p pplus q qplus h : ℕ,
    machine.eval (Nat.pair (Nat.pair n m)
      (Nat.pair (Nat.pair p pplus) (Nat.pair (Nat.pair q qplus) h))) =
      Part.some (encode (checkMinimal n m p pplus q qplus h)) := by
  have ht : Primrec (fun s : RawInput =>
      checkMinimal s.1.1 s.1.2 s.2.1.1 s.2.1.2 s.2.2.1.1 s.2.2.1.2 s.2.2.2) :=
    checkMinimal_primrec (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program ht
  exact ⟨machine, fun n m p pplus q qplus h => hm ((n, m), (p, pplus), (q, qplus), h)⟩

end Alexander313.Carlson.PrimitiveMinimalityChecks
