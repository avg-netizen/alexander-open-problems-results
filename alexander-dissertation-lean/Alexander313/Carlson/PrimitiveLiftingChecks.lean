import Alexander313.Carlson.PrimitivePatternChecks
import Alexander313.Carlson.PrimitiveContinuityChecks
import Alexander313.Carlson.PrimitiveEmbeddingChecks
import Alexander313.Carlson.FiniteLifting

/-!
# Uniform primitive-recursive finite lifting checks

The ten arithmetic lifting conditions and all six pattern lifting fields
have finite checks on the original lossless data views. The placement clause
only needs old-source anchors and extended-source points: membership of the
anchor is already required by `JustBelow`. No ambient point is omitted from
an active instance of that clause.

The raw checker decodes four complete pattern records and both total finite
maps using the unchanged codecs. Both dimensions are machine inputs. All
failed decodes reject, including map values outside the target bound at
off-carrier source labels. Exhaustive minimality is a separate check.
-/

namespace Alexander313.Carlson.PrimitiveLiftingChecks

open Encodable Finite PrimitivePatternCode PrimitiveFiniteChecks
open PrimitivePatternChecks PrimitiveContinuityChecks PrimitiveEmbeddingChecks
open PrimitiveEndpointIso (mem_carrierView_iff)

/-- Strict order preservation on the supplied carrier. -/
def IncreasingData (A : Finset ℕ) (F : List ℕ) : Prop :=
  ∀ ij ∈ A ×ˢ A, ij.1 < ij.2 → mapAt F ij.1 < mapAt F ij.2

/-- Every carrier image belongs to the supplied target carrier. -/
def LandsData (A B : Finset ℕ) (F : List ℕ) : Prop :=
  A.image (mapAt F) ⊆ B

/-- The extended map agrees with the base map on the old source. -/
def AgreesData (A : Finset ℕ) (H F : List ℕ) : Prop :=
  ∀ i ∈ A, mapAt F i = mapAt H i

/-- Every active old-source anchor and extended-source point is checked. -/
def PlacementData (A Aplus B : Finset ℕ) (H F : List ℕ) : Prop :=
  ∀ ax ∈ A ×ˢ Aplus, JustBelowData A ax.1 ax.2 →
    JustBelowData B (mapAt H ax.1) (mapAt F ax.2)

instance (A : Finset ℕ) (F : List ℕ) : Decidable (IncreasingData A F) := by
  unfold IncreasingData
  infer_instance

instance (A B : Finset ℕ) (F : List ℕ) : Decidable (LandsData A B F) := by
  unfold LandsData
  infer_instance

instance (A : Finset ℕ) (H F : List ℕ) : Decidable (AgreesData A H F) := by
  unfold AgreesData
  infer_instance

instance (A Aplus B : Finset ℕ) (H F : List ℕ) :
    Decidable (PlacementData A Aplus B H F) := by
  unfold PlacementData
  infer_instance

/-- All ten original arithmetic lifting fields in their original order. -/
def ArithmeticData (P Pplus Q Qplus : Data) (H F : List ℕ) : Prop :=
  P.1 ⊆ Pplus.1 ∧ BoundedData P Pplus ∧
    IncreasingData P.1 H ∧ LandsData P.1 Q.1 H ∧ Q.1 ⊆ Qplus.1 ∧
    IncreasingData Pplus.1 F ∧ LandsData Pplus.1 Qplus.1 F ∧
    AgreesData P.1 H F ∧ Qplus.1 = Q.1 ∪ Pplus.1.image (mapAt F) ∧
    PlacementData P.1 Pplus.1 Q.1 H F

instance (P Pplus Q Qplus : Data) (H F : List ℕ) :
    Decidable (ArithmeticData P Pplus Q Qplus H F) := by
  unfold ArithmeticData
  infer_instance

/-- Exact relation agreement on the extended source. `IsoPair` also checks
the strict-order condition already required by arithmetic lifting. -/
def ExactPairsData (P Q : Data) (F : List ℕ) : Prop :=
  ∀ ij ∈ P.1 ×ˢ P.1, IsoPair P Q F ij

instance (P Q : Data) (F : List ℕ) : Decidable (ExactPairsData P Q F) := by
  unfold ExactPairsData
  infer_instance

/-- The full lifting test, including both patternhood and substructure tests. -/
def LiftingData (P Pplus Q Qplus : Data) (H F : List ℕ) : Prop :=
  PatternData Pplus ∧ PatternData Qplus ∧ SubData P Pplus ∧ SubData Q Qplus ∧
    ArithmeticData P Pplus Q Qplus H F ∧ ExactPairsData Pplus Qplus F

instance (P Pplus Q Qplus : Data) (H F : List ℕ) :
    Decidable (LiftingData P Pplus Q Qplus H F) := by
  unfold LiftingData
  infer_instance

variable {σ : Type*} [Primcodable σ]

theorem increasingData_primrec {A : σ → Finset ℕ} {F : σ → List ℕ}
    (hA : Primrec A) (hF : Primrec F) :
    PrimrecPred (fun s => IncreasingData (A s) (F s)) := by
  have hi : Primrec (fun p : (ℕ × ℕ) × σ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ) × σ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hF' : Primrec (fun p : (ℕ × ℕ) × σ => F p.2) := hF.comp Primrec.snd
  have hp : PrimrecRel (fun (ij : ℕ × ℕ) s =>
      ij.1 < ij.2 → mapAt (F s) ij.1 < mapAt (F s) ij.2) :=
    ((Primrec.nat_lt.comp hi hj).not.or
      (Primrec.nat_lt.comp (mapAt_primrec.comp hF' hi)
        (mapAt_primrec.comp hF' hj))).of_eq fun _ => imp_iff_not_or.symm
  exact ((PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hA hA) Primrec.id).of_eq
      fun _ => Iff.rfl

theorem landsData_primrec {A B : σ → Finset ℕ} {F : σ → List ℕ}
    (hA : Primrec A) (hB : Primrec B) (hF : Primrec F) :
    PrimrecPred (fun s => LandsData (A s) (B s) (F s)) :=
  (PrimitiveFiniteOperations.finset_subset.comp
    ((PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF hA) hB).of_eq
      fun _ => Iff.rfl

theorem agreesData_primrec {A : σ → Finset ℕ} {H F : σ → List ℕ}
    (hA : Primrec A) (hH : Primrec H) (hF : Primrec F) :
    PrimrecPred (fun s => AgreesData (A s) (H s) (F s)) := by
  have hp : PrimrecRel (fun (i : ℕ) s => mapAt (F s) i = mapAt (H s) i) :=
    Primrec.eq.comp (mapAt_primrec.comp (hF.comp Primrec.snd) Primrec.fst)
      (mapAt_primrec.comp (hH.comp Primrec.snd) Primrec.fst)
  exact ((PrimitiveFiniteOperations.forall_mem hp).comp hA Primrec.id).of_eq
    fun _ => Iff.rfl

theorem placementData_primrec {A Aplus B : σ → Finset ℕ} {H F : σ → List ℕ}
    (hA : Primrec A) (hAplus : Primrec Aplus) (hB : Primrec B)
    (hH : Primrec H) (hF : Primrec F) :
    PrimrecPred (fun s => PlacementData (A s) (Aplus s) (B s) (H s) (F s)) := by
  have ha : Primrec (fun p : (ℕ × ℕ) × σ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun p : (ℕ × ℕ) × σ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hp : PrimrecRel (fun (ax : ℕ × ℕ) s =>
      JustBelowData (A s) ax.1 ax.2 →
        JustBelowData (B s) (mapAt (H s) ax.1) (mapAt (F s) ax.2)) :=
    ((justBelowData_primrec (hA.comp Primrec.snd) ha hx).not.or
      (justBelowData_primrec (hB.comp Primrec.snd)
        (mapAt_primrec.comp (hH.comp Primrec.snd) ha)
        (mapAt_primrec.comp (hF.comp Primrec.snd) hx))).of_eq
          fun _ => imp_iff_not_or.symm
  exact ((PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hA hAplus) Primrec.id).of_eq
      fun _ => Iff.rfl

theorem arithmeticData_primrec {P Pplus Q Qplus : σ → Data} {H F : σ → List ℕ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hQplus : Primrec Qplus)
    (hH : Primrec H) (hF : Primrec F) :
    PrimrecPred (fun s => ArithmeticData (P s) (Pplus s) (Q s) (Qplus s) (H s) (F s)) := by
  have hA := Primrec.fst.comp hP
  have hAplus := Primrec.fst.comp hPplus
  have hB := Primrec.fst.comp hQ
  have hBplus := Primrec.fst.comp hQplus
  have hcarrier : PrimrecPred (fun s => (Qplus s).1 =
      (Q s).1 ∪ (Pplus s).1.image (mapAt (F s))) :=
    Primrec.eq.comp hBplus (PrimitiveFiniteOperations.finset_union.comp hB
      ((PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF hAplus))
  exact ((PrimitiveFiniteOperations.finset_subset.comp hA hAplus).and
    ((boundedData_primrec hP hPplus).and
    ((increasingData_primrec hA hH).and
    ((landsData_primrec hA hB hH).and
    ((PrimitiveFiniteOperations.finset_subset.comp hB hBplus).and
    ((increasingData_primrec hAplus hF).and
    ((landsData_primrec hAplus hBplus hF).and
    ((agreesData_primrec hA hH hF).and
    (hcarrier.and (placementData_primrec hA hAplus hB hH hF)))))))))).of_eq
      fun _ => Iff.rfl

theorem exactPairsData_primrec {P Q : σ → Data} {F : σ → List ℕ}
    (hP : Primrec P) (hQ : Primrec Q) (hF : Primrec F) :
    PrimrecPred (fun s => ExactPairsData (P s) (Q s) (F s)) := by
  have hU := Primrec.fst.comp hP
  exact ((PrimitiveFiniteOperations.forall_mem (isoPair_primrec hP hQ hF)).comp
    (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id).of_eq
      fun _ => Iff.rfl

/-- No primitive-recursive hypothesis remains on any arithmetic or relation field. -/
theorem liftingData_primrec {P Pplus Q Qplus : σ → Data} {H F : σ → List ℕ}
    (hP : Primrec P) (hPplus : Primrec Pplus) (hQ : Primrec Q) (hQplus : Primrec Qplus)
    (hH : Primrec H) (hF : Primrec F) :
    PrimrecPred (fun s => LiftingData (P s) (Pplus s) (Q s) (Qplus s) (H s) (F s)) :=
  ((patternData_primrec.comp hPplus).and ((patternData_primrec.comp hQplus).and
    ((subData_primrec.comp hP hPplus).and ((subData_primrec.comp hQ hQplus).and
      ((arithmeticData_primrec hP hPplus hQ hQplus hH hF).and
        (exactPairsData_primrec hPplus hQplus hF)))))).of_eq fun _ => Iff.rfl

private theorem forall_carrierView_iff {n : ℕ} (A : Finset (Fin n)) (p : ℕ → Prop) :
    (∀ i ∈ carrierView A, p i) ↔ ∀ x ∈ A, p x.val := by
  constructor
  · intro h x hx
    exact h x.val ((mem_carrierView A x).mpr hx)
  · intro h i hi
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff A i).mp hi
    exact h x hx

theorem increasingData_carrierView_iff {n m : ℕ} (A : Finset (Fin n))
    (f : Fin n → Fin m) : IncreasingData (carrierView A) (mapView f) ↔
      ∀ x ∈ A, ∀ y ∈ A, x < y → f x < f y := by
  unfold IncreasingData
  rw [forall_carrierPairs_iff]
  simp only [mapAt_mapView, Fin.lt_def]

theorem landsData_carrierView_iff {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m))
    (f : Fin n → Fin m) : LandsData (carrierView A) (carrierView B) (mapView f) ↔
      ∀ x ∈ A, f x ∈ B := by
  rw [LandsData, image_mapView, carrierView_subset_iff, Finset.image_subset_iff]

theorem agreesData_carrierView_iff {n m : ℕ} (A : Finset (Fin n))
    (h f : Fin n → Fin m) : AgreesData (carrierView A) (mapView h) (mapView f) ↔
      ∀ x ∈ A, f x = h x := by
  unfold AgreesData
  rw [forall_carrierView_iff]
  simp only [mapAt_mapView, Fin.val_inj]

theorem placementData_carrierView_iff {n m : ℕ} (A Aplus : Finset (Fin n))
    (B : Finset (Fin m)) (h f : Fin n → Fin m) :
    PlacementData (carrierView A) (carrierView Aplus) (carrierView B) (mapView h) (mapView f) ↔
      ∀ a x, x ∈ Aplus → Str.JustBelow A a x → Str.JustBelow B (h a) (f x) := by
  constructor
  · intro hp a x hx hax
    apply (justBelowData_carrierView_iff B (h a) (f x)).mp
    have ht := hp (a.val, x.val) (Finset.mem_product.mpr
      ⟨(mem_carrierView A a).mpr hax.1, (mem_carrierView Aplus x).mpr hx⟩)
      ((justBelowData_carrierView_iff A a x).mpr hax)
    simpa only [mapAt_mapView] using ht
  · intro hp
    rintro ⟨a, x⟩ hax hjb
    obtain ⟨ha, hx⟩ := Finset.mem_product.mp hax
    obtain ⟨a₀, ha₀, rfl⟩ := (mem_carrierView_iff A a).mp ha
    obtain ⟨x₀, hx₀, rfl⟩ := (mem_carrierView_iff Aplus x).mp hx
    have ht := (justBelowData_carrierView_iff B (h a₀) (f x₀)).mpr
      (hp a₀ x₀ hx₀ ((justBelowData_carrierView_iff A a₀ x₀).mp hjb))
    simpa only [mapAt_mapView] using ht

theorem carrierView_union {n : ℕ} (A B : Finset (Fin n)) :
    carrierView (A ∪ B) = carrierView A ∪ carrierView B := by
  exact Finset.map_union A B

/-- Each of the ten arithmetic fields agrees with its original finite predicate. -/
theorem arithmeticData_dataView_iff {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h f : Fin n → Fin m) :
    ArithmeticData (dataView P) (dataView Pplus) (dataView Q) (dataView Qplus)
        (mapView h) (mapView f) ↔
      ArithmeticLifting P.U Pplus.U Q.U Qplus.U h f := by
  have hcarrier : carrierView Qplus.U =
      carrierView Q.U ∪ (carrierView Pplus.U).image (mapAt (mapView f)) ↔
      Qplus.U = Q.U ∪ Pplus.U.image f := by
    rw [image_mapView, ← carrierView_union, carrierView_eq_iff]
  rw [ArithmeticLifting.iff_conditions]
  simp only [ArithmeticData,
    show (dataView P).1 = carrierView P.U from rfl,
    show (dataView Pplus).1 = carrierView Pplus.U from rfl,
    show (dataView Q).1 = carrierView Q.U from rfl,
    show (dataView Qplus).1 = carrierView Qplus.U from rfl,
    carrierView_subset_iff, boundedData_dataView_iff, PatternCode.toStr_U,
    increasingData_carrierView_iff, landsData_carrierView_iff,
    agreesData_carrierView_iff, placementData_carrierView_iff, hcarrier]

theorem exactPairsData_dataView_iff {n m : ℕ} (P : PatternCode n) (Q : PatternCode m)
    (f : Fin n → Fin m) : ExactPairsData (dataView P) (dataView Q) (mapView f) ↔
      (∀ x ∈ P.U, ∀ y ∈ P.U, x < y → f x < f y) ∧
      (∀ x ∈ P.U, ∀ y ∈ P.U,
        (P.toStr.r₁ x y ↔ Q.toStr.r₁ (f x) (f y)) ∧
        (P.toStr.r₂ x y ↔ Q.toStr.r₂ (f x) (f y))) := by
  change (∀ ij ∈ carrierView P.U ×ˢ carrierView P.U,
    IsoPair (dataView P) (dataView Q) (mapView f) ij) ↔ _
  rw [forall_carrierPairs_iff]
  simp only [isoPair_dataView_iff]
  constructor
  · intro hp
    exact ⟨fun x hx y hy => (hp x hx y hy).1,
      fun x hx y hy => ⟨Bool.eq_iff_iff.mp (hp x hx y hy).2.1,
        Bool.eq_iff_iff.mp (hp x hx y hy).2.2⟩⟩
  · rintro ⟨horder, hrels⟩
    exact fun x hx y hy => ⟨horder x hx y hy,
      Bool.eq_iff_iff.mpr (hrels x hx y hy).1,
      Bool.eq_iff_iff.mpr (hrels x hx y hy).2⟩

/-- Full semantic equivalence, without patternhood or canonical-code assumptions. -/
theorem liftingData_dataView_iff {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h f : Fin n → Fin m) :
    LiftingData (dataView P) (dataView Pplus) (dataView Q) (dataView Qplus)
        (mapView h) (mapView f) ↔
      PatternLifting P.toStr Pplus.toStr Q.toStr Qplus.toStr h f := by
  rw [PatternLifting.iff_conditions]
  simp only [LiftingData, patternData_dataView_iff, subData_dataView_iff,
    arithmeticData_dataView_iff, exactPairsData_dataView_iff, PatternCode.toStr_U]
  constructor
  · rintro ⟨hP, hQ, hsubP, hsubQ, harith, _, hrels⟩
    exact ⟨hP, hQ, hsubP, hsubQ, harith, hrels⟩
  · rintro ⟨hP, hQ, hsubP, hsubQ, harith, hrels⟩
    exact ⟨hP, hQ, hsubP, hsubQ, harith, harith.mono, hrels⟩

@[simp] theorem decide_liftingData {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h f : Fin n → Fin m) :
    decide (LiftingData (dataView P) (dataView Pplus) (dataView Q) (dataView Qplus)
      (mapView h) (mapView f)) = P.checkLifting Pplus Q Qplus h f := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkLifting_eq_true]
  exact liftingData_dataView_iff P Pplus Q Qplus h f

/-- Pair independent successful decodes; a failure of either input rejects. -/
def pairDecoded {α β : Type*} (a : Option α) (b : Option β) : Option (α × β) :=
  a.bind fun x => b.map fun y => (x, y)

theorem pairDecoded_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {a : σ → Option α} {b : σ → Option β} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun s => pairDecoded (a s) (b s)) := by
  unfold pairDecoded
  refine Primrec.option_bind ha ?_
  apply Primrec₂.mk
  exact Primrec.option_map (hb.comp Primrec.fst)
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

/-- Group the old/extended source, old/extended target, and base/extended maps. -/
abbrev Input := (Data × Data) × (Data × Data) × (List ℕ × List ℕ)

def decodeInput (n m p pplus q qplus h f : ℕ) : Option Input :=
  pairDecoded (pairDecoded (decodeData n p) (decodeData n pplus))
    (pairDecoded (pairDecoded (decodeData m q) (decodeData m qplus))
      (pairDecoded (decodeMap n m h) (decodeMap n m f)))

theorem decodeInput_primrec {n m p pplus q qplus h f : σ → ℕ}
    (hn : Primrec n) (hm : Primrec m) (hp : Primrec p) (hpplus : Primrec pplus)
    (hq : Primrec q) (hqplus : Primrec qplus) (hh : Primrec h) (hf : Primrec f) :
    Primrec (fun s => decodeInput (n s) (m s) (p s) (pplus s) (q s) (qplus s) (h s) (f s)) :=
  pairDecoded_primrec
    (pairDecoded_primrec (decodeData_primrec.comp hn hp) (decodeData_primrec.comp hn hpplus))
    (pairDecoded_primrec
      (pairDecoded_primrec (decodeData_primrec.comp hm hq) (decodeData_primrec.comp hm hqplus))
      (pairDecoded_primrec (decodeMap_primrec hn hm hh) (decodeMap_primrec hn hm hf)))

/-- Total raw checking of the unchanged pattern lifting predicate. -/
def checkLifting (n m p pplus q qplus h f : ℕ) : Bool :=
  ((decodeInput n m p pplus q qplus h f).map fun s =>
    decide (LiftingData s.1.1 s.1.2 s.2.1.1 s.2.1.2 s.2.2.1 s.2.2.2)).getD false

/-- All dimensions and all six original encoded objects are varying inputs. -/
theorem checkLifting_primrec {n m p pplus q qplus h f : σ → ℕ}
    (hn : Primrec n) (hm : Primrec m) (hp : Primrec p) (hpplus : Primrec pplus)
    (hq : Primrec q) (hqplus : Primrec qplus) (hh : Primrec h) (hf : Primrec f) :
    Primrec (fun s => checkLifting (n s) (m s) (p s) (pplus s) (q s) (qplus s) (h s) (f s)) := by
  have ht : Primrec (fun s : Input =>
      decide (LiftingData s.1.1 s.1.2 s.2.1.1 s.2.1.2 s.2.2.1 s.2.2.2)) :=
    (liftingData_primrec (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).decide
  exact (Primrec.option_getD.comp
    ((Primrec.option_map₁ ht).comp (decodeInput_primrec hn hm hp hpplus hq hqplus hh hf))
    (Primrec.const false)).of_eq fun _ => rfl

/-- Every raw input has exactly the original decoder and checker behavior. -/
theorem checkLifting_eq (n m p pplus q qplus h f : ℕ) :
    checkLifting n m p pplus q qplus h f =
    match decode (α := PatternCode n) p, decode (α := PatternCode n) pplus,
      decode (α := PatternCode m) q, decode (α := PatternCode m) qplus,
      decode (α := Fin n → Fin m) h, decode (α := Fin n → Fin m) f with
    | some P, some Pplus, some Q, some Qplus, some H, some F =>
        P.checkLifting Pplus Q Qplus H F
    | _, _, _, _, _, _ => false := by
  cases hP : decode (α := PatternCode n) p <;>
    cases hPplus : decode (α := PatternCode n) pplus <;>
    cases hQ : decode (α := PatternCode m) q <;>
    cases hQplus : decode (α := PatternCode m) qplus <;>
    cases hH : decode (α := Fin n → Fin m) h <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [checkLifting, decodeInput, pairDecoded, decodeData_eq, decodeMap_eq,
      hP, hPplus, hQ, hQplus, hH, hF]

@[simp] theorem checkLifting_encode {n m : ℕ} (P Pplus : PatternCode n)
    (Q Qplus : PatternCode m) (h f : Fin n → Fin m) :
    checkLifting n m (encode P) (encode Pplus) (encode Q) (encode Qplus) (encode h) (encode f) =
      P.checkLifting Pplus Q Qplus h f := by
  rw [checkLifting_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek, Encodable.encodek]

theorem checkLifting_eq_true (n m p pplus q qplus h f : ℕ) :
    checkLifting n m p pplus q qplus h f = true ↔
    ∃ (P Pplus : PatternCode n) (Q Qplus : PatternCode m) (H F : Fin n → Fin m),
      decode p = some P ∧ decode pplus = some Pplus ∧
      decode q = some Q ∧ decode qplus = some Qplus ∧
      decode h = some H ∧ decode f = some F ∧
      PatternLifting P.toStr Pplus.toStr Q.toStr Qplus.toStr H F := by
  rw [checkLifting_eq]
  cases hP : decode (α := PatternCode n) p <;>
    cases hPplus : decode (α := PatternCode n) pplus <;>
    cases hQ : decode (α := PatternCode m) q <;>
    cases hQplus : decode (α := PatternCode m) qplus <;>
    cases hH : decode (α := Fin n → Fin m) h <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [PatternCode.checkLifting_eq_true]

/-- Grouped natural input: dimensions, source codes, target codes, and map codes. -/
abbrev RawInput := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- One total machine checks all finite lifting instances and malformed raw inputs. -/
theorem checkLifting_program : ∃ machine : Nat.Partrec.Code, ∀ n m p pplus q qplus h f : ℕ,
    machine.eval (Nat.pair (Nat.pair n m)
      (Nat.pair (Nat.pair p pplus) (Nat.pair (Nat.pair q qplus) (Nat.pair h f)))) =
      Part.some (encode (checkLifting n m p pplus q qplus h f)) := by
  have ht : Primrec (fun s : RawInput =>
      checkLifting s.1.1 s.1.2 s.2.1.1 s.2.1.2 s.2.2.1.1 s.2.2.1.2 s.2.2.2.1 s.2.2.2.2) :=
    checkLifting_primrec (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program ht
  exact ⟨machine, fun n m p pplus q qplus h f => hm ((n, m), (p, pplus), (q, qplus), (h, f))⟩

end Alexander313.Carlson.PrimitiveLiftingChecks
