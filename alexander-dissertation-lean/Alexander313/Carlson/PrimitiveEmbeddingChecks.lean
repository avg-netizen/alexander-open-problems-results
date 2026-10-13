import Alexander313.Carlson.PrimitiveFiniteChecks

/-!
# Primitive-recursive covering and isomorphism checks

The source dimension, target dimension, both pattern codes and a total map
code are all natural-number inputs. The map decoder reuses the original
index-tagged finite-function format and checks every output bound, including
values at labels outside the source carrier. The structural checks themselves
inspect only carrier points and pairs, exactly as the original predicates do.

Coverings preserve both relations forward and need not cover the target
carrier. Isomorphisms require the exact image carrier and reflect both
relations as well. No patternhood hypothesis is imposed by either checker.
This module does not certify continuous embeddings or lifting minimality.
-/

namespace Alexander313.Carlson.PrimitiveEmbeddingChecks

open Encodable Finite PrimitivePatternCode PrimitiveFiniteFunctions
open PrimitiveEndpointIso (entry₁ entry₂ entry₁_primrec entry₂_primrec
  entry₁_dataView entry₂_dataView mem_carrierView_iff)

/-- The values of a total finite map, with both finite bounds erased. -/
def mapView {n m : ℕ} (f : Fin n → Fin m) : List ℕ :=
  List.ofFn (fun i => (f i).val)

/-- Uniform decoding with the original inferred finite-function codec. -/
def decodeMap (n m code : ℕ) : Option (List ℕ) :=
  decodeArrowWith (decodeLabel m) n code

/-- Exact compatibility on every raw code, for independently varying bounds. -/
theorem decodeMap_eq (n m code : ℕ) :
    decodeMap n m code =
      (decode (α := Fin n → Fin m) code).map mapView := by
  unfold decodeMap
  have h : decodeLabel m = fun c => (decode (α := Fin m) c).map Fin.val := by
    funext c
    exact decodeLabel_eq m c
  rw [h]
  exact decodeArrowWith_map Fin.val n code

@[simp] theorem decodeMap_encode {n m : ℕ} (f : Fin n → Fin m) :
    decodeMap n m (encode f) = some (mapView f) := by
  rw [decodeMap_eq, Encodable.encodek]
  rfl

/-- Success certifies the full domain length and every codomain bound. -/
theorem decodeMap_bounds {n m code : ℕ} {F : List ℕ}
    (h : decodeMap n m code = some F) :
    F.length = n ∧ ∀ j ∈ F, j < m := by
  rw [decodeMap_eq] at h
  obtain ⟨f, _, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨List.length_ofFn, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
  exact (f i).isLt

variable {σ : Type*} [Primcodable σ]

theorem decodeMap_primrec {n m code : σ → ℕ}
    (hn : Primrec n) (hm : Primrec m) (hc : Primrec code) :
    Primrec (fun s => decodeMap (n s) (m s) (code s)) := by
  unfold decodeMap
  exact decodeArrowWith_primrec
    (decodeLabel_primrec.comp (hm.comp Primrec.fst) Primrec.snd).to₂ hn hc

/-- Missing entries have a total default. Successful decoding ensures
that the default is never used at a source-carrier label. -/
def mapAt (F : List ℕ) (i : ℕ) : ℕ := (F[i]?).getD 0

theorem mapAt_primrec : Primrec₂ mapAt :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const 0)).of_eq
    fun _ => rfl

@[simp] theorem mapAt_mapView {n m : ℕ} (f : Fin n → Fin m) (i : Fin n) :
    mapAt (mapView f) i.val = (f i).val := by
  simp [mapAt, mapView]

/-- Order preservation and forward preservation of both relation tables. -/
def CoversPair (C D : Data) (F : List ℕ) (ij : ℕ × ℕ) : Prop :=
  (ij.1 < ij.2 → mapAt F ij.1 < mapAt F ij.2) ∧
    (entry₁ C ij = true → entry₁ D (mapAt F ij.1, mapAt F ij.2) = true) ∧
    (entry₂ C ij = true → entry₂ D (mapAt F ij.1, mapAt F ij.2) = true)

instance (C D : Data) (F : List ℕ) (ij : ℕ × ℕ) :
    Decidable (CoversPair C D F ij) := by
  unfold CoversPair
  infer_instance

/-- Order preservation and exact agreement of both relation tables. -/
def IsoPair (C D : Data) (F : List ℕ) (ij : ℕ × ℕ) : Prop :=
  (ij.1 < ij.2 → mapAt F ij.1 < mapAt F ij.2) ∧
    entry₁ C ij = entry₁ D (mapAt F ij.1, mapAt F ij.2) ∧
    entry₂ C ij = entry₂ D (mapAt F ij.1, mapAt F ij.2)

instance (C D : Data) (F : List ℕ) (ij : ℕ × ℕ) :
    Decidable (IsoPair C D F ij) := by
  unfold IsoPair
  infer_instance

/-- Covering requires carrier inclusion, without a surjectivity condition. -/
def CoversIntoData (C D : Data) (F : List ℕ) : Prop :=
  C.1.image (mapAt F) ⊆ D.1 ∧ ∀ ij ∈ C.1 ×ˢ C.1, CoversPair C D F ij

instance (C D : Data) (F : List ℕ) : Decidable (CoversIntoData C D F) := by
  unfold CoversIntoData
  infer_instance

/-- Isomorphism requires the image carrier to equal the target carrier. -/
def IsoData (C D : Data) (F : List ℕ) : Prop :=
  C.1.image (mapAt F) = D.1 ∧ ∀ ij ∈ C.1 ×ˢ C.1, IsoPair C D F ij

instance (C D : Data) (F : List ℕ) : Decidable (IsoData C D F) := by
  unfold IsoData
  infer_instance

theorem coversPair_primrec {C D : σ → Data} {F : σ → List ℕ}
    (hC : Primrec C) (hD : Primrec D) (hF : Primrec F) :
    PrimrecRel (fun (ij : ℕ × ℕ) s => CoversPair (C s) (D s) (F s) ij) := by
  have hC' := hC.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hD' := hD.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hF' := hF.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hi : Primrec (fun p : (ℕ × ℕ) × σ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ) × σ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hx := mapAt_primrec.comp hF' hi
  have hy := mapAt_primrec.comp hF' hj
  have ho := ((Primrec.nat_lt.comp hi hj).not.or (Primrec.nat_lt.comp hx hy)).of_eq
    (fun _ => imp_iff_not_or.symm)
  have h₁ := ((Primrec.eq.comp (entry₁_primrec.comp hC' Primrec.fst)
    (Primrec.const true)).not.or
      (Primrec.eq.comp (entry₁_primrec.comp hD' (hx.pair hy)) (Primrec.const true))).of_eq
        (fun _ => imp_iff_not_or.symm)
  have h₂ := ((Primrec.eq.comp (entry₂_primrec.comp hC' Primrec.fst)
    (Primrec.const true)).not.or
      (Primrec.eq.comp (entry₂_primrec.comp hD' (hx.pair hy)) (Primrec.const true))).of_eq
        (fun _ => imp_iff_not_or.symm)
  exact (ho.and (h₁.and h₂)).of_eq fun _ => Iff.rfl

theorem isoPair_primrec {C D : σ → Data} {F : σ → List ℕ}
    (hC : Primrec C) (hD : Primrec D) (hF : Primrec F) :
    PrimrecRel (fun (ij : ℕ × ℕ) s => IsoPair (C s) (D s) (F s) ij) := by
  have hC' := hC.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hD' := hD.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hF' := hF.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hi : Primrec (fun p : (ℕ × ℕ) × σ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ) × σ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hx := mapAt_primrec.comp hF' hi
  have hy := mapAt_primrec.comp hF' hj
  have ho := ((Primrec.nat_lt.comp hi hj).not.or (Primrec.nat_lt.comp hx hy)).of_eq
    (fun _ => imp_iff_not_or.symm)
  exact (ho.and
    ((Primrec.eq.comp (entry₁_primrec.comp hC' Primrec.fst)
      (entry₁_primrec.comp hD' (hx.pair hy))).and
    (Primrec.eq.comp (entry₂_primrec.comp hC' Primrec.fst)
      (entry₂_primrec.comp hD' (hx.pair hy))))).of_eq fun _ => Iff.rfl

theorem coversIntoData_primrec {C D : σ → Data} {F : σ → List ℕ}
    (hC : Primrec C) (hD : Primrec D) (hF : Primrec F) :
    PrimrecPred (fun s => CoversIntoData (C s) (D s) (F s)) := by
  have hU := Primrec.fst.comp hC
  have himage := (PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF hU
  exact ((PrimitiveFiniteOperations.finset_subset.comp himage (Primrec.fst.comp hD)).and
    ((PrimitiveFiniteOperations.forall_mem (coversPair_primrec hC hD hF)).comp
      (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id)).of_eq
        fun _ => Iff.rfl

theorem isoData_primrec {C D : σ → Data} {F : σ → List ℕ}
    (hC : Primrec C) (hD : Primrec D) (hF : Primrec F) :
    PrimrecPred (fun s => IsoData (C s) (D s) (F s)) := by
  have hU := Primrec.fst.comp hC
  have himage := (PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF hU
  exact ((Primrec.eq.comp himage (Primrec.fst.comp hD)).and
    ((PrimitiveFiniteOperations.forall_mem (isoPair_primrec hC hD hF)).comp
      (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id)).of_eq
        fun _ => Iff.rfl

theorem image_mapView {n m : ℕ} (U : Finset (Fin n)) (f : Fin n → Fin m) :
    (carrierView U).image (mapAt (mapView f)) = carrierView (U.image f) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, h⟩ := Finset.mem_image.mp hj
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff U i).mp hi
    apply (mem_carrierView_iff (U.image f) j).mpr
    exact ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, (mapAt_mapView f x).symm.trans h⟩
  · intro hj
    obtain ⟨y, hy, rfl⟩ := (mem_carrierView_iff (U.image f) j).mp hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr
      ⟨x.val, (mem_carrierView U x).mpr hx, mapAt_mapView f x⟩

theorem carrierView_eq_iff {n : ℕ} (U V : Finset (Fin n)) :
    carrierView U = carrierView V ↔ U = V := by
  constructor
  · intro h
    ext i
    rw [← mem_carrierView U i, h, mem_carrierView V i]
  · rintro rfl
    rfl

theorem forall_carrierPairs_iff {n : ℕ} (U : Finset (Fin n)) (p : ℕ × ℕ → Prop) :
    (∀ ij ∈ carrierView U ×ˢ carrierView U, p ij) ↔
      ∀ x ∈ U, ∀ y ∈ U, p (x.val, y.val) := by
  constructor
  · intro h x hx y hy
    exact h (x.val, y.val) (Finset.mem_product.mpr
      ⟨(mem_carrierView U x).mpr hx, (mem_carrierView U y).mpr hy⟩)
  · intro h
    rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff U i).mp hi
    obtain ⟨y, hy, rfl⟩ := (mem_carrierView_iff U j).mp hj
    exact h x hx y hy

@[simp] theorem coversPair_dataView_iff {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) (i j : Fin n) :
    CoversPair (dataView C) (dataView D) (mapView f) (i.val, j.val) ↔
      (i < j → f i < f j) ∧
        (C.r₁ i j = true → D.r₁ (f i) (f j) = true) ∧
        (C.r₂ i j = true → D.r₂ (f i) (f j) = true) := by
  simp only [CoversPair, mapAt_mapView, entry₁_dataView, entry₂_dataView] <;> rfl

@[simp] theorem isoPair_dataView_iff {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) (i j : Fin n) :
    IsoPair (dataView C) (dataView D) (mapView f) (i.val, j.val) ↔
      (i < j → f i < f j) ∧
        C.r₁ i j = D.r₁ (f i) (f j) ∧ C.r₂ i j = D.r₂ (f i) (f j) := by
  simp only [IsoPair, mapAt_mapView, entry₁_dataView, entry₂_dataView] <;> rfl

/-- The data predicate is exactly the original covering predicate. -/
theorem coversIntoData_dataView_iff {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    CoversIntoData (dataView C) (dataView D) (mapView f) ↔
      Str.CoversInto C.toStr D.toStr f := by
  change ((carrierView C.U).image (mapAt (mapView f)) ⊆ carrierView D.U ∧
    ∀ ij ∈ carrierView C.U ×ˢ carrierView C.U,
      CoversPair (dataView C) (dataView D) (mapView f) ij) ↔ _
  rw [image_mapView, PrimitiveFiniteChecks.carrierView_subset_iff,
    forall_carrierPairs_iff]
  simp only [coversPair_dataView_iff]
  constructor
  · rintro ⟨hU, hpair⟩
    exact ⟨fun x hx => hU (Finset.mem_image.mpr ⟨x, hx, rfl⟩),
      fun x hx y hy => (hpair x hx y hy).1,
      fun x hx y hy => (hpair x hx y hy).2.1,
      fun x hx y hy => (hpair x hx y hy).2.2⟩
  · rintro ⟨hU, horder, h₁, h₂⟩
    refine ⟨?_, fun x hx y hy => ⟨horder x hx y hy, h₁ x hx y hy, h₂ x hx y hy⟩⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hU x hx

/-- Exact image equality and two-way relation agreement match `Str.IsIso`. -/
theorem isoData_dataView_iff {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    IsoData (dataView C) (dataView D) (mapView f) ↔
      Str.IsIso C.toStr D.toStr f := by
  change ((carrierView C.U).image (mapAt (mapView f)) = carrierView D.U ∧
    ∀ ij ∈ carrierView C.U ×ˢ carrierView C.U,
      IsoPair (dataView C) (dataView D) (mapView f) ij) ↔ _
  rw [image_mapView, carrierView_eq_iff, forall_carrierPairs_iff]
  simp only [isoPair_dataView_iff]
  constructor
  · rintro ⟨hU, hpair⟩
    exact ⟨hU, fun x hx y hy => (hpair x hx y hy).1,
      fun x hx y hy => ⟨Bool.eq_iff_iff.mp (hpair x hx y hy).2.1,
        Bool.eq_iff_iff.mp (hpair x hx y hy).2.2⟩⟩
  · rintro ⟨hU, horder, hrels⟩
    exact ⟨hU, fun x hx y hy => ⟨horder x hx y hy,
      Bool.eq_iff_iff.mpr (hrels x hx y hy).1,
      Bool.eq_iff_iff.mpr (hrels x hx y hy).2⟩⟩

@[simp] theorem decide_coversIntoData {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    decide (CoversIntoData (dataView C) (dataView D) (mapView f)) =
      C.checkCoversInto D f := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkCoversInto_eq_true]
  exact coversIntoData_dataView_iff C D f

@[simp] theorem decide_isoData {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    decide (IsoData (dataView C) (dataView D) (mapView f)) = C.checkIso D f := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkIso_eq_true]
  exact isoData_dataView_iff C D f

/-- The shared raw-code boundary rejects any of the three failed decodes. -/
def checkWith (test : Data × Data × List ℕ → Bool) (n m c d f : ℕ) : Bool :=
  ((decodeData n c).bind fun C =>
    (decodeData m d).bind fun D =>
      (decodeMap n m f).map fun F => test (C, D, F)).getD false

theorem checkWith_primrec {test : Data × Data × List ℕ → Bool} (ht : Primrec test) :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ =>
      checkWith test p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hn : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hm : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hf : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hC := decodeData_primrec.comp hn hc
  have hD := decodeData_primrec.comp hm hd
  have hF := decodeMap_primrec hn hm hf
  unfold checkWith
  refine Primrec.option_getD.comp ?_ (Primrec.const false)
  refine Primrec.option_bind hC ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (hD.comp Primrec.fst) ?_
  apply Primrec₂.mk
  exact Primrec.option_map (hF.comp (Primrec.fst.comp Primrec.fst))
    (ht.comp ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂

/-- Total covering check on the original raw codes. -/
def checkCoversInto (n m c d f : ℕ) : Bool :=
  checkWith (fun p => decide (CoversIntoData p.1 p.2.1 p.2.2)) n m c d f

/-- Total exact-isomorphism check on the original raw codes. -/
def checkIso (n m c d f : ℕ) : Bool :=
  checkWith (fun p => decide (IsoData p.1 p.2.1 p.2.2)) n m c d f

theorem checkCoversInto_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ =>
      checkCoversInto p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  checkWith_primrec (coversIntoData_primrec Primrec.fst
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide

theorem checkIso_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ =>
      checkIso p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  checkWith_primrec (isoData_primrec Primrec.fst
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide

/-- Compatibility is quantified over all raw inputs, including invalid codes. -/
theorem checkCoversInto_eq (n m c d f : ℕ) : checkCoversInto n m c d f =
    match decode (α := PatternCode n) c, decode (α := PatternCode m) d,
        decode (α := Fin n → Fin m) f with
    | some C, some D, some F => C.checkCoversInto D F
    | _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode m) d <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [checkCoversInto, checkWith, decodeData_eq, decodeMap_eq, hC, hD, hF]

theorem checkIso_eq (n m c d f : ℕ) : checkIso n m c d f =
    match decode (α := PatternCode n) c, decode (α := PatternCode m) d,
        decode (α := Fin n → Fin m) f with
    | some C, some D, some F => C.checkIso D F
    | _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode m) d <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [checkIso, checkWith, decodeData_eq, decodeMap_eq, hC, hD, hF]

@[simp] theorem checkCoversInto_encode {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    checkCoversInto n m (encode C) (encode D) (encode f) = C.checkCoversInto D f := by
  rw [checkCoversInto_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek]

@[simp] theorem checkIso_encode {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    checkIso n m (encode C) (encode D) (encode f) = C.checkIso D f := by
  rw [checkIso_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek]

theorem checkCoversInto_eq_true (n m c d f : ℕ) : checkCoversInto n m c d f = true ↔
    ∃ (C : PatternCode n) (D : PatternCode m) (F : Fin n → Fin m),
      decode c = some C ∧ decode d = some D ∧ decode f = some F ∧
        Str.CoversInto C.toStr D.toStr F := by
  rw [checkCoversInto_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode m) d <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [PatternCode.checkCoversInto_eq_true]

theorem checkIso_eq_true (n m c d f : ℕ) : checkIso n m c d f = true ↔
    ∃ (C : PatternCode n) (D : PatternCode m) (F : Fin n → Fin m),
      decode c = some C ∧ decode d = some D ∧ decode f = some F ∧
        Str.IsIso C.toStr D.toStr F := by
  rw [checkIso_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode m) d <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [PatternCode.checkIso_eq_true]

/-- One map-decoding program accepts independently varying finite bounds. -/
theorem decodeMap_program : ∃ machine : Nat.Partrec.Code, ∀ n m f : ℕ,
    machine.eval (Nat.pair n (Nat.pair m f)) = Part.some (encode (decodeMap n m f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program
    (decodeMap_primrec (Primrec.fst : Primrec (@Prod.fst ℕ (ℕ × ℕ)))
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact ⟨machine, fun n m f => hm (n, m, f)⟩

/-- One total machine decides covering for every pair of dimensions. -/
theorem checkCoversInto_program : ∃ machine : Nat.Partrec.Code, ∀ n m c d f : ℕ,
    machine.eval (Nat.pair n (Nat.pair m (Nat.pair c (Nat.pair d f)))) =
      Part.some (encode (checkCoversInto n m c d f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkCoversInto_primrec
  exact ⟨machine, fun n m c d f => hm (n, m, c, d, f)⟩

/-- One total machine decides exact isomorphism for every pair of dimensions. -/
theorem checkIso_program : ∃ machine : Nat.Partrec.Code, ∀ n m c d f : ℕ,
    machine.eval (Nat.pair n (Nat.pair m (Nat.pair c (Nat.pair d f)))) =
      Part.some (encode (checkIso n m c d f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkIso_primrec
  exact ⟨machine, fun n m c d f => hm (n, m, c, d, f)⟩

end Alexander313.Carlson.PrimitiveEmbeddingChecks
