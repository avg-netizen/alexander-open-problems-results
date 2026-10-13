import Alexander313.Carlson.PrimitivePatternChecks
import Alexander313.Carlson.PrimitiveContinuityChecks
import Alexander313.Carlson.PrimitiveEmbeddingChecks
import Alexander313.Carlson.FiniteReflection

/-!
# Uniform primitive-recursive reflection hypothesis checks

The natural-data predicates in this module check every field of the original
`Str.DownData` and `Str.UpData` records. They use the established patternhood,
continuity and extension certificates, with finite searches for the placement
and matching of the copied points. The complete finite map is decoded with
its original index tags and output bounds, although the reflection hypotheses
only inspect its values on the supplied set of new points.

The raw checks reject failed pattern, point, carrier and map decodes. Their
compatibility statements cover all natural inputs, with no canonical-code
precondition. This module certifies the reflection hypotheses; certification
of the constructed relation tables and of exhaustive lifting minimality are
separate obligations.
-/

namespace Alexander313.Carlson.PrimitiveReflectionChecks

open Encodable Finite PrimitivePatternCode PrimitivePatternChecks
open PrimitiveContinuityChecks PrimitiveEmbeddingChecks
open PrimitiveEndpointIso (entry₂ entry₂_primrec entry₂_dataView mem_carrierView_iff)

/-- The original block to be copied lies in the half-open interval `[a,b)`. -/
def BlockData (C : Data) (a b : ℕ) (X : Finset ℕ) : Prop :=
  ∀ x ∈ X, x ∈ C.1 ∧ a ≤ x ∧ x < b

/-- Every copy point is fresh, below the anchor, and above every old point
below that anchor. -/
def PlacementData (C : Data) (N : Finset ℕ) (a : ℕ) : Prop :=
  (∀ x ∈ N, x ∉ C.1) ∧ (∀ x ∈ N, x < a) ∧
    ∀ xq ∈ N ×ˢ C.1, xq.2 < a → xq.2 < xq.1

/-- Strict monotonicity is required only on the supplied copied carrier. -/
def MapMonoData (N : Finset ℕ) (F : List ℕ) : Prop :=
  ∀ ij ∈ N ×ˢ N, ij.1 < ij.2 → mapAt F ij.1 < mapAt F ij.2

/-- The twelve downward-reflection fields, grouped without changing them. -/
def DownwardData (C : Data) (k : Bool) (a b : ℕ) (X N : Finset ℕ)
    (F : List ℕ) : Prop :=
  PatternData C ∧ a ∈ C.1 ∧ b ∈ C.1 ∧ a < b ∧ entryLevel C k (a, b) = true ∧
    BlockData C a b X ∧ X.Nonempty ∧ PlacementData C N a ∧
      N.image (mapAt F) = X ∧ MapMonoData N F

/-- The eleven upward-reflection fields, including both relation levels of
continuity and the original nontrivial extension condition. -/
def UpwardData (C D : Data) (a b : ℕ) (N : Finset ℕ) (F : List ℕ) : Prop :=
  PatternData D ∧ ContinuousData C D ∧ ExtensionAtData C D a ∧
    b ∈ C.1 ∧ a < b ∧ entry₂ C (a, b) = true ∧ PlacementData C N b ∧
      N.image (mapAt F) = D.1 \ C.1 ∧ MapMonoData N F

instance (C : Data) (a b : ℕ) (X : Finset ℕ) : Decidable (BlockData C a b X) := by
  unfold BlockData
  infer_instance

instance (C : Data) (N : Finset ℕ) (a : ℕ) : Decidable (PlacementData C N a) := by
  unfold PlacementData
  infer_instance

instance (N : Finset ℕ) (F : List ℕ) : Decidable (MapMonoData N F) := by
  unfold MapMonoData
  infer_instance

instance (C : Data) (k : Bool) (a b : ℕ) (X N : Finset ℕ) (F : List ℕ) :
    Decidable (DownwardData C k a b X N F) := by
  unfold DownwardData
  infer_instance

instance (C D : Data) (a b : ℕ) (N : Finset ℕ) (F : List ℕ) :
    Decidable (UpwardData C D a b N F) := by
  unfold UpwardData
  infer_instance

variable {σ : Type*} [Primcodable σ]

theorem blockData_primrec {C : σ → Data} {a b : σ → ℕ} {X : σ → Finset ℕ}
    (hC : Primrec C) (ha : Primrec a) (hb : Primrec b) (hX : Primrec X) :
    PrimrecPred (fun s => BlockData (C s) (a s) (b s) (X s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hp : PrimrecRel (fun (x : ℕ) s => x ∈ (C s).1 ∧ a s ≤ x ∧ x < b s) :=
    (PrimitiveFiniteData.finset_mem.comp Primrec.fst (hU.comp Primrec.snd)).and
      ((Primrec.nat_le.comp (ha.comp Primrec.snd) Primrec.fst).and
        (Primrec.nat_lt.comp Primrec.fst (hb.comp Primrec.snd)))
  exact ((PrimitiveFiniteOperations.forall_mem hp).comp hX Primrec.id).of_eq
    fun _ => Iff.rfl

theorem placementData_primrec {C : σ → Data} {N : σ → Finset ℕ} {a : σ → ℕ}
    (hC : Primrec C) (hN : Primrec N) (ha : Primrec a) :
    PrimrecPred (fun s => PlacementData (C s) (N s) (a s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hfresh : PrimrecRel (fun (x : ℕ) s => x ∉ (C s).1) :=
    (PrimitiveFiniteData.finset_mem.comp Primrec.fst (hU.comp Primrec.snd)).not
  have hbelow : PrimrecRel (fun (x : ℕ) s => x < a s) :=
    Primrec.nat_lt.comp Primrec.fst (ha.comp Primrec.snd)
  have hx : Primrec (fun p : (ℕ × ℕ) × σ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : (ℕ × ℕ) × σ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hgap : PrimrecRel (fun (xq : ℕ × ℕ) s => xq.2 < a s → xq.2 < xq.1) :=
    ((Primrec.nat_lt.comp hq (ha.comp Primrec.snd)).not.or
      (Primrec.nat_lt.comp hq hx)).of_eq fun _ => imp_iff_not_or.symm
  exact (((PrimitiveFiniteOperations.forall_mem hfresh).comp hN Primrec.id).and
    (((PrimitiveFiniteOperations.forall_mem hbelow).comp hN Primrec.id).and
      ((PrimitiveFiniteOperations.forall_mem hgap).comp
        (PrimitiveFiniteOperations.finset_product.comp hN hU) Primrec.id))).of_eq
          fun _ => Iff.rfl

theorem mapMonoData_primrec {N : σ → Finset ℕ} {F : σ → List ℕ}
    (hN : Primrec N) (hF : Primrec F) :
    PrimrecPred (fun s => MapMonoData (N s) (F s)) := by
  have hi : Primrec (fun p : (ℕ × ℕ) × σ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ) × σ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hF' : Primrec (fun p : (ℕ × ℕ) × σ => F p.2) := hF.comp Primrec.snd
  have hp : PrimrecRel (fun (ij : ℕ × ℕ) s =>
      ij.1 < ij.2 → mapAt (F s) ij.1 < mapAt (F s) ij.2) :=
    ((Primrec.nat_lt.comp hi hj).not.or
      (Primrec.nat_lt.comp (mapAt_primrec.comp hF' hi)
        (mapAt_primrec.comp hF' hj))).of_eq fun _ => imp_iff_not_or.symm
  exact ((PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hN hN) Primrec.id).of_eq
      fun _ => Iff.rfl

theorem downwardData_primrec {C : σ → Data} {k : σ → Bool} {a b : σ → ℕ}
    {X N : σ → Finset ℕ} {F : σ → List ℕ} (hC : Primrec C) (hk : Primrec k)
    (ha : Primrec a) (hb : Primrec b) (hX : Primrec X) (hN : Primrec N) (hF : Primrec F) :
    PrimrecPred (fun s => DownwardData (C s) (k s) (a s) (b s) (X s) (N s) (F s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have himage : Primrec (fun s => (N s).image (mapAt (F s))) :=
    (PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF hN
  exact ((patternData_primrec.comp hC).and
    ((PrimitiveFiniteData.finset_mem.comp ha hU).and
    ((PrimitiveFiniteData.finset_mem.comp hb hU).and
    ((Primrec.nat_lt.comp ha hb).and
    ((Primrec.eq.comp (entryLevel_primrec hC hk (ha.pair hb)) (Primrec.const true)).and
    ((blockData_primrec hC ha hb hX).and
    ((PrimitiveFiniteOperations.finset_nonempty.comp hX).and
    ((placementData_primrec hC hN ha).and
    ((Primrec.eq.comp himage hX).and (mapMonoData_primrec hN hF)))))))))).of_eq
      fun _ => Iff.rfl

theorem upwardData_primrec {C D : σ → Data} {a b : σ → ℕ}
    {N : σ → Finset ℕ} {F : σ → List ℕ} (hC : Primrec C) (hD : Primrec D)
    (ha : Primrec a) (hb : Primrec b) (hN : Primrec N) (hF : Primrec F) :
    PrimrecPred (fun s => UpwardData (C s) (D s) (a s) (b s) (N s) (F s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hV : Primrec (fun s => (D s).1) := Primrec.fst.comp hD
  have himage : Primrec (fun s => (N s).image (mapAt (F s))) :=
    (PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF hN
  exact ((patternData_primrec.comp hD).and
    ((continuousData_primrec hC hD).and
    ((extensionAtData_primrec hC hD ha).and
    ((PrimitiveFiniteData.finset_mem.comp hb hU).and
    ((Primrec.nat_lt.comp ha hb).and
    ((Primrec.eq.comp (entry₂_primrec.comp hC (ha.pair hb)) (Primrec.const true)).and
    ((placementData_primrec hC hN hb).and
    ((Primrec.eq.comp himage (PrimitiveFiniteOperations.finset_sdiff.comp hV hU)).and
      (mapMonoData_primrec hN hF))))))))).of_eq fun _ => Iff.rfl

private theorem forall_carrierView_iff {n : ℕ} (U : Finset (Fin n)) (p : ℕ → Prop) :
    (∀ x ∈ carrierView U, p x) ↔ ∀ x ∈ U, p x.val := by
  constructor
  · intro h x hx
    exact h x.val ((mem_carrierView U x).mpr hx)
  · intro h x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (mem_carrierView_iff U x).mp hx
    exact h x₀ hx₀

private theorem forall_carrierProduct_iff {n : ℕ} (U V : Finset (Fin n))
    (p : ℕ × ℕ → Prop) :
    (∀ ij ∈ carrierView U ×ˢ carrierView V, p ij) ↔
      ∀ i ∈ U, ∀ j ∈ V, p (i.val, j.val) := by
  constructor
  · intro h i hi j hj
    exact h (i.val, j.val) (Finset.mem_product.mpr
      ⟨(mem_carrierView U i).mpr hi, (mem_carrierView V j).mpr hj⟩)
  · intro h
    rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    obtain ⟨i₀, hi₀, rfl⟩ := (mem_carrierView_iff U i).mp hi
    obtain ⟨j₀, hj₀, rfl⟩ := (mem_carrierView_iff V j).mp hj
    exact h i₀ hi₀ j₀ hj₀

theorem blockData_dataView_iff {n : ℕ} (C : PatternCode n) (a b : Fin n)
    (X : Finset (Fin n)) :
    BlockData (dataView C) a.val b.val (carrierView X) ↔
      ∀ x ∈ X, x ∈ C.U ∧ a ≤ x ∧ x < b := by
  change (∀ x ∈ carrierView X, x ∈ carrierView C.U ∧ a.val ≤ x ∧ x < b.val) ↔ _
  rw [forall_carrierView_iff]
  simp only [mem_carrierView, Fin.le_def, Fin.lt_def]

theorem placementData_dataView_iff {n : ℕ} (C : PatternCode n)
    (N : Finset (Fin n)) (a : Fin n) :
    PlacementData (dataView C) (carrierView N) a.val ↔
      (∀ x ∈ N, x ∉ C.U) ∧ (∀ x ∈ N, x < a) ∧
        ∀ x ∈ N, ∀ q ∈ C.U, q < a → q < x := by
  unfold PlacementData
  change ((∀ x ∈ carrierView N, x ∉ carrierView C.U) ∧
    (∀ x ∈ carrierView N, x < a.val) ∧
    ∀ xq ∈ carrierView N ×ˢ carrierView C.U, xq.2 < a.val → xq.2 < xq.1) ↔ _
  rw [forall_carrierView_iff, forall_carrierView_iff, forall_carrierProduct_iff]
  simp only [mem_carrierView, Fin.lt_def]

theorem mapMonoData_mapView_iff {n : ℕ} (N : Finset (Fin n)) (g : Fin n → Fin n) :
    MapMonoData (carrierView N) (mapView g) ↔
      ∀ x ∈ N, ∀ y ∈ N, x < y → g x < g y := by
  unfold MapMonoData
  rw [forall_carrierPairs_iff]
  simp only [mapAt_mapView, Fin.lt_def]

theorem carrierView_nonempty_iff {n : ℕ} (X : Finset (Fin n)) :
    (carrierView X).Nonempty ↔ X.Nonempty := Finset.map_nonempty

theorem carrierView_sdiff {n : ℕ} (X Y : Finset (Fin n)) :
    carrierView (X \ Y) = carrierView X \ carrierView Y := Finset.map_sdiff X Y

/-- Exact recovery of all twelve original downward-reflection fields. -/
theorem downwardData_dataView_iff {n : ℕ} (C : PatternCode n) (k : Bool)
    (a b : Fin n) (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    DownwardData (dataView C) k a.val b.val (carrierView X) (carrierView N) (mapView g) ↔
      Str.DownData C.toStr (level k) a b X N g := by
  have himage : (carrierView N).image (mapAt (mapView g)) = carrierView X ↔
      N.image g = X := by rw [image_mapView, carrierView_eq_iff]
  constructor
  · rintro ⟨hpat, ha, hb, hab, hrel, hX, hXne, hplace, himg, hmono⟩
    obtain ⟨hNP, hNa, hNL⟩ := (placementData_dataView_iff C N a).mp hplace
    exact ⟨(patternData_dataView_iff C).mp hpat, (mem_carrierView C.U a).mp ha,
      (mem_carrierView C.U b).mp hb, hab, (entryLevel_dataView_iff C k a b).mp hrel,
      (blockData_dataView_iff C a b X).mp hX, (carrierView_nonempty_iff X).mp hXne,
      hNP, hNa, hNL, himage.mp himg, (mapMonoData_mapView_iff N g).mp hmono⟩
  · intro D
    exact ⟨(patternData_dataView_iff C).mpr D.pat, (mem_carrierView C.U a).mpr D.ha,
      (mem_carrierView C.U b).mpr D.hb, D.hab, (entryLevel_dataView_iff C k a b).mpr D.hrel,
      (blockData_dataView_iff C a b X).mpr D.hX, (carrierView_nonempty_iff X).mpr D.hXne,
      (placementData_dataView_iff C N a).mpr ⟨D.hNP, D.hNa, D.hNL⟩,
      himage.mpr D.himage, (mapMonoData_mapView_iff N g).mpr D.hmono⟩

/-- Exact recovery of all eleven original upward-reflection fields. -/
theorem upwardData_dataView_iff {n : ℕ} (C D : PatternCode n)
    (a b : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n) :
    UpwardData (dataView C) (dataView D) a.val b.val (carrierView N) (mapView g) ↔
      Str.UpData C.toStr D.toStr a b N g := by
  have himage : (carrierView N).image (mapAt (mapView g)) =
      (dataView D).1 \ (dataView C).1 ↔ N.image g = D.U \ C.U := by
    change (carrierView N).image (mapAt (mapView g)) =
      carrierView D.U \ carrierView C.U ↔ _
    rw [image_mapView, ← carrierView_sdiff, carrierView_eq_iff]
  have hrel : entry₂ (dataView C) (a.val, b.val) = true ↔ C.toStr.r₂ a b := by
    simp only [entry₂_dataView, PatternCode.toStr_r₂]
  constructor
  · rintro ⟨hpat, hcont, hext, hb, hab, hr, hplace, himg, hmono⟩
    obtain ⟨hNP, hNb, hNL⟩ := (placementData_dataView_iff C N b).mp hplace
    exact ⟨(patternData_dataView_iff D).mp hpat,
      (continuousData_dataView_iff C D).mp hcont,
      (extensionAtData_dataView_iff C D a).mp hext,
      (mem_carrierView C.U b).mp hb, hab, hrel.mp hr, hNP, hNb, hNL,
      himage.mp himg, (mapMonoData_mapView_iff N g).mp hmono⟩
  · intro H
    exact ⟨(patternData_dataView_iff D).mpr H.pat,
      (continuousData_dataView_iff C D).mpr H.cont,
      (extensionAtData_dataView_iff C D a).mpr H.ext,
      (mem_carrierView C.U b).mpr H.hb, H.hab, hrel.mpr H.hrel,
      (placementData_dataView_iff C N b).mpr ⟨H.hNP, H.hNb, H.hNL⟩,
      himage.mpr H.himage, (mapMonoData_mapView_iff N g).mpr H.hmono⟩

@[simp] theorem decide_downwardData {n : ℕ} (C : PatternCode n) (k : Bool)
    (a b : Fin n) (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    decide (DownwardData (dataView C) k a.val b.val (carrierView X) (carrierView N)
      (mapView g)) = C.checkDownward (level k) a b X N g := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkDownward_eq_true]
  exact downwardData_dataView_iff C k a b X N g

@[simp] theorem decide_upwardData {n : ℕ} (C D : PatternCode n)
    (a b : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n) :
    decide (UpwardData (dataView C) (dataView D) a.val b.val (carrierView N) (mapView g)) =
      C.checkUpward D a b N g := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkUpward_eq_true]
  exact upwardData_dataView_iff C D a b N g

private theorem carrierView_primrec (n : ℕ) : Primrec (@carrierView n) :=
  Primrec.encode_iff.mp
    (Primrec.encode.of_eq fun S => (encode_carrierView S).symm)

private theorem mapView_primrec (n : ℕ) : Primrec (@mapView n n) := by
  unfold mapView
  apply Primrec.list_ofFn
  intro i
  exact Primrec.fin_val.comp (Primrec.fin_app.comp Primrec.id (Primrec.const i))

abbrev DownwardInputs (n : ℕ) := PatternCode n × Fin n × Fin n ×
  Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n)

abbrev UpwardInputs (n : ℕ) := PatternCode n × PatternCode n × Fin n × Fin n ×
  Finset (Fin n) × (Fin n → Fin n)

/-- The existing downward checker is certified at each finite size and level. -/
theorem original_checkDownward_primrec (n : ℕ) (k : Lvl) :
    Primrec (fun p : DownwardInputs n => p.1.checkDownward k p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have hval : Primrec (fun a : Fin n => a.val) := Primrec.encode.of_eq fun _ => rfl
  have hC : Primrec (fun p : DownwardInputs n => dataView p.1) :=
    (PrimitiveFiniteChecks.dataView_primrec n).comp Primrec.fst
  have ha : Primrec (fun p : DownwardInputs n => p.2.1.val) :=
    hval.comp (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : DownwardInputs n => p.2.2.1.val) :=
    hval.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hX : Primrec (fun p : DownwardInputs n => carrierView p.2.2.2.1) :=
    (carrierView_primrec n).comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hN : Primrec (fun p : DownwardInputs n => carrierView p.2.2.2.2.1) :=
    (carrierView_primrec n).comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hF : Primrec (fun p : DownwardInputs n => mapView p.2.2.2.2.2) :=
    (mapView_primrec n).comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have h (b : Bool) : Primrec (fun p : DownwardInputs n =>
      p.1.checkDownward (level b) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
    (downwardData_primrec hC (Primrec.const b) ha hb hX hN hF).decide.of_eq
      fun p => decide_downwardData p.1 b p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
  cases k
  · exact h false
  · exact h true

theorem original_checkUpward_primrec (n : ℕ) :
    Primrec (fun p : UpwardInputs n => p.1.checkUpward p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have hval : Primrec (fun a : Fin n => a.val) := Primrec.encode.of_eq fun _ => rfl
  have hC : Primrec (fun p : UpwardInputs n => dataView p.1) :=
    (PrimitiveFiniteChecks.dataView_primrec n).comp Primrec.fst
  have hD : Primrec (fun p : UpwardInputs n => dataView p.2.1) :=
    (PrimitiveFiniteChecks.dataView_primrec n).comp (Primrec.fst.comp Primrec.snd)
  have ha : Primrec (fun p : UpwardInputs n => p.2.2.1.val) :=
    hval.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun p : UpwardInputs n => p.2.2.2.1.val) :=
    hval.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hN : Primrec (fun p : UpwardInputs n => carrierView p.2.2.2.2.1) :=
    (carrierView_primrec n).comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hF : Primrec (fun p : UpwardInputs n => mapView p.2.2.2.2.2) :=
    (mapView_primrec n).comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (upwardData_primrec hC hD ha hb hN hF).decide.of_eq
    fun p => decide_upwardData p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2

/-- Shared decoded anchors, fresh carrier and total finite matching map. -/
abbrev Parameters := ℕ × ℕ × Finset ℕ × List ℕ

def decodeParameters (n a b s f : ℕ) : Option Parameters :=
  (decodeLabel n a).bind fun a' =>
    (decodeLabel n b).bind fun b' =>
      (decodeCarrier n s).bind fun N =>
        (decodeMap n n f).map fun F => (a', b', N, F)

theorem decodeParameters_primrec {n a b s f : σ → ℕ} (hn : Primrec n)
    (ha : Primrec a) (hb : Primrec b) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun x => decodeParameters (n x) (a x) (b x) (s x) (f x)) := by
  have hA : Primrec (fun x => decodeLabel (n x) (a x)) := decodeLabel_primrec.comp hn ha
  have hB : Primrec (fun x => decodeLabel (n x) (b x)) := decodeLabel_primrec.comp hn hb
  have hN : Primrec (fun x => decodeCarrier (n x) (s x)) := decodeCarrier_primrec.comp hn hs
  have hF : Primrec (fun x => decodeMap (n x) (n x) (f x)) := decodeMap_primrec hn hn hf
  unfold decodeParameters
  refine Primrec.option_bind hA ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (hB.comp Primrec.fst) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (hN.comp (Primrec.fst.comp Primrec.fst)) ?_
  apply Primrec₂.mk
  refine Primrec.option_map
    (hF.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) ?_
  have h₁ : Primrec (fun p : (((σ × ℕ) × ℕ) × Finset ℕ) × List ℕ => p.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have h₂ : Primrec (fun p : (((σ × ℕ) × ℕ) × Finset ℕ) × List ℕ => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have h₃ : Primrec (fun p : (((σ × ℕ) × ℕ) × Finset ℕ) × List ℕ => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have h₄ : Primrec (fun p : (((σ × ℕ) × ℕ) × Finset ℕ) × List ℕ => p.2) := Primrec.snd
  exact (h₁.pair (h₂.pair (h₃.pair h₄))).to₂

/-- The shared decoder uses exactly the original point, carrier and map codecs. -/
theorem decodeParameters_eq (n a b s f : ℕ) : decodeParameters n a b s f =
    (decode (α := Fin n) a).bind fun a' =>
      (decode (α := Fin n) b).bind fun b' =>
        (decode (α := Finset (Fin n)) s).bind fun N =>
          (decode (α := Fin n → Fin n) f).map fun g =>
            (a'.val, b'.val, carrierView N, mapView g) := by
  cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [decodeParameters, decodeLabel_eq, decodeCarrier_eq, decodeMap_eq, ha, hb, hN, hg]

@[simp] theorem decodeParameters_encode {n : ℕ} (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    decodeParameters n (encode a) (encode b) (encode N) (encode g) =
      some (a.val, b.val, carrierView N, mapView g) := by
  rw [decodeParameters_eq, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek]
  rfl

/-- Total downward checking, with failure rejection in every decoded field. -/
def checkDownward (k : Bool) (n c a b x s f : ℕ) : Bool :=
  ((decodeData n c).bind fun C =>
    (decodeCarrier n x).bind fun X =>
      (decodeParameters n a b s f).map fun p =>
        decide (DownwardData C k p.1 p.2.1 X p.2.2.1 p.2.2.2)).getD false

/-- Total upward checking, including both original pattern records. -/
def checkUpward (n c d a b s f : ℕ) : Bool :=
  ((decodeData n c).bind fun C =>
    (decodeData n d).bind fun D =>
      (decodeParameters n a b s f).map fun p =>
        decide (UpwardData C D p.1 p.2.1 p.2.2.1 p.2.2.2)).getD false

private theorem checkDownward_comp {k : σ → Bool} {n c a b x s f : σ → ℕ}
    (hk : Primrec k) (hn : Primrec n) (hc : Primrec c) (ha : Primrec a)
    (hb : Primrec b) (hx : Primrec x) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun p => checkDownward (k p) (n p) (c p) (a p) (b p) (x p) (s p) (f p)) := by
  have hC : Primrec (fun p => decodeData (n p) (c p)) := decodeData_primrec.comp hn hc
  have hX : Primrec (fun p => decodeCarrier (n p) (x p)) := decodeCarrier_primrec.comp hn hx
  have hP : Primrec (fun p => decodeParameters (n p) (a p) (b p) (s p) (f p)) :=
    decodeParameters_primrec hn ha hb hs hf
  have h : Primrec (fun p =>
      (decodeData (n p) (c p)).bind fun C =>
        (decodeCarrier (n p) (x p)).bind fun X =>
          (decodeParameters (n p) (a p) (b p) (s p) (f p)).map fun q =>
            decide (DownwardData C (k p) q.1 q.2.1 X q.2.2.1 q.2.2.2)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    refine Primrec.option_bind (hX.comp Primrec.fst) ?_
    apply Primrec₂.mk
    refine Primrec.option_map (hP.comp (Primrec.fst.comp Primrec.fst)) ?_
    have htest : Primrec (fun q : ((σ × Data) × Finset ℕ) × Parameters =>
        decide (DownwardData q.1.1.2 (k q.1.1.1) q.2.1 q.2.2.1 q.1.2
          q.2.2.2.1 q.2.2.2.2)) :=
      (downwardData_primrec (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (hk.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).decide
    exact htest.to₂
  exact (Primrec.option_getD.comp h (Primrec.const false)).of_eq fun _ => rfl

private theorem checkUpward_comp {n c d a b s f : σ → ℕ}
    (hn : Primrec n) (hc : Primrec c) (hd : Primrec d) (ha : Primrec a)
    (hb : Primrec b) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun p => checkUpward (n p) (c p) (d p) (a p) (b p) (s p) (f p)) := by
  have hC : Primrec (fun p => decodeData (n p) (c p)) := decodeData_primrec.comp hn hc
  have hD : Primrec (fun p => decodeData (n p) (d p)) := decodeData_primrec.comp hn hd
  have hP : Primrec (fun p => decodeParameters (n p) (a p) (b p) (s p) (f p)) :=
    decodeParameters_primrec hn ha hb hs hf
  have h : Primrec (fun p =>
      (decodeData (n p) (c p)).bind fun C =>
        (decodeData (n p) (d p)).bind fun D =>
          (decodeParameters (n p) (a p) (b p) (s p) (f p)).map fun q =>
            decide (UpwardData C D q.1 q.2.1 q.2.2.1 q.2.2.2)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    refine Primrec.option_bind (hD.comp Primrec.fst) ?_
    apply Primrec₂.mk
    refine Primrec.option_map (hP.comp (Primrec.fst.comp Primrec.fst)) ?_
    have htest : Primrec (fun q : ((σ × Data) × Data) × Parameters =>
        decide (UpwardData q.1.1.2 q.1.2 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) :=
      (upwardData_primrec (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).decide
    exact htest.to₂
  exact (Primrec.option_getD.comp h (Primrec.const false)).of_eq fun _ => rfl

abbrev RawInputs := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- A single primitive-recursive function works at every bound for each level. -/
theorem checkDownward_primrec (k : Bool) :
    Primrec (fun p : RawInputs => checkDownward k p.1 p.2.1 p.2.2.1 p.2.2.2.1
      p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) :=
  checkDownward_comp (Primrec.const k) Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem checkUpward_primrec :
    Primrec (fun p : RawInputs => checkUpward p.1 p.2.1 p.2.2.1 p.2.2.2.1
      p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) :=
  checkUpward_comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

/-- All-input compatibility with the original six downward parameter decoders. -/
theorem checkDownward_eq (k : Bool) (n c a b x s f : ℕ) : checkDownward k n c a b x s f =
    match decode (α := PatternCode n) c, decode (α := Fin n) a, decode (α := Fin n) b,
        decode (α := Finset (Fin n)) x, decode (α := Finset (Fin n)) s,
        decode (α := Fin n → Fin n) f with
    | some C, some a', some b', some X, some N, some g =>
        C.checkDownward (level k) a' b' X N g
    | _, _, _, _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hX : decode (α := Finset (Fin n)) x <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [checkDownward, decodeData_eq, decodeCarrier_eq, decodeParameters_eq,
      hC, ha, hb, hX, hN, hg]

/-- All-input compatibility with the original six upward parameter decoders. -/
theorem checkUpward_eq (n c d a b s f : ℕ) : checkUpward n c d a b s f =
    match decode (α := PatternCode n) c, decode (α := PatternCode n) d,
        decode (α := Fin n) a, decode (α := Fin n) b,
        decode (α := Finset (Fin n)) s, decode (α := Fin n → Fin n) f with
    | some C, some D, some a', some b', some N, some g => C.checkUpward D a' b' N g
    | _, _, _, _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [checkUpward, decodeData_eq, decodeParameters_eq, hC, hD, ha, hb, hN, hg]

@[simp] theorem checkDownward_encode {n : ℕ} (k : Bool) (C : PatternCode n)
    (a b : Fin n) (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    checkDownward k n (encode C) (encode a) (encode b) (encode X) (encode N) (encode g) =
      C.checkDownward (level k) a b X N g := by
  rw [checkDownward_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek, Encodable.encodek]

@[simp] theorem checkUpward_encode {n : ℕ} (C D : PatternCode n)
    (a b : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n) :
    checkUpward n (encode C) (encode D) (encode a) (encode b) (encode N) (encode g) =
      C.checkUpward D a b N g := by
  rw [checkUpward_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek, Encodable.encodek]

/-- Exact downward acceptance, including all successful noncanonical decodes. -/
theorem checkDownward_eq_true (k : Bool) (n c a b x s f : ℕ) :
    checkDownward k n c a b x s f = true ↔
      ∃ (C : PatternCode n) (a' b' : Fin n) (X N : Finset (Fin n)) (g : Fin n → Fin n),
        decode c = some C ∧ decode a = some a' ∧ decode b = some b' ∧
        decode x = some X ∧ decode s = some N ∧ decode f = some g ∧
          Str.DownData C.toStr (level k) a' b' X N g := by
  rw [checkDownward_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hX : decode (α := Finset (Fin n)) x <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [PatternCode.checkDownward_eq_true]

theorem checkUpward_eq_true (n c d a b s f : ℕ) : checkUpward n c d a b s f = true ↔
    ∃ (C D : PatternCode n) (a' b' : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n),
      decode c = some C ∧ decode d = some D ∧ decode a = some a' ∧
      decode b = some b' ∧ decode s = some N ∧ decode f = some g ∧
        Str.UpData C.toStr D.toStr a' b' N g := by
  rw [checkUpward_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [PatternCode.checkUpward_eq_true]

set_option maxHeartbeats 800000 in
/-- One machine implements downward reflection checking at each level. -/
theorem checkDownward_program (k : Bool) : ∃ machine : Nat.Partrec.Code,
    ∀ n c a b x s f : ℕ,
      machine.eval (Nat.pair n (Nat.pair c (Nat.pair a (Nat.pair b
        (Nat.pair x (Nat.pair s f)))))) =
          Part.some (encode (checkDownward k n c a b x s f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program (checkDownward_primrec k)
  exact ⟨machine, fun n c a b x s f => hm ((n, c, a, b, x, s, f) : RawInputs)⟩

set_option maxHeartbeats 800000 in
theorem checkUpward_program : ∃ machine : Nat.Partrec.Code, ∀ n c d a b s f : ℕ,
    machine.eval (Nat.pair n (Nat.pair c (Nat.pair d (Nat.pair a
      (Nat.pair b (Nat.pair s f)))))) =
        Part.some (encode (checkUpward n c d a b s f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkUpward_primrec
  exact ⟨machine, fun n c d a b s f => hm ((n, c, d, a, b, s, f) : RawInputs)⟩

end Alexander313.Carlson.PrimitiveReflectionChecks
