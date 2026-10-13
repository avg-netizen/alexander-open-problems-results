import Alexander313.Carlson.PrimitiveEmbeddingChecks
import Alexander313.Carlson.PrimitiveContinuityChecks
import Alexander313.Carlson.FiniteLifting

/-!
# Primitive-recursive continuous embedding checks

A continuous embedding identifies its source with the restriction of the
target to the source image, and that restricted target must be a continuous
substructure of the whole target. The two existing certified checks can
therefore be composed after computing the finite image carrier. Both target
relation tables are retained exactly when this carrier is replaced.

The source and target bounds are independent natural inputs. The raw checker
uses the original pattern and index-tagged finite-function decoders, including
validation of every map value outside the source carrier. Compatibility is
proved for all raw codes, with no canonical-input or patternhood assumption.
-/

namespace Alexander313.Carlson.PrimitiveContinuousEmbeddingChecks

open Encodable Finite PrimitivePatternCode PrimitiveEmbeddingChecks
open PrimitiveContinuityChecks (ContinuousData continuousData_primrec
  continuousData_dataView_iff)

/-- The target's complete tables, restricted to the image carrier only. -/
def imageData (C D : Data) (F : List ℕ) : Data :=
  (C.1.image (mapAt F), D.2)

/-- A finite code for precisely the restricted target in the original
continuous embedding predicate. No off-carrier table entry is changed. -/
def imageCode {n m : ℕ} (C : PatternCode n) (D : PatternCode m)
    (f : Fin n → Fin m) : PatternCode m :=
  { D with U := C.U.image f }

@[simp] theorem imageCode_toStr {n m : ℕ} (C : PatternCode n) (D : PatternCode m)
    (f : Fin n → Fin m) :
    (imageCode C D f).toStr = D.toStr.restrict (C.toStr.U.image f) := rfl

/-- Natural image formation agrees with finite-label image formation. -/
@[simp] theorem imageData_dataView {n m : ℕ} (C : PatternCode n) (D : PatternCode m)
    (f : Fin n → Fin m) :
    imageData (dataView C) (dataView D) (mapView f) = dataView (imageCode C D f) := by
  change ((carrierView C.U).image (mapAt (mapView f)), (dataView D).2) =
    (carrierView (C.U.image f), (dataView D).2)
  rw [image_mapView]

/-- Exact embedding into the image and continuity of that image in the target. -/
def ContinuousEmbeddingData (C D : Data) (F : List ℕ) : Prop :=
  IsoData C (imageData C D F) F ∧ ContinuousData (imageData C D F) D

instance (C D : Data) (F : List ℕ) : Decidable (ContinuousEmbeddingData C D F) := by
  unfold ContinuousEmbeddingData
  infer_instance

variable {σ : Type*} [Primcodable σ]

theorem imageData_primrec {C D : σ → Data} {F : σ → List ℕ}
    (hC : Primrec C) (hD : Primrec D) (hF : Primrec F) :
    Primrec (fun s => imageData (C s) (D s) (F s)) :=
  ((PrimitiveFiniteOperations.finset_image mapAt_primrec).comp hF
    (Primrec.fst.comp hC)).pair (Primrec.snd.comp hD)

/-- Image computation and both finite predicates have explicit certificates;
there is no unproved decidability-to-primitive-recursion implication. -/
theorem continuousEmbeddingData_primrec {C D : σ → Data} {F : σ → List ℕ}
    (hC : Primrec C) (hD : Primrec D) (hF : Primrec F) :
    PrimrecPred (fun s => ContinuousEmbeddingData (C s) (D s) (F s)) := by
  have hI : Primrec (fun s => imageData (C s) (D s) (F s)) :=
    imageData_primrec hC hD hF
  exact ((isoData_primrec hC hI hF).and
    (continuousData_primrec hI hD)).of_eq fun _ => Iff.rfl

/-- Agreement with the original predicate includes continuity in the target's
ambient order and exact preservation and reflection of both relations. -/
theorem continuousEmbeddingData_dataView_iff {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    ContinuousEmbeddingData (dataView C) (dataView D) (mapView f) ↔
      Str.ContinuousEmbedding C.toStr D.toStr f := by
  simp only [ContinuousEmbeddingData, imageData_dataView,
    isoData_dataView_iff, continuousData_dataView_iff, imageCode_toStr] <;> rfl

@[simp] theorem decide_continuousEmbeddingData {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    decide (ContinuousEmbeddingData (dataView C) (dataView D) (mapView f)) =
      C.checkEmbedding D f := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkEmbedding_eq_true]
  exact continuousEmbeddingData_dataView_iff C D f

/-- Total continuous embedding checking with the same original raw-code
boundary as the covering and isomorphism checkers. -/
def checkEmbedding (n m c d f : ℕ) : Bool :=
  checkWith (fun p => decide (ContinuousEmbeddingData p.1 p.2.1 p.2.2)) n m c d f

theorem checkEmbedding_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ =>
      checkEmbedding p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :=
  checkWith_primrec (continuousEmbeddingData_primrec Primrec.fst
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide

/-- Exact compatibility on every raw input. All three decodes must succeed,
including the map's original position tags and both ambient bounds. -/
theorem checkEmbedding_eq (n m c d f : ℕ) : checkEmbedding n m c d f =
    match decode (α := PatternCode n) c, decode (α := PatternCode m) d,
        decode (α := Fin n → Fin m) f with
    | some C, some D, some F => C.checkEmbedding D F
    | _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode m) d <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [checkEmbedding, checkWith, decodeData_eq, decodeMap_eq, hC, hD, hF]

@[simp] theorem checkEmbedding_encode {n m : ℕ} (C : PatternCode n)
    (D : PatternCode m) (f : Fin n → Fin m) :
    checkEmbedding n m (encode C) (encode D) (encode f) = C.checkEmbedding D f := by
  rw [checkEmbedding_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek]

/-- Positive acceptance is precisely successful original decoding followed
by the original continuous embedding predicate. -/
theorem checkEmbedding_eq_true (n m c d f : ℕ) : checkEmbedding n m c d f = true ↔
    ∃ (C : PatternCode n) (D : PatternCode m) (F : Fin n → Fin m),
      decode c = some C ∧ decode d = some D ∧ decode f = some F ∧
        Str.ContinuousEmbedding C.toStr D.toStr F := by
  rw [checkEmbedding_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode m) d <;>
    cases hF : decode (α := Fin n → Fin m) f <;>
    simp [PatternCode.checkEmbedding_eq_true]

/-- A single total natural-input machine handles all source and target
dimensions, valid finite maps and malformed raw codes. -/
theorem checkEmbedding_program : ∃ machine : Nat.Partrec.Code, ∀ n m c d f : ℕ,
    machine.eval (Nat.pair n (Nat.pair m (Nat.pair c (Nat.pair d f)))) =
      Part.some (encode (checkEmbedding n m c d f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkEmbedding_primrec
  exact ⟨machine, fun n m c d f => hm (n, m, c, d, f)⟩

end Alexander313.Carlson.PrimitiveContinuousEmbeddingChecks
