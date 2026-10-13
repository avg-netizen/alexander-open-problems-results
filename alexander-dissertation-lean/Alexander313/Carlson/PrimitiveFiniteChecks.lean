import Alexander313.Carlson.PrimitiveEndpointIso

/-!
# Primitive-recursive finite agreement and substructure checks

The natural-number algorithms here certify two structural tests needed by
finite derivation checking. They use the existing pattern and carrier codecs,
uniformly in the ambient size, and reject every failed decode. Agreement reads
both tables on the supplied set, even outside the source carrier. Substructure
checking instead compares the tables only on the source carrier.

This is a partial finite-checker milestone: no primitive-recursive certificate
for patternhood, reflection, minimality, or the recursive derivation checker
is claimed. The original `PatternCode.checkAgree` and `checkSub` are unchanged.
-/

namespace Alexander313.Carlson.PrimitiveFiniteChecks

open Encodable Finite PrimitivePatternCode
open PrimitiveEndpointIso (entry₁ entry₂ entry₁_primrec entry₂_primrec
  entry₁_dataView entry₂_dataView mem_carrierView_iff)

/-- Both stored Boolean relations agree at one pair of natural labels. -/
def PairAgree (C D : Data) (ij : ℕ × ℕ) : Prop :=
  entry₁ C ij = entry₁ D ij ∧ entry₂ C ij = entry₂ D ij

instance (C D : Data) (ij : ℕ × ℕ) : Decidable (PairAgree C D ij) := by
  unfold PairAgree
  infer_instance

/-- Agreement on the supplied set, not implicitly on a structure's carrier. -/
def AgreeData (C D : Data) (S : Finset ℕ) : Prop :=
  ∀ ij ∈ S ×ˢ S, PairAgree C D ij

instance (C D : Data) (S : Finset ℕ) : Decidable (AgreeData C D S) := by
  unfold AgreeData
  infer_instance

/-- Carrier inclusion and agreement on every source-carrier pair. -/
def SubData (C D : Data) : Prop := C.1 ⊆ D.1 ∧ AgreeData C D C.1

instance (C D : Data) : Decidable (SubData C D) := by
  unfold SubData
  infer_instance

variable {σ : Type*} [Primcodable σ]

theorem pairAgree_primrec {C D : σ → Data} (hC : Primrec C) (hD : Primrec D) :
    PrimrecRel (fun (ij : ℕ × ℕ) s => PairAgree (C s) (D s) ij) := by
  have hC' := hC.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  have hD' := hD.comp (Primrec.snd : Primrec (@Prod.snd (ℕ × ℕ) σ))
  exact ((Primrec.eq.comp (entry₁_primrec.comp hC' Primrec.fst)
      (entry₁_primrec.comp hD' Primrec.fst)).and
    (Primrec.eq.comp (entry₂_primrec.comp hC' Primrec.fst)
      (entry₂_primrec.comp hD' Primrec.fst))).of_eq fun _ => Iff.rfl

theorem agreeData_primrec {C D : σ → Data} {S : σ → Finset ℕ}
    (hC : Primrec C) (hD : Primrec D) (hS : Primrec S) :
    PrimrecPred (fun s => AgreeData (C s) (D s) (S s)) :=
  ((PrimitiveFiniteOperations.forall_mem (pairAgree_primrec hC hD)).comp
    (PrimitiveFiniteOperations.finset_product.comp hS hS) Primrec.id).of_eq
      fun _ => Iff.rfl

theorem subData_primrec : PrimrecRel SubData :=
  ((PrimitiveFiniteOperations.finset_subset.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).and
    (agreeData_primrec Primrec.fst Primrec.snd (Primrec.fst.comp Primrec.fst))).of_eq
      fun _ => Iff.rfl

/-- Erasing the bounds on finite labels preserves and reflects inclusion. -/
theorem carrierView_subset_iff {n : ℕ} (S T : Finset (Fin n)) :
    carrierView S ⊆ carrierView T ↔ S ⊆ T := by
  constructor
  · intro h i hi
    exact (mem_carrierView T i).mp (h ((mem_carrierView S i).mpr hi))
  · intro h i hi
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff S i).mp hi
    exact (mem_carrierView T x).mpr (h hx)

/-- The uniform data test has exactly the original agreement semantics. -/
theorem agreeData_dataView_iff {n : ℕ} (C D : PatternCode n) (S : Finset (Fin n)) :
    AgreeData (dataView C) (dataView D) (carrierView S) ↔
      Str.Agree C.toStr D.toStr S := by
  constructor
  · intro h x hx y hy
    have hp := h (x.val, y.val) (Finset.mem_product.mpr
      ⟨(mem_carrierView S x).mpr hx, (mem_carrierView S y).mpr hy⟩)
    change entry₁ (dataView C) (x.val, y.val) = entry₁ (dataView D) (x.val, y.val) ∧
      entry₂ (dataView C) (x.val, y.val) = entry₂ (dataView D) (x.val, y.val) at hp
    rw [entry₁_dataView, entry₁_dataView, entry₂_dataView, entry₂_dataView] at hp
    exact ⟨Bool.eq_iff_iff.mp hp.1, Bool.eq_iff_iff.mp hp.2⟩
  · intro h
    rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff S i).mp hi
    obtain ⟨y, hy, rfl⟩ := (mem_carrierView_iff S j).mp hj
    unfold PairAgree
    rw [entry₁_dataView, entry₁_dataView, entry₂_dataView, entry₂_dataView]
    exact ⟨Bool.eq_iff_iff.mpr (h x hx y hy).1, Bool.eq_iff_iff.mpr (h x hx y hy).2⟩

/-- No patternhood assumption and no off-carrier agreement is required. -/
theorem subData_dataView_iff {n : ℕ} (C D : PatternCode n) :
    SubData (dataView C) (dataView D) ↔ Str.IsSub C.toStr D.toStr := by
  change (carrierView C.U ⊆ carrierView D.U ∧
    AgreeData (dataView C) (dataView D) (carrierView C.U)) ↔ _
  rw [carrierView_subset_iff, agreeData_dataView_iff]
  rfl

@[simp] theorem decide_agreeData {n : ℕ} (C D : PatternCode n) (S : Finset (Fin n)) :
    decide (AgreeData (dataView C) (dataView D) (carrierView S)) = C.checkAgree D S := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkAgree_eq_true]
  exact agreeData_dataView_iff C D S

@[simp] theorem decide_subData {n : ℕ} (C D : PatternCode n) :
    decide (SubData (dataView C) (dataView D)) = C.checkSub D := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkSub_eq_true]
  exact subData_dataView_iff C D

/-- The original lossless view also has a certificate for each fixed size. -/
theorem dataView_primrec (n : ℕ) : Primrec (@dataView n) :=
  Primrec.option_some_iff.mp
    ((decodeData_primrec.comp (Primrec.const n) Primrec.encode).of_eq
      fun C => decodeData_encode C)

theorem original_checkAgree_primrec (n : ℕ) :
    Primrec (fun p : PatternCode n × PatternCode n × Finset (Fin n) =>
      p.1.checkAgree p.2.1 p.2.2) := by
  have hS : Primrec (fun S : Finset (Fin n) => carrierView S) := by
    apply Primrec.encode_iff.mp
    exact Primrec.encode.of_eq fun S => (encode_carrierView S).symm
  exact (agreeData_primrec ((dataView_primrec n).comp Primrec.fst)
    ((dataView_primrec n).comp (Primrec.fst.comp Primrec.snd))
    (hS.comp (Primrec.snd.comp Primrec.snd))).decide.of_eq
      fun p => decide_agreeData p.1 p.2.1 p.2.2

theorem original_checkSub_primrec (n : ℕ) : Primrec₂ (@PatternCode.checkSub n) :=
  (subData_primrec.decide.comp ((dataView_primrec n).comp Primrec.fst)
    ((dataView_primrec n).comp Primrec.snd)).of_eq
      fun p => decide_subData p.1 p.2

/-- Total raw-code agreement checking, with an explicitly encoded test set. -/
def checkAgree (n c d s : ℕ) : Bool :=
  match decodeData n c with
  | none => false
  | some C => match decodeData n d with
    | none => false
    | some D => match decodeCarrier n s with
      | none => false
      | some S => decide (AgreeData C D S)

/-- Total raw-code substructure checking. Invalid codes always reject. -/
def checkSub (n c d : ℕ) : Bool :=
  match decodeData n c with
  | none => false
  | some C => match decodeData n d with
    | none => false
    | some D => decide (SubData C D)

/-- One primitive-recursive algorithm handles every ambient size. -/
theorem checkSub_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => checkSub p.1 p.2.1 p.2.2) := by
  have hC : Primrec (fun p : ℕ × ℕ × ℕ => decodeData p.1 p.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hD : Primrec (fun p : ℕ × ℕ × ℕ => decodeData p.1 p.2.2) :=
    decodeData_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have h : Primrec (fun p : ℕ × ℕ × ℕ =>
      (decodeData p.1 p.2.1).bind fun C =>
        (decodeData p.1 p.2.2).map fun D => decide (SubData C D)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    exact Primrec.option_map (hD.comp Primrec.fst)
      (subData_primrec.decide.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  refine (Primrec.option_getD.comp h (Primrec.const false)).of_eq ?_
  intro p
  cases hC : decodeData p.1 p.2.1 <;>
    cases hD : decodeData p.1 p.2.2 <;> simp [checkSub, hC, hD]

/-- Agreement checking is uniform in both table size and the supplied set. -/
theorem checkAgree_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ => checkAgree p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hC : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => decodeData p.1 p.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hD : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => decodeData p.1 p.2.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hS : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => decodeCarrier p.1 p.2.2.2) :=
    decodeCarrier_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h : Primrec (fun p : ℕ × ℕ × ℕ × ℕ =>
      (decodeData p.1 p.2.1).bind fun C =>
        (decodeData p.1 p.2.2.1).bind fun D =>
          (decodeCarrier p.1 p.2.2.2).map fun S => decide (AgreeData C D S)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    refine Primrec.option_bind (hD.comp Primrec.fst) ?_
    apply Primrec₂.mk
    exact Primrec.option_map (hS.comp (Primrec.fst.comp Primrec.fst))
      (agreeData_primrec (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd).decide.to₂
  refine (Primrec.option_getD.comp h (Primrec.const false)).of_eq ?_
  intro p
  cases hC : decodeData p.1 p.2.1 <;>
    cases hD : decodeData p.1 p.2.2.1 <;>
    cases hS : decodeCarrier p.1 p.2.2.2 <;> simp [checkAgree, hC, hD, hS]

/-- All-input compatibility, including noncanonical accepted encodings and
failed decodes. This is stronger than an encode/decode round trip. -/
theorem checkSub_eq (n c d : ℕ) : checkSub n c d =
    match decode (α := PatternCode n) c, decode (α := PatternCode n) d with
    | some C, some D => C.checkSub D
    | _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    simp [checkSub, decodeData_eq, hC, hD]

theorem checkAgree_eq (n c d s : ℕ) : checkAgree n c d s =
    match decode (α := PatternCode n) c, decode (α := PatternCode n) d,
        decode (α := Finset (Fin n)) s with
    | some C, some D, some S => C.checkAgree D S
    | _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases hS : decode (α := Finset (Fin n)) s <;>
    simp [checkAgree, decodeData_eq, decodeCarrier_eq, hC, hD, hS]

@[simp] theorem checkSub_encode {n : ℕ} (C D : PatternCode n) :
    checkSub n (encode C) (encode D) = C.checkSub D := by
  rw [checkSub_eq, Encodable.encodek, Encodable.encodek]

@[simp] theorem checkAgree_encode {n : ℕ} (C D : PatternCode n) (S : Finset (Fin n)) :
    checkAgree n (encode C) (encode D) (encode S) = C.checkAgree D S := by
  rw [checkAgree_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek]

/-- Exact positive acceptance semantics for arbitrary raw inputs. -/
theorem checkSub_eq_true (n c d : ℕ) : checkSub n c d = true ↔
    ∃ C D : PatternCode n, decode c = some C ∧ decode d = some D ∧
      Str.IsSub C.toStr D.toStr := by
  rw [checkSub_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    simp [PatternCode.checkSub_eq_true]

theorem checkAgree_eq_true (n c d s : ℕ) : checkAgree n c d s = true ↔
    ∃ (C D : PatternCode n) (S : Finset (Fin n)),
      decode c = some C ∧ decode d = some D ∧ decode s = some S ∧
        Str.Agree C.toStr D.toStr S := by
  rw [checkAgree_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases hS : decode (α := Finset (Fin n)) s <;>
    simp [PatternCode.checkAgree_eq_true]

/-- A single total machine handles every natural size and both raw codes. -/
theorem checkSub_program : ∃ machine : Nat.Partrec.Code, ∀ n c d : ℕ,
    machine.eval (Nat.pair n (Nat.pair c d)) = Part.some (encode (checkSub n c d)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkSub_primrec
  exact ⟨machine, fun n c d => hm (n, c, d)⟩

theorem checkAgree_program : ∃ machine : Nat.Partrec.Code, ∀ n c d s : ℕ,
    machine.eval (Nat.pair n (Nat.pair c (Nat.pair d s))) =
      Part.some (encode (checkAgree n c d s)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkAgree_primrec
  exact ⟨machine, fun n c d s => hm (n, c, d, s)⟩

end Alexander313.Carlson.PrimitiveFiniteChecks
