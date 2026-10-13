import Alexander313.Carlson.PrimitiveFiniteChecks

/-!
# Uniform primitive-recursive finite patternhood

Each of the eight fields of `Str.IsPattern` is checked over the natural
carrier of the lossless `PrimitivePatternCode.Data` view. Only carrier
points, pairs and triples are quantified over. The complete relation tables
remain stored unchanged, including entries outside the carrier.

The raw checker uses the existing decoder, uniformly in the supplied label
bound, and rejects every failed decode. Its specification covers all natural
inputs, including accepted noncanonical encodings. The final theorem supplies
one `Nat.Partrec.Code` for this total checker. Reflection, minimality and the
finite derivation checkers remain separate obligations.
-/

namespace Alexander313.Carlson.PrimitivePatternChecks

open Encodable Finite PrimitivePatternCode
open PrimitiveEndpointIso (entry₁ entry₂ entry₁_primrec entry₂_primrec
  entry₁_dataView entry₂_dataView mem_carrierView_iff)

/-- The first relation is contained in the ambient order on the carrier. -/
def Le₁Data (d : Data) : Prop :=
  ∀ ij ∈ d.1 ×ˢ d.1, entry₁ d ij = true → ij.1 ≤ ij.2

/-- The second relation is contained in the first on the carrier. -/
def Sub₂Data (d : Data) : Prop :=
  ∀ ij ∈ d.1 ×ˢ d.1, entry₂ d ij = true → entry₁ d ij = true

def Refl₁Data (d : Data) : Prop := ∀ i ∈ d.1, entry₁ d (i, i) = true

def Refl₂Data (d : Data) : Prop := ∀ i ∈ d.1, entry₂ d (i, i) = true

def Trans₁Data (d : Data) : Prop :=
  ∀ ijk ∈ d.1 ×ˢ (d.1 ×ˢ d.1),
    entry₁ d (ijk.1, ijk.2.1) = true →
    entry₁ d (ijk.2.1, ijk.2.2) = true → entry₁ d (ijk.1, ijk.2.2) = true

def Trans₂Data (d : Data) : Prop :=
  ∀ ijk ∈ d.1 ×ˢ (d.1 ×ˢ d.1),
    entry₂ d (ijk.1, ijk.2.1) = true →
    entry₂ d (ijk.2.1, ijk.2.2) = true → entry₂ d (ijk.1, ijk.2.2) = true

def Convex₁Data (d : Data) : Prop :=
  ∀ ijk ∈ d.1 ×ˢ (d.1 ×ˢ d.1), ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
    entry₁ d (ijk.1, ijk.2.2) = true → entry₁ d (ijk.1, ijk.2.1) = true

def Respect₂Data (d : Data) : Prop :=
  ∀ ijk ∈ d.1 ×ˢ (d.1 ×ˢ d.1), ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
    entry₂ d (ijk.1, ijk.2.2) = true → entry₁ d (ijk.2.1, ijk.2.2) = true →
      entry₂ d (ijk.1, ijk.2.1) = true

/-- All eight original pattern conditions, with their original order. -/
def PatternData (d : Data) : Prop :=
  Le₁Data d ∧ Sub₂Data d ∧ Refl₁Data d ∧ Refl₂Data d ∧
    Trans₁Data d ∧ Trans₂Data d ∧ Convex₁Data d ∧ Respect₂Data d

instance (d : Data) : Decidable (Le₁Data d) := by unfold Le₁Data; infer_instance
instance (d : Data) : Decidable (Sub₂Data d) := by unfold Sub₂Data; infer_instance
instance (d : Data) : Decidable (Refl₁Data d) := by unfold Refl₁Data; infer_instance
instance (d : Data) : Decidable (Refl₂Data d) := by unfold Refl₂Data; infer_instance
instance (d : Data) : Decidable (Trans₁Data d) := by unfold Trans₁Data; infer_instance
instance (d : Data) : Decidable (Trans₂Data d) := by unfold Trans₂Data; infer_instance
instance (d : Data) : Decidable (Convex₁Data d) := by unfold Convex₁Data; infer_instance
instance (d : Data) : Decidable (Respect₂Data d) := by unfold Respect₂Data; infer_instance
instance (d : Data) : Decidable (PatternData d) := by unfold PatternData; infer_instance

variable {σ : Type*} [Primcodable σ]

private theorem imp_primrec {p q : σ → Prop} (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred (fun s => p s → q s) :=
  (hp.not.or hq).of_eq fun _ => imp_iff_not_or.symm

private theorem edge₁_primrec {d : σ → Data} {i j : σ → ℕ}
    (hd : Primrec d) (hi : Primrec i) (hj : Primrec j) :
    PrimrecPred (fun s => entry₁ (d s) (i s, j s) = true) :=
  Primrec.eq.comp (entry₁_primrec.comp hd (hi.pair hj)) (Primrec.const true)

private theorem edge₂_primrec {d : σ → Data} {i j : σ → ℕ}
    (hd : Primrec d) (hi : Primrec i) (hj : Primrec j) :
    PrimrecPred (fun s => entry₂ (d s) (i s, j s) = true) :=
  Primrec.eq.comp (entry₂_primrec.comp hd (hi.pair hj)) (Primrec.const true)

private theorem forall_points_primrec {p : ℕ → Data → Prop} (hp : PrimrecRel p) :
    PrimrecPred (fun d : Data => ∀ i ∈ d.1, p i d) :=
  (PrimitiveFiniteOperations.forall_mem hp).comp
    (Primrec.fst : Primrec (fun d : Data => d.1)) Primrec.id

private theorem forall_pairs_primrec {p : (ℕ × ℕ) → Data → Prop}
    (hp : PrimrecRel p) :
    PrimrecPred (fun d : Data => ∀ ij ∈ d.1 ×ˢ d.1, p ij d) := by
  have hU : Primrec (fun d : Data => d.1) := Primrec.fst
  exact (PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id

private theorem forall_triples_primrec {p : (ℕ × ℕ × ℕ) → Data → Prop}
    (hp : PrimrecRel p) :
    PrimrecPred (fun d : Data => ∀ ijk ∈ d.1 ×ˢ (d.1 ×ˢ d.1), p ijk d) := by
  have hU : Primrec (fun d : Data => d.1) := Primrec.fst
  have hUU : Primrec (fun d : Data => d.1 ×ˢ d.1) :=
    PrimitiveFiniteOperations.finset_product.comp hU hU
  exact (PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hU hUU) Primrec.id

theorem le₁Data_primrec : PrimrecPred Le₁Data := by
  have hd : Primrec (fun p : (ℕ × ℕ) × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℕ × ℕ) × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ) × Data => p.1.2) := Primrec.snd.comp Primrec.fst
  have hp : PrimrecRel (fun (ij : ℕ × ℕ) (d : Data) =>
      entry₁ d ij = true → ij.1 ≤ ij.2) :=
    (imp_primrec (edge₁_primrec hd hi hj) (Primrec.nat_le.comp hi hj)).of_eq
      fun _ => Iff.rfl
  exact (forall_pairs_primrec hp).of_eq fun _ => Iff.rfl

theorem sub₂Data_primrec : PrimrecPred Sub₂Data := by
  have hd : Primrec (fun p : (ℕ × ℕ) × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℕ × ℕ) × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ) × Data => p.1.2) := Primrec.snd.comp Primrec.fst
  have hp : PrimrecRel (fun (ij : ℕ × ℕ) (d : Data) =>
      entry₂ d ij = true → entry₁ d ij = true) :=
    (imp_primrec (edge₂_primrec hd hi hj) (edge₁_primrec hd hi hj)).of_eq
      fun _ => Iff.rfl
  exact (forall_pairs_primrec hp).of_eq fun _ => Iff.rfl

theorem refl₁Data_primrec : PrimrecPred Refl₁Data := by
  have hd : Primrec (fun p : ℕ × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : ℕ × Data => p.1) := Primrec.fst
  have hp : PrimrecRel (fun (i : ℕ) (d : Data) => entry₁ d (i, i) = true) :=
    edge₁_primrec hd hi hi
  exact (forall_points_primrec hp).of_eq fun _ => Iff.rfl

theorem refl₂Data_primrec : PrimrecPred Refl₂Data := by
  have hd : Primrec (fun p : ℕ × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : ℕ × Data => p.1) := Primrec.fst
  have hp : PrimrecRel (fun (i : ℕ) (d : Data) => entry₂ d (i, i) = true) :=
    edge₂_primrec hd hi hi
  exact (forall_points_primrec hp).of_eq fun _ => Iff.rfl

theorem trans₁Data_primrec : PrimrecPred Trans₁Data := by
  have hd : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℕ × ℕ × ℕ) (d : Data) =>
      entry₁ d (ijk.1, ijk.2.1) = true →
        entry₁ d (ijk.2.1, ijk.2.2) = true → entry₁ d (ijk.1, ijk.2.2) = true) :=
    imp_primrec (edge₁_primrec hd hi hj)
      (imp_primrec (edge₁_primrec hd hj hk) (edge₁_primrec hd hi hk))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

theorem trans₂Data_primrec : PrimrecPred Trans₂Data := by
  have hd : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℕ × ℕ × ℕ) (d : Data) =>
      entry₂ d (ijk.1, ijk.2.1) = true →
        entry₂ d (ijk.2.1, ijk.2.2) = true → entry₂ d (ijk.1, ijk.2.2) = true) :=
    imp_primrec (edge₂_primrec hd hi hj)
      (imp_primrec (edge₂_primrec hd hj hk) (edge₂_primrec hd hi hk))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

theorem convex₁Data_primrec : PrimrecPred Convex₁Data := by
  have hd : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℕ × ℕ × ℕ) (d : Data) =>
      ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
        entry₁ d (ijk.1, ijk.2.2) = true → entry₁ d (ijk.1, ijk.2.1) = true) :=
    imp_primrec (Primrec.nat_le.comp hi hj)
      (imp_primrec (Primrec.nat_le.comp hj hk)
        (imp_primrec (edge₁_primrec hd hi hk) (edge₁_primrec hd hi hj)))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

theorem respect₂Data_primrec : PrimrecPred Respect₂Data := by
  have hd : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℕ × ℕ × ℕ) × Data => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℕ × ℕ × ℕ) (d : Data) =>
      ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
        entry₂ d (ijk.1, ijk.2.2) = true → entry₁ d (ijk.2.1, ijk.2.2) = true →
          entry₂ d (ijk.1, ijk.2.1) = true) :=
    imp_primrec (Primrec.nat_le.comp hi hj)
      (imp_primrec (Primrec.nat_le.comp hj hk)
        (imp_primrec (edge₂_primrec hd hi hk)
          (imp_primrec (edge₁_primrec hd hj hk) (edge₂_primrec hd hi hj))))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

/-- A primitive-recursive certificate for every one of the eight fields. -/
theorem patternData_primrec : PrimrecPred PatternData :=
  (le₁Data_primrec.and (sub₂Data_primrec.and (refl₁Data_primrec.and
    (refl₂Data_primrec.and (trans₁Data_primrec.and (trans₂Data_primrec.and
      (convex₁Data_primrec.and respect₂Data_primrec))))))).of_eq fun _ => Iff.rfl

private theorem forall_carrierView_iff {n : ℕ} (U : Finset (Fin n)) (p : ℕ → Prop) :
    (∀ i ∈ carrierView U, p i) ↔ ∀ x ∈ U, p x.val := by
  constructor
  · intro h x hx
    exact h x.val ((mem_carrierView U x).mpr hx)
  · intro h i hi
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff U i).mp hi
    exact h x hx

private theorem forall_pairs_carrierView_iff {n : ℕ} (U : Finset (Fin n))
    (p : (ℕ × ℕ) → Prop) :
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

private theorem forall_triples_carrierView_iff {n : ℕ} (U : Finset (Fin n))
    (p : (ℕ × ℕ × ℕ) → Prop) :
    (∀ ijk ∈ carrierView U ×ˢ (carrierView U ×ˢ carrierView U), p ijk) ↔
      ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, p (x.val, y.val, z.val) := by
  constructor
  · intro h x hx y hy z hz
    exact h (x.val, y.val, z.val) (Finset.mem_product.mpr
      ⟨(mem_carrierView U x).mpr hx, Finset.mem_product.mpr
        ⟨(mem_carrierView U y).mpr hy, (mem_carrierView U z).mpr hz⟩⟩)
  · intro h
    rintro ⟨i, j, k⟩ hijk
    obtain ⟨hi, hjk⟩ := Finset.mem_product.mp hijk
    obtain ⟨hj, hk⟩ := Finset.mem_product.mp hjk
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff U i).mp hi
    obtain ⟨y, hy, rfl⟩ := (mem_carrierView_iff U j).mp hj
    obtain ⟨z, hz, rfl⟩ := (mem_carrierView_iff U k).mp hk
    exact h x hx y hy z hz

/-- The natural-data predicate has exactly the original pattern semantics.
No assumption about entries outside the carrier is needed. -/
theorem patternData_dataView_iff {n : ℕ} (C : PatternCode n) :
    PatternData (dataView C) ↔ C.toStr.IsPattern := by
  rw [Str.isPattern_iff_conditions]
  simp only [PatternData, Le₁Data, Sub₂Data, Refl₁Data, Refl₂Data,
    Trans₁Data, Trans₂Data, Convex₁Data, Respect₂Data,
    show (dataView C).1 = carrierView C.U from rfl,
    forall_carrierView_iff, forall_pairs_carrierView_iff,
    forall_triples_carrierView_iff, entry₁_dataView, entry₂_dataView,
    PatternCode.toStr_U, PatternCode.toStr_r₁, PatternCode.toStr_r₂, Fin.le_def]

@[simp] theorem decide_patternData {n : ℕ} (C : PatternCode n) :
    decide (PatternData (dataView C)) = C.checkPattern := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkPattern_eq_true]
  exact patternData_dataView_iff C

/-- The certificate also applies to the unchanged original fixed-size checker. -/
theorem original_checkPattern_primrec (n : ℕ) : Primrec (@PatternCode.checkPattern n) :=
  (patternData_primrec.decide.comp (PrimitiveFiniteChecks.dataView_primrec n)).of_eq
    fun C => decide_patternData C

/-- A total raw-code checker; failed pattern-record decoding rejects. -/
def checkPattern (n code : ℕ) : Bool :=
  match decodeData n code with
  | none => false
  | some d => decide (PatternData d)

/-- One primitive-recursive algorithm accepts the label bound as an input. -/
theorem checkPattern_primrec : Primrec₂ checkPattern := by
  have h : Primrec (fun p : ℕ × ℕ =>
      (decodeData p.1 p.2).map fun d => decide (PatternData d)) :=
    Primrec.option_map decodeData_primrec
      (patternData_primrec.decide.comp Primrec.snd).to₂
  apply Primrec₂.mk
  refine (Primrec.option_getD.comp h (Primrec.const false)).of_eq ?_
  intro p
  cases hd : decodeData p.1 p.2 <;> simp [checkPattern, hd]

/-- All-input compatibility with the original decoder and Boolean checker. -/
theorem checkPattern_eq (n code : ℕ) : checkPattern n code =
    match decode (α := PatternCode n) code with
    | none => false
    | some C => C.checkPattern := by
  cases hC : decode (α := PatternCode n) code <;>
    simp [checkPattern, decodeData_eq, hC]

@[simp] theorem checkPattern_encode {n : ℕ} (C : PatternCode n) :
    checkPattern n (encode C) = C.checkPattern := by
  rw [checkPattern_eq, Encodable.encodek]

/-- Failed decoding rejects independently of the failure's component. -/
theorem checkPattern_of_decode_none {n code : ℕ}
    (h : decode (α := PatternCode n) code = none) : checkPattern n code = false := by
  rw [checkPattern_eq, h]

/-- Exact acceptance semantics on arbitrary raw natural inputs. -/
theorem checkPattern_eq_true (n code : ℕ) : checkPattern n code = true ↔
    ∃ C : PatternCode n, decode code = some C ∧ C.toStr.IsPattern := by
  rw [checkPattern_eq]
  cases hC : decode (α := PatternCode n) code <;>
    simp [PatternCode.checkPattern_eq_true]

/-- A single total machine implements patternhood at every finite size,
using the existing encodings for both input numbers and its Boolean result. -/
theorem checkPattern_program : ∃ machine : Nat.Partrec.Code, ∀ n code : ℕ,
    machine.eval (Nat.pair n code) = Part.some (encode (checkPattern n code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkPattern_primrec
  exact ⟨machine, fun n code => hm (n, code)⟩

end Alexander313.Carlson.PrimitivePatternChecks
