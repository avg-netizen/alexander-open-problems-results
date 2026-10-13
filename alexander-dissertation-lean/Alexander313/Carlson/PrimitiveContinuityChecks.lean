import Alexander313.Carlson.PrimitiveFiniteChecks

/-!
# Primitive-recursive finite continuity and extension checks

All searches in this module run over explicitly stored finite carriers.
The least-point and just-below tests use natural labels, and the two
correctness tests inspect the original Boolean relation tables. A Boolean
selects the relation level (`false` for one and `true` for two); the
original `Lvl` type and all existing codecs are unchanged.

The raw checkers are uniform in the ambient size and reject failed
pattern or point decodes. Their compatibility theorems apply to every
raw natural code, including accepted noncanonical encodings. Patternhood
is neither assumed nor imposed by these structural checks.
-/

namespace Alexander313.Carlson.PrimitiveContinuityChecks

open Encodable Finite PrimitivePatternCode PrimitiveFiniteChecks
open PrimitiveEndpointIso (entry₁ entry₂ entry₁_primrec entry₂_primrec
  entry₁_dataView entry₂_dataView mem_carrierView_iff)

/-- Preserve the original two levels without introducing a new `Lvl` codec. -/
def level (k : Bool) : Lvl := if k then .two else .one

/-- Read the selected original table, retaining its off-carrier entries. -/
def entryLevel (C : Data) (k : Bool) (ij : ℕ × ℕ) : Bool :=
  if k then entry₂ C ij else entry₁ C ij

/-- A bounded least-point test on natural labels. -/
def LeastGEData (S : Finset ℕ) (x p : ℕ) : Prop :=
  p ∈ S ∧ x ≤ p ∧ ∀ q ∈ S, x ≤ q → p ≤ q

instance (S : Finset ℕ) (x p : ℕ) : Decidable (LeastGEData S x p) := by
  unfold LeastGEData
  infer_instance

/-- A bounded test that a new point lies immediately below an old anchor. -/
def JustBelowData (S : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ S ∧ b < a ∧ ∀ q ∈ S, q < a → q < b

instance (S : Finset ℕ) (a b : ℕ) : Decidable (JustBelowData S a b) := by
  unfold JustBelowData
  infer_instance

/-- Correctness at one old label and two labels of the extension. The
required target witness is searched for only in the old carrier. -/
def CorrectAt (C D : Data) (k : Bool) (t : ℕ × ℕ × ℕ) : Prop :=
  (LeastGEData C.1 t.2.1 t.1 ∧ t.1 < t.2.2 ∧
      entryLevel D k (t.2.1, t.2.2) = true) →
    ∃ p' ∈ C.1, LeastGEData C.1 t.2.2 p' ∧ entryLevel C k (t.1, p') = true

instance (C D : Data) (k : Bool) (t : ℕ × ℕ × ℕ) :
    Decidable (CorrectAt C D k t) := by
  unfold CorrectAt
  infer_instance

/-- Each potentially active correctness premise is checked on a finite
product. Membership of the old label is already implied by `LeastGE`. -/
def KCorrectData (C D : Data) (k : Bool) : Prop :=
  ∀ t ∈ C.1 ×ˢ (D.1 ×ˢ D.1), CorrectAt C D k t

instance (C D : Data) (k : Bool) : Decidable (KCorrectData C D k) := by
  unfold KCorrectData
  infer_instance

/-- Every new-carrier label has an old-carrier upper bound. -/
def BoundedData (C D : Data) : Prop :=
  ∀ x ∈ D.1, ∃ p ∈ C.1, x ≤ p

instance (C D : Data) : Decidable (BoundedData C D) := by
  unfold BoundedData
  infer_instance

/-- Substructure, no new maximum, and correctness of both original relations. -/
def ContinuousData (C D : Data) : Prop :=
  SubData C D ∧ BoundedData C D ∧ KCorrectData C D false ∧ KCorrectData C D true

instance (C D : Data) : Decidable (ContinuousData C D) := by
  unfold ContinuousData
  infer_instance

/-- An extension must add at least one point, and every added point must
lie just below the supplied anchor in the old carrier. -/
def ExtensionAtData (C D : Data) (a : ℕ) : Prop :=
  SubData C D ∧ a ∈ C.1 ∧ (∃ x ∈ D.1, x ∉ C.1) ∧
    ∀ x ∈ D.1, x ∉ C.1 → JustBelowData C.1 a x

instance (C D : Data) (a : ℕ) : Decidable (ExtensionAtData C D a) := by
  unfold ExtensionAtData
  infer_instance

variable {σ : Type*} [Primcodable σ]

theorem entryLevel_primrec {C : σ → Data} {k : σ → Bool} {ij : σ → ℕ × ℕ}
    (hC : Primrec C) (hk : Primrec k) (hij : Primrec ij) :
    Primrec (fun s => entryLevel (C s) (k s) (ij s)) :=
  Primrec.ite (Primrec.eq.comp hk (Primrec.const true))
    (entry₂_primrec.comp hC hij) (entry₁_primrec.comp hC hij)

theorem leastGEData_primrec {S : σ → Finset ℕ} {x p : σ → ℕ}
    (hS : Primrec S) (hx : Primrec x) (hp : Primrec p) :
    PrimrecPred (fun s => LeastGEData (S s) (x s) (p s)) := by
  have hmin : PrimrecRel (fun (q : ℕ) s => x s ≤ q → p s ≤ q) :=
    ((Primrec.nat_le.comp (hx.comp Primrec.snd) Primrec.fst).not.or
      (Primrec.nat_le.comp (hp.comp Primrec.snd) Primrec.fst)).of_eq
        fun _ => imp_iff_not_or.symm
  exact ((PrimitiveFiniteData.finset_mem.comp hp hS).and
    ((Primrec.nat_le.comp hx hp).and
      ((PrimitiveFiniteOperations.forall_mem hmin).comp hS Primrec.id))).of_eq
        fun _ => Iff.rfl

theorem justBelowData_primrec {S : σ → Finset ℕ} {a b : σ → ℕ}
    (hS : Primrec S) (ha : Primrec a) (hb : Primrec b) :
    PrimrecPred (fun s => JustBelowData (S s) (a s) (b s)) := by
  have hbelow : PrimrecRel (fun (q : ℕ) s => q < a s → q < b s) :=
    ((Primrec.nat_lt.comp Primrec.fst (ha.comp Primrec.snd)).not.or
      (Primrec.nat_lt.comp Primrec.fst (hb.comp Primrec.snd))).of_eq
        fun _ => imp_iff_not_or.symm
  exact ((PrimitiveFiniteData.finset_mem.comp ha hS).and
    ((Primrec.nat_lt.comp hb ha).and
      ((PrimitiveFiniteOperations.forall_mem hbelow).comp hS Primrec.id))).of_eq
        fun _ => Iff.rfl

theorem correctAt_primrec {C D : σ → Data} {k : σ → Bool}
    {t : σ → ℕ × ℕ × ℕ} (hC : Primrec C) (hD : Primrec D)
    (hk : Primrec k) (ht : Primrec t) :
    PrimrecPred (fun s => CorrectAt (C s) (D s) (k s) (t s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hp : Primrec (fun s => (t s).1) := Primrec.fst.comp ht
  have hx : Primrec (fun s => (t s).2.1) := Primrec.fst.comp (Primrec.snd.comp ht)
  have hy : Primrec (fun s => (t s).2.2) := Primrec.snd.comp (Primrec.snd.comp ht)
  have hpremise : PrimrecPred (fun s => LeastGEData (C s).1 (t s).2.1 (t s).1 ∧
      (t s).1 < (t s).2.2 ∧ entryLevel (D s) (k s) ((t s).2.1, (t s).2.2) = true) :=
    (leastGEData_primrec hU hx hp).and ((Primrec.nat_lt.comp hp hy).and
      (Primrec.eq.comp (entryLevel_primrec hD hk (hx.pair hy)) (Primrec.const true)))
  have hwitness : PrimrecRel (fun (p' : ℕ) s =>
      LeastGEData (C s).1 (t s).2.2 p' ∧ entryLevel (C s) (k s) ((t s).1, p') = true) :=
    (leastGEData_primrec (hU.comp Primrec.snd) (hy.comp Primrec.snd) Primrec.fst).and
      (Primrec.eq.comp (entryLevel_primrec (hC.comp Primrec.snd)
        (hk.comp Primrec.snd) ((hp.comp Primrec.snd).pair Primrec.fst))
        (Primrec.const true))
  exact (hpremise.not.or
    ((PrimitiveFiniteOperations.exists_mem hwitness).comp hU Primrec.id)).of_eq
      fun _ => imp_iff_not_or.symm

theorem kCorrectData_primrec {C D : σ → Data} {k : σ → Bool}
    (hC : Primrec C) (hD : Primrec D) (hk : Primrec k) :
    PrimrecPred (fun s => KCorrectData (C s) (D s) (k s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hV : Primrec (fun s => (D s).1) := Primrec.fst.comp hD
  have hp : PrimrecRel (fun (t : ℕ × ℕ × ℕ) s => CorrectAt (C s) (D s) (k s) t) :=
    correctAt_primrec (hC.comp Primrec.snd) (hD.comp Primrec.snd)
      (hk.comp Primrec.snd) Primrec.fst
  exact ((PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hU
      (PrimitiveFiniteOperations.finset_product.comp hV hV)) Primrec.id).of_eq
        fun _ => Iff.rfl

theorem boundedData_primrec {C D : σ → Data} (hC : Primrec C) (hD : Primrec D) :
    PrimrecPred (fun s => BoundedData (C s) (D s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hp : PrimrecRel (fun (p : ℕ) (q : ℕ × σ) => q.1 ≤ p) :=
    Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hx : PrimrecRel (fun (x : ℕ) s => ∃ p ∈ (C s).1, x ≤ p) :=
    (PrimitiveFiniteOperations.exists_mem hp).comp (hU.comp Primrec.snd) Primrec.id
  exact ((PrimitiveFiniteOperations.forall_mem hx).comp
    (Primrec.fst.comp hD) Primrec.id).of_eq fun _ => Iff.rfl

theorem continuousData_primrec {C D : σ → Data} (hC : Primrec C) (hD : Primrec D) :
    PrimrecPred (fun s => ContinuousData (C s) (D s)) :=
  ((subData_primrec.comp hC hD).and ((boundedData_primrec hC hD).and
    ((kCorrectData_primrec hC hD (Primrec.const false)).and
      (kCorrectData_primrec hC hD (Primrec.const true))))).of_eq fun _ => Iff.rfl

theorem extensionAtData_primrec {C D : σ → Data} {a : σ → ℕ}
    (hC : Primrec C) (hD : Primrec D) (ha : Primrec a) :
    PrimrecPred (fun s => ExtensionAtData (C s) (D s) (a s)) := by
  have hU : Primrec (fun s => (C s).1) := Primrec.fst.comp hC
  have hV : Primrec (fun s => (D s).1) := Primrec.fst.comp hD
  have hnew : PrimrecRel (fun (x : ℕ) s => x ∉ (C s).1) :=
    (PrimitiveFiniteData.finset_mem.comp Primrec.fst (hU.comp Primrec.snd)).not
  have hbelow : PrimrecRel (fun (x : ℕ) s =>
      x ∉ (C s).1 → JustBelowData (C s).1 (a s) x) :=
    (hnew.not.or (justBelowData_primrec (hU.comp Primrec.snd)
      (ha.comp Primrec.snd) Primrec.fst)).of_eq fun _ => imp_iff_not_or.symm
  exact ((subData_primrec.comp hC hD).and
    ((PrimitiveFiniteData.finset_mem.comp ha hU).and
      (((PrimitiveFiniteOperations.exists_mem hnew).comp hV Primrec.id).and
        ((PrimitiveFiniteOperations.forall_mem hbelow).comp hV Primrec.id)))).of_eq
          fun _ => Iff.rfl

@[simp] theorem entryLevel_dataView_iff {n : ℕ} (C : PatternCode n) (k : Bool)
    (i j : Fin n) :
    entryLevel (dataView C) k (i.val, j.val) = true ↔ C.toStr.rel (level k) i j := by
  cases k <;> simp [entryLevel, level, Str.rel]

/-- Finite-label erasure preserves the least-point predicate exactly. -/
theorem leastGEData_carrierView_iff {n : ℕ} (S : Finset (Fin n)) (x p : Fin n) :
    LeastGEData (carrierView S) x.val p.val ↔ Str.LeastGE S x p := by
  constructor
  · rintro ⟨hp, hxp, hmin⟩
    exact ⟨(mem_carrierView S p).mp hp, hxp,
      fun q hq hxq => hmin q.val ((mem_carrierView S q).mpr hq) hxq⟩
  · rintro ⟨hp, hxp, hmin⟩
    refine ⟨(mem_carrierView S p).mpr hp, hxp, ?_⟩
    intro q hq hxq
    obtain ⟨r, hr, rfl⟩ := (mem_carrierView_iff S q).mp hq
    exact hmin r hr hxq

/-- Finite-label erasure preserves every old point below the anchor. -/
theorem justBelowData_carrierView_iff {n : ℕ} (S : Finset (Fin n)) (a b : Fin n) :
    JustBelowData (carrierView S) a.val b.val ↔ Str.JustBelow S a b := by
  constructor
  · rintro ⟨ha, hba, hbelow⟩
    exact ⟨(mem_carrierView S a).mp ha, hba,
      fun q hq hqa => hbelow q.val ((mem_carrierView S q).mpr hq) hqa⟩
  · rintro ⟨ha, hba, hbelow⟩
    refine ⟨(mem_carrierView S a).mpr ha, hba, ?_⟩
    intro q hq hqa
    obtain ⟨r, hr, rfl⟩ := (mem_carrierView_iff S q).mp hq
    exact hbelow r hr hqa

/-- Restricting the universal triple and the existential witness to their
stored carriers loses no instance of the original correctness condition. -/
theorem kCorrectData_dataView_iff {n : ℕ} (C D : PatternCode n) (k : Bool) :
    KCorrectData (dataView C) (dataView D) k ↔
      Str.KCorrect C.toStr D.toStr (level k) := by
  constructor
  · intro h p x y hx hy hp hpy hxy
    have ht : (p.val, x.val, y.val) ∈
        (dataView C).1 ×ˢ ((dataView D).1 ×ˢ (dataView D).1) :=
      Finset.mem_product.mpr ⟨(mem_carrierView C.U p).mpr hp.1,
        Finset.mem_product.mpr ⟨(mem_carrierView D.U x).mpr hx,
          (mem_carrierView D.U y).mpr hy⟩⟩
    obtain ⟨q, hq, hmin, hrel⟩ := h (p.val, x.val, y.val) ht
      ⟨(leastGEData_carrierView_iff C.U x p).mpr hp, hpy,
        (entryLevel_dataView_iff D k x y).mpr hxy⟩
    obtain ⟨p', hp', rfl⟩ := (mem_carrierView_iff C.U q).mp hq
    exact ⟨p', (leastGEData_carrierView_iff C.U y p').mp hmin,
      (entryLevel_dataView_iff C k p p').mp hrel⟩
  · intro h
    rintro ⟨p, x, y⟩ ht ⟨hp, hpy, hxy⟩
    obtain ⟨hpC, hxyD⟩ := Finset.mem_product.mp ht
    obtain ⟨hxD, hyD⟩ := Finset.mem_product.mp hxyD
    obtain ⟨p₀, hp₀, rfl⟩ := (mem_carrierView_iff C.U p).mp hpC
    obtain ⟨x₀, hx₀, rfl⟩ := (mem_carrierView_iff D.U x).mp hxD
    obtain ⟨y₀, hy₀, rfl⟩ := (mem_carrierView_iff D.U y).mp hyD
    obtain ⟨p', hmin, hrel⟩ := h p₀ x₀ y₀ hx₀ hy₀
      ((leastGEData_carrierView_iff C.U x₀ p₀).mp hp) hpy
      ((entryLevel_dataView_iff D k x₀ y₀).mp hxy)
    exact ⟨p'.val, (mem_carrierView C.U p').mpr hmin.1,
      (leastGEData_carrierView_iff C.U y₀ p').mpr hmin,
      (entryLevel_dataView_iff C k p₀ p').mpr hrel⟩

theorem boundedData_dataView_iff {n : ℕ} (C D : PatternCode n) :
    BoundedData (dataView C) (dataView D) ↔
      ∀ x ∈ D.toStr.U, ∃ p ∈ C.toStr.U, x ≤ p := by
  constructor
  · intro h x hx
    obtain ⟨p, hp, hxp⟩ := h x.val ((mem_carrierView D.U x).mpr hx)
    obtain ⟨p₀, hp₀, rfl⟩ := (mem_carrierView_iff C.U p).mp hp
    exact ⟨p₀, hp₀, hxp⟩
  · intro h x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (mem_carrierView_iff D.U x).mp hx
    obtain ⟨p, hp, hxp⟩ := h x₀ hx₀
    exact ⟨p.val, (mem_carrierView C.U p).mpr hp, hxp⟩

theorem continuousData_dataView_iff {n : ℕ} (C D : PatternCode n) :
    ContinuousData (dataView C) (dataView D) ↔ Str.Continuous C.toStr D.toStr := by
  unfold ContinuousData
  rw [subData_dataView_iff, boundedData_dataView_iff,
    kCorrectData_dataView_iff, kCorrectData_dataView_iff]
  rfl

theorem extensionAtData_dataView_iff {n : ℕ} (C D : PatternCode n) (a : Fin n) :
    ExtensionAtData (dataView C) (dataView D) a.val ↔
      Str.ExtensionAt C.toStr D.toStr a := by
  constructor
  · rintro ⟨hsub, ha, hnew, hbelow⟩
    refine ⟨(subData_dataView_iff C D).mp hsub, (mem_carrierView C.U a).mp ha, ?_, ?_⟩
    · obtain ⟨x, hx, hxnot⟩ := hnew
      obtain ⟨x₀, hx₀, rfl⟩ := (mem_carrierView_iff D.U x).mp hx
      exact ⟨x₀, hx₀, fun hm => hxnot ((mem_carrierView C.U x₀).mpr hm)⟩
    · intro x hx hxnot
      exact (justBelowData_carrierView_iff C.U a x).mp
        (hbelow x.val ((mem_carrierView D.U x).mpr hx)
          (fun hm => hxnot ((mem_carrierView C.U x).mp hm)))
  · rintro ⟨hsub, ha, hnew, hbelow⟩
    refine ⟨(subData_dataView_iff C D).mpr hsub, (mem_carrierView C.U a).mpr ha, ?_, ?_⟩
    · obtain ⟨x, hx, hxnot⟩ := hnew
      exact ⟨x.val, (mem_carrierView D.U x).mpr hx,
        fun hm => hxnot ((mem_carrierView C.U x).mp hm)⟩
    · intro x hx hxnot
      obtain ⟨x₀, hx₀, rfl⟩ := (mem_carrierView_iff D.U x).mp hx
      exact (justBelowData_carrierView_iff C.U a x₀).mpr
        (hbelow x₀ hx₀ (fun hm => hxnot ((mem_carrierView C.U x₀).mpr hm)))

@[simp] theorem decide_kCorrectData {n : ℕ} (C D : PatternCode n) (k : Bool) :
    decide (KCorrectData (dataView C) (dataView D) k) = C.checkKCorrect D (level k) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkKCorrect_eq_true]
  exact kCorrectData_dataView_iff C D k

@[simp] theorem decide_continuousData {n : ℕ} (C D : PatternCode n) :
    decide (ContinuousData (dataView C) (dataView D)) = C.checkContinuous D := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkContinuous_eq_true]
  exact continuousData_dataView_iff C D

@[simp] theorem decide_extensionAtData {n : ℕ} (C D : PatternCode n) (a : Fin n) :
    decide (ExtensionAtData (dataView C) (dataView D) a.val) = C.checkExtensionAt D a := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, PatternCode.checkExtensionAt_eq_true]
  exact extensionAtData_dataView_iff C D a

/-- The original checker is primitive recursive for each original level. -/
theorem original_checkKCorrect_primrec (n : ℕ) (k : Lvl) :
    Primrec₂ (fun C D : PatternCode n => C.checkKCorrect D k) := by
  have hb (b : Bool) : Primrec₂ (fun C D : PatternCode n => C.checkKCorrect D (level b)) :=
    (kCorrectData_primrec ((dataView_primrec n).comp Primrec.fst)
      ((dataView_primrec n).comp Primrec.snd) (Primrec.const b)).decide.of_eq
        fun p => decide_kCorrectData p.1 p.2 b
  cases k
  · exact hb false
  · exact hb true

theorem original_checkContinuous_primrec (n : ℕ) :
    Primrec₂ (@PatternCode.checkContinuous n) :=
  (continuousData_primrec ((dataView_primrec n).comp Primrec.fst)
    ((dataView_primrec n).comp Primrec.snd)).decide.of_eq
      fun p => decide_continuousData p.1 p.2

theorem original_checkExtensionAt_primrec (n : ℕ) :
    Primrec (fun p : PatternCode n × PatternCode n × Fin n =>
      p.1.checkExtensionAt p.2.1 p.2.2) := by
  have hval : Primrec (fun a : Fin n => a.val) := Primrec.encode.of_eq fun _ => rfl
  exact (extensionAtData_primrec ((dataView_primrec n).comp Primrec.fst)
    ((dataView_primrec n).comp (Primrec.fst.comp Primrec.snd))
    (hval.comp (Primrec.snd.comp Primrec.snd))).decide.of_eq
      fun p => decide_extensionAtData p.1 p.2.1 p.2.2

/-- Total raw-code correctness checking at either selected original level. -/
def checkKCorrect (k : Bool) (n c d : ℕ) : Bool :=
  match decodeData n c with
  | none => false
  | some C => match decodeData n d with
    | none => false
    | some D => decide (KCorrectData C D k)

/-- Total raw-code continuity checking, including both relation levels. -/
def checkContinuous (n c d : ℕ) : Bool :=
  match decodeData n c with
  | none => false
  | some C => match decodeData n d with
    | none => false
    | some D => decide (ContinuousData C D)

/-- Total raw-code extension checking. The anchor is decoded using the
existing `Fin n` codec, and out-of-range point codes reject. -/
def checkExtensionAt (n c d a : ℕ) : Bool :=
  match decodeData n c with
  | none => false
  | some C => match decodeData n d with
    | none => false
    | some D => match decodeLabel n a with
      | none => false
      | some p => decide (ExtensionAtData C D p)

theorem checkKCorrect_primrec (k : Bool) :
    Primrec (fun p : ℕ × ℕ × ℕ => checkKCorrect k p.1 p.2.1 p.2.2) := by
  have hC : Primrec (fun p : ℕ × ℕ × ℕ => decodeData p.1 p.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hD : Primrec (fun p : ℕ × ℕ × ℕ => decodeData p.1 p.2.2) :=
    decodeData_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have h : Primrec (fun p : ℕ × ℕ × ℕ =>
      (decodeData p.1 p.2.1).bind fun C =>
        (decodeData p.1 p.2.2).map fun D => decide (KCorrectData C D k)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    exact Primrec.option_map (hD.comp Primrec.fst)
      (kCorrectData_primrec (Primrec.snd.comp Primrec.fst) Primrec.snd
        (Primrec.const k)).decide.to₂
  refine (Primrec.option_getD.comp h (Primrec.const false)).of_eq ?_
  intro p
  cases hC : decodeData p.1 p.2.1 <;>
    cases hD : decodeData p.1 p.2.2 <;> simp [checkKCorrect, hC, hD]

/-- The selector itself can vary as an input, with its existing Boolean
encoding and without a `Primcodable Lvl` instance. -/
theorem checkKCorrect_uniform_primrec :
    Primrec (fun p : Bool × ℕ × ℕ × ℕ =>
      checkKCorrect p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hk : Primrec (fun p : Bool × ℕ × ℕ × ℕ => p.1) := Primrec.fst
  refine (Primrec.ite (Primrec.eq.comp hk (Primrec.const true))
    ((checkKCorrect_primrec true).comp Primrec.snd)
    ((checkKCorrect_primrec false).comp Primrec.snd)).of_eq ?_
  rintro ⟨k, n, c, d⟩
  cases k <;> rfl

theorem checkContinuous_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => checkContinuous p.1 p.2.1 p.2.2) := by
  have hC : Primrec (fun p : ℕ × ℕ × ℕ => decodeData p.1 p.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hD : Primrec (fun p : ℕ × ℕ × ℕ => decodeData p.1 p.2.2) :=
    decodeData_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have h : Primrec (fun p : ℕ × ℕ × ℕ =>
      (decodeData p.1 p.2.1).bind fun C =>
        (decodeData p.1 p.2.2).map fun D => decide (ContinuousData C D)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    exact Primrec.option_map (hD.comp Primrec.fst)
      (continuousData_primrec (Primrec.snd.comp Primrec.fst) Primrec.snd).decide.to₂
  refine (Primrec.option_getD.comp h (Primrec.const false)).of_eq ?_
  intro p
  cases hC : decodeData p.1 p.2.1 <;>
    cases hD : decodeData p.1 p.2.2 <;> simp [checkContinuous, hC, hD]

theorem checkExtensionAt_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ => checkExtensionAt p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hC : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => decodeData p.1 p.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hD : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => decodeData p.1 p.2.2.1) :=
    decodeData_primrec.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => decodeLabel p.1 p.2.2.2) :=
    decodeLabel_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h : Primrec (fun p : ℕ × ℕ × ℕ × ℕ =>
      (decodeData p.1 p.2.1).bind fun C =>
        (decodeData p.1 p.2.2.1).bind fun D =>
          (decodeLabel p.1 p.2.2.2).map fun a => decide (ExtensionAtData C D a)) := by
    refine Primrec.option_bind hC ?_
    apply Primrec₂.mk
    refine Primrec.option_bind (hD.comp Primrec.fst) ?_
    apply Primrec₂.mk
    exact Primrec.option_map (ha.comp (Primrec.fst.comp Primrec.fst))
      (extensionAtData_primrec (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd).decide.to₂
  refine (Primrec.option_getD.comp h (Primrec.const false)).of_eq ?_
  intro p
  cases hC : decodeData p.1 p.2.1 <;>
    cases hD : decodeData p.1 p.2.2.1 <;>
    cases ha : decodeLabel p.1 p.2.2.2 <;> simp [checkExtensionAt, hC, hD, ha]

/-- All-input compatibility with the original pattern decoders and checker. -/
theorem checkKCorrect_eq (k : Bool) (n c d : ℕ) : checkKCorrect k n c d =
    match decode (α := PatternCode n) c, decode (α := PatternCode n) d with
    | some C, some D => C.checkKCorrect D (level k)
    | _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    simp [checkKCorrect, decodeData_eq, hC, hD]

theorem checkContinuous_eq (n c d : ℕ) : checkContinuous n c d =
    match decode (α := PatternCode n) c, decode (α := PatternCode n) d with
    | some C, some D => C.checkContinuous D
    | _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    simp [checkContinuous, decodeData_eq, hC, hD]

theorem checkExtensionAt_eq (n c d a : ℕ) : checkExtensionAt n c d a =
    match decode (α := PatternCode n) c, decode (α := PatternCode n) d,
        decode (α := Fin n) a with
    | some C, some D, some p => C.checkExtensionAt D p
    | _, _, _ => false := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases ha : decode (α := Fin n) a <;>
    simp [checkExtensionAt, decodeData_eq, decodeLabel_eq, hC, hD, ha]

@[simp] theorem checkKCorrect_encode {n : ℕ} (k : Bool) (C D : PatternCode n) :
    checkKCorrect k n (encode C) (encode D) = C.checkKCorrect D (level k) := by
  rw [checkKCorrect_eq, Encodable.encodek, Encodable.encodek]

@[simp] theorem checkContinuous_encode {n : ℕ} (C D : PatternCode n) :
    checkContinuous n (encode C) (encode D) = C.checkContinuous D := by
  rw [checkContinuous_eq, Encodable.encodek, Encodable.encodek]

@[simp] theorem checkExtensionAt_encode {n : ℕ} (C D : PatternCode n) (a : Fin n) :
    checkExtensionAt n (encode C) (encode D) (encode a) = C.checkExtensionAt D a := by
  rw [checkExtensionAt_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek]

/-- Exact positive acceptance semantics, without a canonical-code precondition. -/
theorem checkKCorrect_eq_true (k : Bool) (n c d : ℕ) : checkKCorrect k n c d = true ↔
    ∃ C D : PatternCode n, decode c = some C ∧ decode d = some D ∧
      Str.KCorrect C.toStr D.toStr (level k) := by
  rw [checkKCorrect_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    simp [PatternCode.checkKCorrect_eq_true]

theorem checkContinuous_eq_true (n c d : ℕ) : checkContinuous n c d = true ↔
    ∃ C D : PatternCode n, decode c = some C ∧ decode d = some D ∧
      Str.Continuous C.toStr D.toStr := by
  rw [checkContinuous_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    simp [PatternCode.checkContinuous_eq_true]

theorem checkExtensionAt_eq_true (n c d a : ℕ) : checkExtensionAt n c d a = true ↔
    ∃ (C D : PatternCode n) (p : Fin n),
      decode c = some C ∧ decode d = some D ∧ decode a = some p ∧
        Str.ExtensionAt C.toStr D.toStr p := by
  rw [checkExtensionAt_eq]
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases ha : decode (α := Fin n) a <;>
    simp [PatternCode.checkExtensionAt_eq_true]

/-- For either relation level, one total machine handles every natural
size and both raw pattern codes. -/
theorem checkKCorrect_program (k : Bool) : ∃ machine : Nat.Partrec.Code, ∀ n c d : ℕ,
    machine.eval (Nat.pair n (Nat.pair c d)) =
      Part.some (encode (checkKCorrect k n c d)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program (checkKCorrect_primrec k)
  exact ⟨machine, fun n c d => hm (n, c, d)⟩

/-- One machine handles both Boolean relation selectors and all sizes. -/
theorem checkKCorrect_uniform_program : ∃ machine : Nat.Partrec.Code,
    ∀ (k : Bool) (n c d : ℕ),
      machine.eval (Nat.pair (encode k) (Nat.pair n (Nat.pair c d))) =
        Part.some (encode (checkKCorrect k n c d)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkKCorrect_uniform_primrec
  exact ⟨machine, fun k n c d => hm (k, n, c, d)⟩

theorem checkContinuous_program : ∃ machine : Nat.Partrec.Code, ∀ n c d : ℕ,
    machine.eval (Nat.pair n (Nat.pair c d)) = Part.some (encode (checkContinuous n c d)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkContinuous_primrec
  exact ⟨machine, fun n c d => hm (n, c, d)⟩

theorem checkExtensionAt_program : ∃ machine : Nat.Partrec.Code, ∀ n c d a : ℕ,
    machine.eval (Nat.pair n (Nat.pair c (Nat.pair d a))) =
      Part.some (encode (checkExtensionAt n c d a)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program checkExtensionAt_primrec
  exact ⟨machine, fun n c d a => hm (n, c, d, a)⟩

end Alexander313.Carlson.PrimitiveContinuityChecks
