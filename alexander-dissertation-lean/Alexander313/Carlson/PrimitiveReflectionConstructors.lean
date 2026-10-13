import Alexander313.Carlson.PrimitiveReflectionChecks

/-!
# Uniform primitive-recursive reflection constructors

These algorithms construct the actual downward and upward relation tables,
including every entry outside the carrier. The label bound is an input.
Compatibility requires only successful original decodes, with no patternhood
or reflection-hypothesis assumption. The raw outputs use the original
`PatternCode` encoder and reject malformed fields.
-/

namespace Alexander313.Carlson.PrimitiveReflectionConstructors

open Encodable Finite PrimitivePatternCode PrimitiveContinuityChecks
open PrimitiveEmbeddingChecks PrimitiveReflectionChecks
open PrimitiveEndpointIso (entry₁ entry₂ entry₁_primrec entry₂_primrec
  entry₁_dataView entry₂_dataView)

/-- A complete square table, without filtering its carrier. -/
def tabulate (n : ℕ) (r : ℕ × ℕ → Bool) : List (List Bool) :=
  (List.range n).map fun i => (List.range n).map fun j => r (i, j)

theorem tabulate_eq (n : ℕ) (r : ℕ × ℕ → Bool) :
    tabulate n r = List.ofFn (fun i : Fin n =>
      List.ofFn (fun j : Fin n => r (i.val, j.val))) := by
  apply List.ext_getElem
  · simp [tabulate]
  · intro i hi hi'
    simp only [tabulate, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp

variable {σ : Type*} [Primcodable σ]

theorem tabulate_primrec {n : σ → ℕ} {r : σ → ℕ × ℕ → Bool}
    (hn : Primrec n) (hr : Primrec₂ r) :
    Primrec (fun s => tabulate (n s) (r s)) := by
  unfold tabulate
  refine Primrec.list_map (Primrec.list_range.comp hn) ?_
  apply Primrec₂.mk
  refine Primrec.list_map (Primrec.list_range.comp (hn.comp Primrec.fst)) ?_
  exact (hr.comp (Primrec.fst.comp Primrec.fst)
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂

/-- The executable back map with erased finite-label bounds. -/
def back (N : Finset ℕ) (F : List ℕ) (x : ℕ) : ℕ :=
  if x ∈ N then mapAt F x else x

theorem back_primrec {N : σ → Finset ℕ} {F : σ → List ℕ} {x : σ → ℕ}
    (hN : Primrec N) (hF : Primrec F) (hx : Primrec x) :
    Primrec (fun s => back (N s) (F s) (x s)) :=
  Primrec.ite (PrimitiveFiniteData.finset_mem.comp hx hN)
    (mapAt_primrec.comp hF hx) hx

@[simp] theorem back_view {n : ℕ} (N : Finset (Fin n)) (g : Fin n → Fin n)
    (x : Fin n) : back (carrierView N) (mapView g) x.val = (finiteBack N g x).val := by
  by_cases hx : x ∈ N <;> simp [back, finiteBack, hx]

/-- The old-old or copied-low clause shared by the downward tables. -/
def downCore (C : Data) (l : Bool) (a : ℕ) (N : Finset ℕ) (F : List ℕ)
    (ij : ℕ × ℕ) : Prop :=
  (ij.1 ∈ C.1 ∧ ij.2 ∈ C.1 ∧ entryLevel C l ij = true) ∨
  ((ij.1 ∈ N ∨ ij.2 ∈ N) ∧ (ij.1 ∈ N ∨ ij.1 < a) ∧
    (ij.2 ∈ N ∨ ij.2 < a) ∧
      entryLevel C l (back N F ij.1, back N F ij.2) = true)

instance (C : Data) (l : Bool) (a : ℕ) (N : Finset ℕ) (F : List ℕ)
    (ij : ℕ × ℕ) : Decidable (downCore C l a N F ij) := by
  unfold downCore
  infer_instance

theorem downCore_primrec {C : σ → Data} {l : σ → Bool} {a : σ → ℕ}
    {N : σ → Finset ℕ} {F : σ → List ℕ} {ij : σ → ℕ × ℕ}
    (hC : Primrec C) (hl : Primrec l) (ha : Primrec a) (hN : Primrec N)
    (hF : Primrec F) (hij : Primrec ij) :
    PrimrecPred (fun s => downCore (C s) (l s) (a s) (N s) (F s) (ij s)) := by
  have hu := Primrec.fst.comp hij
  have hv := Primrec.snd.comp hij
  have hU := Primrec.fst.comp hC
  have huN := PrimitiveFiniteData.finset_mem.comp hu hN
  have hvN := PrimitiveFiniteData.finset_mem.comp hv hN
  exact (((PrimitiveFiniteData.finset_mem.comp hu hU).and
    ((PrimitiveFiniteData.finset_mem.comp hv hU).and
      (Primrec.eq.comp (entryLevel_primrec hC hl hij) (Primrec.const true)))).or
    ((huN.or hvN).and ((huN.or (Primrec.nat_lt.comp hu ha)).and
      ((hvN.or (Primrec.nat_lt.comp hv ha)).and
        (Primrec.eq.comp (entryLevel_primrec hC hl
          ((back_primrec hN hF hu).pair (back_primrec hN hF hv)))
            (Primrec.const true)))))).of_eq fun _ => Iff.rfl

/-- The additional first-relation bridge at the second reflection level. -/
def downBridge (C : Data) (k : Bool) (a b : ℕ) (N : Finset ℕ) (F : List ℕ)
    (ij : ℕ × ℕ) : Prop :=
  k = true ∧ ij.1 ∈ N ∧ ij.2 ∈ C.1 ∧ a ≤ ij.2 ∧
    entry₁ C (mapAt F ij.1, b) = true ∧ entry₁ C (a, ij.2) = true

instance (C : Data) (k : Bool) (a b : ℕ) (N : Finset ℕ) (F : List ℕ)
    (ij : ℕ × ℕ) : Decidable (downBridge C k a b N F ij) := by
  unfold downBridge
  infer_instance

theorem downBridge_primrec {C : σ → Data} {k : σ → Bool} {a b : σ → ℕ}
    {N : σ → Finset ℕ} {F : σ → List ℕ} {ij : σ → ℕ × ℕ}
    (hC : Primrec C) (hk : Primrec k) (ha : Primrec a) (hb : Primrec b)
    (hN : Primrec N) (hF : Primrec F) (hij : Primrec ij) :
    PrimrecPred (fun s => downBridge (C s) (k s) (a s) (b s) (N s) (F s) (ij s)) := by
  have hu := Primrec.fst.comp hij
  have hv := Primrec.snd.comp hij
  exact ((Primrec.eq.comp hk (Primrec.const true)).and
    ((PrimitiveFiniteData.finset_mem.comp hu hN).and
    ((PrimitiveFiniteData.finset_mem.comp hv (Primrec.fst.comp hC)).and
    ((Primrec.nat_le.comp ha hv).and
    ((Primrec.eq.comp (entry₁_primrec.comp hC
      ((mapAt_primrec.comp hF hu).pair hb)) (Primrec.const true)).and
      (Primrec.eq.comp (entry₁_primrec.comp hC (ha.pair hv))
        (Primrec.const true))))))).of_eq fun _ => Iff.rfl

def downwardData (n : ℕ) (C : Data) (k : Bool) (a b : ℕ)
    (N : Finset ℕ) (F : List ℕ) : Data :=
  (C.1 ∪ N,
    tabulate n (fun ij => decide (downCore C false a N F ij ∨ downBridge C k a b N F ij)),
    tabulate n (fun ij => decide (downCore C true a N F ij)))

theorem downwardData_primrec {n : σ → ℕ} {C : σ → Data} {k : σ → Bool}
    {a b : σ → ℕ} {N : σ → Finset ℕ} {F : σ → List ℕ}
    (hn : Primrec n) (hC : Primrec C) (hk : Primrec k) (ha : Primrec a)
    (hb : Primrec b) (hN : Primrec N) (hF : Primrec F) :
    Primrec (fun s => downwardData (n s) (C s) (k s) (a s) (b s) (N s) (F s)) := by
  have hcore (l : Bool) : PrimrecRel (fun s ij => downCore (C s) l (a s) (N s) (F s) ij) :=
    (downCore_primrec (hC.comp Primrec.fst) (Primrec.const l) (ha.comp Primrec.fst)
      (hN.comp Primrec.fst) (hF.comp Primrec.fst) Primrec.snd)
  have hbridge : PrimrecRel (fun s ij => downBridge (C s) (k s) (a s) (b s) (N s) (F s) ij) :=
    (downBridge_primrec (hC.comp Primrec.fst) (hk.comp Primrec.fst) (ha.comp Primrec.fst)
      (hb.comp Primrec.fst) (hN.comp Primrec.fst) (hF.comp Primrec.fst) Primrec.snd)
  exact (PrimitiveFiniteOperations.finset_union.comp (Primrec.fst.comp hC) hN).pair
    ((tabulate_primrec hn ((hcore false).or hbridge).decide.to₂).pair
      (tabulate_primrec hn (hcore true).decide.to₂))

/-- Exact downward tables, without assuming the reflection hypotheses. -/
theorem downwardData_view {n : ℕ} (C : PatternCode n) (k : Bool) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    downwardData n (dataView C) k a.val b.val (carrierView N) (mapView g) =
      dataView (C.downward (level k) a b N g) := by
  apply Prod.ext
  · exact (Finset.map_union C.U N).symm
  · apply Prod.ext
    · dsimp only [downwardData, dataView]
      rw [tabulate_eq]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      cases k <;> simp [downCore, downBridge, entryLevel, level, -Fin.val_fin_lt, -Fin.val_fin_le,
        PrimitiveEndpointIso.entry₁, relation₁,
        PatternCode.downward, Fin.lt_def, Fin.le_def, or_assoc]
    · dsimp only [downwardData, dataView]
      rw [tabulate_eq]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      simp [downCore, entryLevel, PrimitiveEndpointIso.entry₂, relation₂,
        PatternCode.downward, Fin.lt_def, -Fin.val_fin_lt]

/-- Old edges, the new cross clause, and copied edges of an upward table. -/
def upCell (C D : Data) (l : Bool) (a b : ℕ) (N : Finset ℕ) (F : List ℕ)
    (ij : ℕ × ℕ) : Prop :=
  (ij.1 ∈ C.1 ∧ ij.2 ∈ C.1 ∧ entryLevel C l ij = true) ∨
  (ij.1 ∈ C.1 ∧ ij.2 ∈ N ∧
    (if l then ij.1 < a ∧ entry₂ D (ij.1, mapAt F ij.2) = true
      else ij.1 < b ∧ entry₁ C (ij.1, b) = true)) ∨
  (ij.1 ∈ N ∧ ij.2 ∈ N ∧ entryLevel D l (mapAt F ij.1, mapAt F ij.2) = true)

instance (C D : Data) (l : Bool) (a b : ℕ) (N : Finset ℕ) (F : List ℕ)
    (ij : ℕ × ℕ) : Decidable (upCell C D l a b N F ij) := by
  unfold upCell
  infer_instance

theorem upCell_primrec {C D : σ → Data} {l : σ → Bool} {a b : σ → ℕ}
    {N : σ → Finset ℕ} {F : σ → List ℕ} {ij : σ → ℕ × ℕ}
    (hC : Primrec C) (hD : Primrec D) (hl : Primrec l) (ha : Primrec a)
    (hb : Primrec b) (hN : Primrec N) (hF : Primrec F) (hij : Primrec ij) :
    PrimrecPred (fun s => upCell (C s) (D s) (l s) (a s) (b s) (N s) (F s) (ij s)) := by
  have hu := Primrec.fst.comp hij
  have hv := Primrec.snd.comp hij
  have huP := PrimitiveFiniteData.finset_mem.comp hu (Primrec.fst.comp hC)
  have hvP := PrimitiveFiniteData.finset_mem.comp hv (Primrec.fst.comp hC)
  have huN := PrimitiveFiniteData.finset_mem.comp hu hN
  have hvN := PrimitiveFiniteData.finset_mem.comp hv hN
  have hgu := mapAt_primrec.comp hF hu
  have hgv := mapAt_primrec.comp hF hv
  have hcross : PrimrecPred (fun s => if l s then
      (ij s).1 < a s ∧ entry₂ (D s) ((ij s).1, mapAt (F s) (ij s).2) = true
      else (ij s).1 < b s ∧ entry₁ (C s) ((ij s).1, b s) = true) := by
    apply Primrec.primrecPred
    exact (Primrec.ite (Primrec.eq.comp hl (Primrec.const true))
      ((Primrec.nat_lt.comp hu ha).and
        (Primrec.eq.comp (entry₂_primrec.comp hD (hu.pair hgv)) (Primrec.const true))).decide
      ((Primrec.nat_lt.comp hu hb).and
        (Primrec.eq.comp (entry₁_primrec.comp hC (hu.pair hb))
          (Primrec.const true))).decide).of_eq fun s => by cases l s <;> simp
  exact ((huP.and (hvP.and
    (Primrec.eq.comp (entryLevel_primrec hC hl hij) (Primrec.const true)))).or
    ((huP.and (hvN.and hcross)).or
      (huN.and (hvN.and (Primrec.eq.comp (entryLevel_primrec hD hl (hgu.pair hgv))
        (Primrec.const true)))))).of_eq fun _ => Iff.rfl

def upwardData (n : ℕ) (C D : Data) (a b : ℕ) (N : Finset ℕ) (F : List ℕ) : Data :=
  (C.1 ∪ N, tabulate n (fun ij => decide (upCell C D false a b N F ij)),
    tabulate n (fun ij => decide (upCell C D true a b N F ij)))

theorem upwardData_primrec {n : σ → ℕ} {C D : σ → Data} {a b : σ → ℕ}
    {N : σ → Finset ℕ} {F : σ → List ℕ}
    (hn : Primrec n) (hC : Primrec C) (hD : Primrec D) (ha : Primrec a)
    (hb : Primrec b) (hN : Primrec N) (hF : Primrec F) :
    Primrec (fun s => upwardData (n s) (C s) (D s) (a s) (b s) (N s) (F s)) := by
  have hcell (l : Bool) : PrimrecRel (fun s ij => upCell (C s) (D s) l (a s) (b s)
      (N s) (F s) ij) :=
    (upCell_primrec (hC.comp Primrec.fst) (hD.comp Primrec.fst) (Primrec.const l)
      (ha.comp Primrec.fst) (hb.comp Primrec.fst) (hN.comp Primrec.fst)
      (hF.comp Primrec.fst) Primrec.snd)
  exact (PrimitiveFiniteOperations.finset_union.comp (Primrec.fst.comp hC) hN).pair
    ((tabulate_primrec hn (hcell false).decide.to₂).pair
      (tabulate_primrec hn (hcell true).decide.to₂))

/-- Exact upward tables, including off-carrier entries, for arbitrary records. -/
theorem upwardData_view {n : ℕ} (C D : PatternCode n) (a b : Fin n)
    (N : Finset (Fin n)) (g : Fin n → Fin n) :
    upwardData n (dataView C) (dataView D) a.val b.val (carrierView N) (mapView g) =
      dataView (C.upward D a b N g) := by
  apply Prod.ext
  · exact (Finset.map_union C.U N).symm
  · apply Prod.ext
    · dsimp only [upwardData, dataView]
      rw [tabulate_eq]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      simp [upCell, entryLevel, PrimitiveEndpointIso.entry₁, relation₁,
        PatternCode.upward, Fin.lt_def, -Fin.val_fin_lt]
    · dsimp only [upwardData, dataView]
      rw [tabulate_eq]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      simp [upCell, entryLevel, PrimitiveEndpointIso.entry₂, relation₂,
        PatternCode.upward, Fin.lt_def, -Fin.val_fin_lt,
        and_left_comm]

/-- Decode fields and construct the original downward target code. -/
def constructDownward (k : Bool) (n c a b s f : ℕ) : Option ℕ :=
  (decodeData n c).bind fun C =>
    (decodeParameters n a b s f).map fun p =>
      encodeData (downwardData n C k p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Decode fields and construct the original upward target code. -/
def constructUpward (n c d a b s f : ℕ) : Option ℕ :=
  (decodeData n c).bind fun C =>
    (decodeData n d).bind fun D =>
      (decodeParameters n a b s f).map fun p =>
        encodeData (upwardData n C D p.1 p.2.1 p.2.2.1 p.2.2.2)

theorem constructDownward_comp {k : σ → Bool} {n c a b s f : σ → ℕ}
    (hk : Primrec k) (hn : Primrec n) (hc : Primrec c) (ha : Primrec a)
    (hb : Primrec b) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun x => constructDownward (k x) (n x) (c x) (a x) (b x) (s x) (f x)) := by
  have hC := decodeData_primrec.comp hn hc
  have hP := decodeParameters_primrec hn ha hb hs hf
  unfold constructDownward
  refine Primrec.option_bind hC ?_
  apply Primrec₂.mk
  refine Primrec.option_map (hP.comp Primrec.fst) ?_
  apply Primrec₂.mk
  exact encodeData_primrec.comp
    (downwardData_primrec (hn.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst) (hk.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem constructUpward_comp {n c d a b s f : σ → ℕ}
    (hn : Primrec n) (hc : Primrec c) (hd : Primrec d) (ha : Primrec a)
    (hb : Primrec b) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun x => constructUpward (n x) (c x) (d x) (a x) (b x) (s x) (f x)) := by
  have hC := decodeData_primrec.comp hn hc
  have hD := decodeData_primrec.comp hn hd
  have hP := decodeParameters_primrec hn ha hb hs hf
  unfold constructUpward
  refine Primrec.option_bind hC ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (hD.comp Primrec.fst) ?_
  apply Primrec₂.mk
  refine Primrec.option_map (hP.comp (Primrec.fst.comp Primrec.fst)) ?_
  apply Primrec₂.mk
  exact encodeData_primrec.comp
    (upwardData_primrec (hn.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

/-- Exact original decoder/constructor behavior on every raw input. -/
theorem constructDownward_eq (k : Bool) (n c a b s f : ℕ) :
    constructDownward k n c a b s f =
      match decode (α := PatternCode n) c, decode (α := Fin n) a,
          decode (α := Fin n) b, decode (α := Finset (Fin n)) s,
          decode (α := Fin n → Fin n) f with
      | some C, some a', some b', some N, some g =>
          some (encode (C.downward (level k) a' b' N g))
      | _, _, _, _, _ => none := by
  cases hC : decode (α := PatternCode n) c <;>
    cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [constructDownward, decodeData_eq, decodeParameters_eq,
      hC, ha, hb, hN, hg, downwardData_view, encodeData_dataView]

theorem constructUpward_eq (n c d a b s f : ℕ) :
    constructUpward n c d a b s f =
      match decode (α := PatternCode n) c, decode (α := PatternCode n) d,
          decode (α := Fin n) a, decode (α := Fin n) b,
          decode (α := Finset (Fin n)) s, decode (α := Fin n → Fin n) f with
      | some C, some D, some a', some b', some N, some g =>
          some (encode (C.upward D a' b' N g))
      | _, _, _, _, _, _ => none := by
  cases hC : decode (α := PatternCode n) c <;>
    cases hD : decode (α := PatternCode n) d <;>
    cases ha : decode (α := Fin n) a <;>
    cases hb : decode (α := Fin n) b <;>
    cases hN : decode (α := Finset (Fin n)) s <;>
    cases hg : decode (α := Fin n → Fin n) f <;>
    simp [constructUpward, decodeData_eq, decodeParameters_eq,
      hC, hD, ha, hb, hN, hg, upwardData_view, encodeData_dataView]

@[simp] theorem constructDownward_encode {n : ℕ} (k : Bool) (C : PatternCode n)
    (a b : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n) :
    constructDownward k n (encode C) (encode a) (encode b) (encode N) (encode g) =
      some (encode (C.downward (level k) a b N g)) := by
  rw [constructDownward_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek]

@[simp] theorem constructUpward_encode {n : ℕ} (C D : PatternCode n)
    (a b : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n) :
    constructUpward n (encode C) (encode D) (encode a) (encode b) (encode N) (encode g) =
      some (encode (C.upward D a b N g)) := by
  rw [constructUpward_eq, Encodable.encodek, Encodable.encodek, Encodable.encodek,
    Encodable.encodek, Encodable.encodek, Encodable.encodek]

abbrev RawDownward := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
abbrev RawUpward := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

theorem constructDownward_primrec (k : Bool) :
    Primrec (fun p : RawDownward => constructDownward k p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  constructDownward_comp (Primrec.const k) Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem constructUpward_primrec :
    Primrec (fun p : RawUpward => constructUpward p.1 p.2.1 p.2.2.1 p.2.2.2.1
      p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) :=
  constructUpward_comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

set_option maxHeartbeats 800000 in
/-- A total machine constructs downward targets at every finite bound. -/
theorem constructDownward_program (k : Bool) : ∃ machine : Nat.Partrec.Code,
    ∀ n c a b s f : ℕ,
      machine.eval (encode ((n, c, a, b, s, f) : RawDownward)) =
        Part.some (encode (constructDownward k n c a b s f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program (constructDownward_primrec k)
  exact ⟨machine, fun n c a b s f => hm (n, c, a, b, s, f)⟩

set_option maxHeartbeats 800000 in
/-- A total machine constructs upward targets at every finite bound. -/
theorem constructUpward_program : ∃ machine : Nat.Partrec.Code,
    ∀ n c d a b s f : ℕ,
      machine.eval (encode ((n, c, d, a, b, s, f) : RawUpward)) =
        Part.some (encode (constructUpward n c d a b s f)) := by
  obtain ⟨machine, hm⟩ := PrimitiveFiniteOperations.exists_program constructUpward_primrec
  exact ⟨machine, fun n c d a b s f => hm (n, c, d, a, b, s, f)⟩

end Alexander313.Carlson.PrimitiveReflectionConstructors
