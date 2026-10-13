import Alexander313.Carlson.PrimitiveRationalMaps
import Alexander313.Carlson.PrimitiveFiniteOperations

/-!
# Primitive-recursive isomorphism checks for rational map tables

The finite carrier image and every carrier pair are tested with the existing
codes. The test is equivalent to the original `Str.IsIso` for arbitrary
presentations and map tables, including repeated keys and off-carrier edges.
-/

namespace Alexander313.Carlson.PrimitiveRationalIso

open Finite PrimitiveRationalPresentation PrimitiveRationalMaps

variable {σ : Type*} [Primcodable σ]

def PairCondition (P Q : RationalPresentation) (t : RationalMap.Table) (xy : ℚ × ℚ) : Prop :=
  (xy.1 < xy.2 → RationalMap.eval t xy.1 < RationalMap.eval t xy.2) ∧
    (P.toStr.r₁ xy.1 xy.2 ↔ Q.toStr.r₁ (RationalMap.eval t xy.1) (RationalMap.eval t xy.2)) ∧
    (P.toStr.r₂ xy.1 xy.2 ↔ Q.toStr.r₂ (RationalMap.eval t xy.1) (RationalMap.eval t xy.2))

instance (P Q : RationalPresentation) (t : RationalMap.Table) (xy : ℚ × ℚ) :
    Decidable (PairCondition P Q t xy) := by unfold PairCondition; infer_instance

def IsoData (P Q : RationalPresentation) (t : RationalMap.Table) : Prop :=
  P.U.image (RationalMap.eval t) = Q.U ∧ ∀ xy ∈ P.U ×ˢ P.U, PairCondition P Q t xy

instance (P Q : RationalPresentation) (t : RationalMap.Table) : Decidable (IsoData P Q t) := by
  unfold IsoData
  infer_instance

theorem pairCondition_primrec {P Q : σ → RationalPresentation} {t : σ → RationalMap.Table}
    (hP : Primrec P) (hQ : Primrec Q) (ht : Primrec t) :
    PrimrecRel (fun (xy : ℚ × ℚ) s => PairCondition (P s) (Q s) (t s) xy) := by
  have hP' := hP.comp (Primrec.snd : Primrec (fun x : (ℚ × ℚ) × σ => x.2))
  have hQ' := hQ.comp (Primrec.snd : Primrec (fun x : (ℚ × ℚ) × σ => x.2))
  have ht' := ht.comp (Primrec.snd : Primrec (fun x : (ℚ × ℚ) × σ => x.2))
  have hi : Primrec (fun x : (ℚ × ℚ) × σ => x.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun x : (ℚ × ℚ) × σ => x.1.2) := Primrec.snd.comp Primrec.fst
  have hx := eval_primrec.comp ht' hi
  have hy := eval_primrec.comp ht' hj
  have ho : PrimrecPred (fun x : (ℚ × ℚ) × σ =>
      x.1.1 < x.1.2 → RationalMap.eval (t x.2) x.1.1 < RationalMap.eval (t x.2) x.1.2) :=
    ((PrimitiveRationalData.rat_lt.comp hi hj).not.or
      (PrimitiveRationalData.rat_lt.comp hx hy)).of_eq (fun _ => imp_iff_not_or.symm)
  have h₁ : PrimrecPred (fun x : (ℚ × ℚ) × σ =>
      (P x.2).toStr.r₁ x.1.1 x.1.2 ↔
        (Q x.2).toStr.r₁ (RationalMap.eval (t x.2) x.1.1) (RationalMap.eval (t x.2) x.1.2)) := by
    refine (Primrec.eq.comp (relation₁_mem.decide.comp hP' Primrec.fst)
      (relation₁_mem.decide.comp hQ' (hx.pair hy))).of_eq ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    rfl
  have h₂ : PrimrecPred (fun x : (ℚ × ℚ) × σ =>
      (P x.2).toStr.r₂ x.1.1 x.1.2 ↔
        (Q x.2).toStr.r₂ (RationalMap.eval (t x.2) x.1.1) (RationalMap.eval (t x.2) x.1.2)) := by
    refine (Primrec.eq.comp (relation₂_mem.decide.comp hP' Primrec.fst)
      (relation₂_mem.decide.comp hQ' (hx.pair hy))).of_eq ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    rfl
  exact (ho.and (h₁.and h₂)).of_eq (fun _ => Iff.rfl)

theorem isoData_primrec {P Q : σ → RationalPresentation} {t : σ → RationalMap.Table}
    (hP : Primrec P) (hQ : Primrec Q) (ht : Primrec t) :
    PrimrecPred (fun s => IsoData (P s) (Q s) (t s)) := by
  have hU := carrier_primrec.comp hP
  have himage := (PrimitiveFiniteOperations.finset_image eval_primrec).comp ht hU
  exact ((Primrec.eq.comp himage (carrier_primrec.comp hQ)).and
    ((PrimitiveFiniteOperations.forall_mem (pairCondition_primrec hP hQ ht)).comp
      (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id)).of_eq
    (fun _ => Iff.rfl)

theorem isoData_iff (P Q : RationalPresentation) (t : RationalMap.Table) :
    IsoData P Q t ↔ Str.IsIso P.toStr Q.toStr (RationalMap.eval t) := by
  unfold IsoData Str.IsIso
  simp only [RationalPresentation.toStr_U]
  refine and_congr Iff.rfl ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · intro x hx y hy hxy
    exact (h (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)).1 hxy
  · intro x hx y hy
    exact (h (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)).2
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    exact ⟨h.1 x hx y hy, h.2 x hx y hy⟩

def check (P Q : RationalPresentation) (t : RationalMap.Table) : Bool := decide (IsoData P Q t)

@[simp] theorem check_eq_true (P Q : RationalPresentation) (t : RationalMap.Table) :
    check P Q t = true ↔ Str.IsIso P.toStr Q.toStr (RationalMap.eval t) := by
  simp only [check, decide_eq_true_eq, isoData_iff]

theorem check_primrec : Primrec (fun x : (RationalPresentation × RationalPresentation) ×
    RationalMap.Table => check x.1.1 x.1.2 x.2) :=
  (isoData_primrec (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst) Primrec.snd).decide

theorem check_program : ∃ p : Nat.Partrec.Code,
    ∀ (P Q : RationalPresentation) (t : RationalMap.Table),
      p.eval (Encodable.encode ((P, Q), t)) = Part.some (Encodable.encode (check P Q t)) := by
  obtain ⟨p, hp⟩ := exists_code check_primrec
  exact ⟨p, fun P Q t => hp ((P, Q), t)⟩

end Alexander313.Carlson.PrimitiveRationalIso
