import Alexander313.Carlson.RationalExactness
import Alexander313.Carlson.PrimitiveDerivationRecognition
import Alexander313.Carlson.PrimitiveFiniteOperations

/-!
# Primitive-recursive rational exactness recognition

The original rational presentation and dependent rational derivation codecs
remain unchanged. All eight pattern conditions and the initial-span boundary
condition are certified by bounded quantification over stored finite carriers.
The resulting verifier is primitive recursive and has an actual machine code.
-/

namespace Alexander313.Carlson.PrimitiveRationalExactness

open Encodable Finite PrimitiveRationalPresentation

private theorem forall_product_iff {α β : Type*} (s : Finset α) (t : Finset β)
    (p : α × β → Prop) :
    (∀ xy ∈ s ×ˢ t, p xy) ↔ ∀ x ∈ s, ∀ y ∈ t, p (x, y) := by
  constructor
  · intro h x hx y hy
    exact h (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)
  · rintro h ⟨x, y⟩ hxy
    exact h x (Finset.mem_product.mp hxy).1 y (Finset.mem_product.mp hxy).2

/-- The first relation is contained in the ambient order on the carrier. -/
private def Le₁Condition (d : RationalPresentation) : Prop :=
  ∀ ij ∈ d.U ×ˢ d.U, ij ∈ d.r₁ → ij.1 ≤ ij.2

/-- The second relation is contained in the first on the carrier. -/
private def Sub₂Condition (d : RationalPresentation) : Prop :=
  ∀ ij ∈ d.U ×ˢ d.U, ij ∈ d.r₂ → ij ∈ d.r₁

private def Refl₁Condition (d : RationalPresentation) : Prop := ∀ i ∈ d.U, (i, i) ∈ d.r₁

private def Refl₂Condition (d : RationalPresentation) : Prop := ∀ i ∈ d.U, (i, i) ∈ d.r₂

private def Trans₁Condition (d : RationalPresentation) : Prop :=
  ∀ ijk ∈ d.U ×ˢ (d.U ×ˢ d.U),
    (ijk.1, ijk.2.1) ∈ d.r₁ →
    (ijk.2.1, ijk.2.2) ∈ d.r₁ → (ijk.1, ijk.2.2) ∈ d.r₁

private def Trans₂Condition (d : RationalPresentation) : Prop :=
  ∀ ijk ∈ d.U ×ˢ (d.U ×ˢ d.U),
    (ijk.1, ijk.2.1) ∈ d.r₂ →
    (ijk.2.1, ijk.2.2) ∈ d.r₂ → (ijk.1, ijk.2.2) ∈ d.r₂

private def Convex₁Condition (d : RationalPresentation) : Prop :=
  ∀ ijk ∈ d.U ×ˢ (d.U ×ˢ d.U), ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
    (ijk.1, ijk.2.2) ∈ d.r₁ → (ijk.1, ijk.2.1) ∈ d.r₁

private def Respect₂Condition (d : RationalPresentation) : Prop :=
  ∀ ijk ∈ d.U ×ˢ (d.U ×ˢ d.U), ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
    (ijk.1, ijk.2.2) ∈ d.r₂ → (ijk.2.1, ijk.2.2) ∈ d.r₁ →
      (ijk.1, ijk.2.1) ∈ d.r₂

/-- All eight original pattern conditions, with their original order. -/
private def PatternCondition (d : RationalPresentation) : Prop :=
  Le₁Condition d ∧ Sub₂Condition d ∧ Refl₁Condition d ∧ Refl₂Condition d ∧
    Trans₁Condition d ∧ Trans₂Condition d ∧ Convex₁Condition d ∧ Respect₂Condition d

private instance (d : RationalPresentation) : Decidable (Le₁Condition d) := by
  unfold Le₁Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Sub₂Condition d) := by
  unfold Sub₂Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Refl₁Condition d) := by
  unfold Refl₁Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Refl₂Condition d) := by
  unfold Refl₂Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Trans₁Condition d) := by
  unfold Trans₁Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Trans₂Condition d) := by
  unfold Trans₂Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Convex₁Condition d) := by
  unfold Convex₁Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (Respect₂Condition d) := by
  unfold Respect₂Condition
  infer_instance
private instance (d : RationalPresentation) : Decidable (PatternCondition d) := by
  unfold PatternCondition
  infer_instance

variable {σ : Type*} [Primcodable σ]

private theorem imp_primrec {p q : σ → Prop} (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred (fun s => p s → q s) :=
  (hp.not.or hq).of_eq fun _ => imp_iff_not_or.symm

private theorem edge₁_primrec {d : σ → RationalPresentation} {i j : σ → ℚ}
    (hd : Primrec d) (hi : Primrec i) (hj : Primrec j) :
    PrimrecPred (fun s => (i s, j s) ∈ (d s).r₁) :=
  relation₁_mem.comp hd (hi.pair hj)

private theorem edge₂_primrec {d : σ → RationalPresentation} {i j : σ → ℚ}
    (hd : Primrec d) (hi : Primrec i) (hj : Primrec j) :
    PrimrecPred (fun s => (i s, j s) ∈ (d s).r₂) :=
  relation₂_mem.comp hd (hi.pair hj)

private theorem forall_points_primrec {p : ℚ → RationalPresentation → Prop} (hp : PrimrecRel p) :
    PrimrecPred (fun d : RationalPresentation => ∀ i ∈ d.U, p i d) :=
  (PrimitiveFiniteOperations.forall_mem hp).comp
    carrier_primrec Primrec.id

private theorem forall_pairs_primrec {p : (ℚ × ℚ) → RationalPresentation → Prop}
    (hp : PrimrecRel p) :
    PrimrecPred (fun d : RationalPresentation => ∀ ij ∈ d.U ×ˢ d.U, p ij d) := by
  have hU : Primrec (fun d : RationalPresentation => d.U) := carrier_primrec
  exact (PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id

private theorem forall_triples_primrec {p : (ℚ × ℚ × ℚ) → RationalPresentation → Prop}
    (hp : PrimrecRel p) :
    PrimrecPred (fun d : RationalPresentation => ∀ ijk ∈ d.U ×ˢ (d.U ×ˢ d.U), p ijk d) := by
  have hU : Primrec (fun d : RationalPresentation => d.U) := carrier_primrec
  have hUU : Primrec (fun d : RationalPresentation => d.U ×ˢ d.U) :=
    PrimitiveFiniteOperations.finset_product.comp hU hU
  exact (PrimitiveFiniteOperations.forall_mem hp).comp
    (PrimitiveFiniteOperations.finset_product.comp hU hUU) Primrec.id

private theorem le₁Condition_primrec : PrimrecPred Le₁Condition := by
  have hd : Primrec (fun p : (ℚ × ℚ) × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℚ × ℚ) × RationalPresentation => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℚ × ℚ) × RationalPresentation => p.1.2) := Primrec.snd.comp Primrec.fst
  have hp : PrimrecRel (fun (ij : ℚ × ℚ) (d : RationalPresentation) =>
      ij ∈ d.r₁ → ij.1 ≤ ij.2) :=
    (imp_primrec (edge₁_primrec hd hi hj) (PrimitiveRationalData.rat_le.comp hi hj)).of_eq
      fun _ => Iff.rfl
  exact (forall_pairs_primrec hp).of_eq fun _ => Iff.rfl

private theorem sub₂Condition_primrec : PrimrecPred Sub₂Condition := by
  have hd : Primrec (fun p : (ℚ × ℚ) × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℚ × ℚ) × RationalPresentation => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℚ × ℚ) × RationalPresentation => p.1.2) := Primrec.snd.comp Primrec.fst
  have hp : PrimrecRel (fun (ij : ℚ × ℚ) (d : RationalPresentation) =>
      ij ∈ d.r₂ → ij ∈ d.r₁) :=
    (imp_primrec (edge₂_primrec hd hi hj) (edge₁_primrec hd hi hj)).of_eq
      fun _ => Iff.rfl
  exact (forall_pairs_primrec hp).of_eq fun _ => Iff.rfl

private theorem refl₁Condition_primrec : PrimrecPred Refl₁Condition := by
  have hd : Primrec (fun p : ℚ × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : ℚ × RationalPresentation => p.1) := Primrec.fst
  have hp : PrimrecRel (fun (i : ℚ) (d : RationalPresentation) => (i, i) ∈ d.r₁) :=
    edge₁_primrec hd hi hi
  exact (forall_points_primrec hp).of_eq fun _ => Iff.rfl

private theorem refl₂Condition_primrec : PrimrecPred Refl₂Condition := by
  have hd : Primrec (fun p : ℚ × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : ℚ × RationalPresentation => p.1) := Primrec.fst
  have hp : PrimrecRel (fun (i : ℚ) (d : RationalPresentation) => (i, i) ∈ d.r₂) :=
    edge₂_primrec hd hi hi
  exact (forall_points_primrec hp).of_eq fun _ => Iff.rfl

private theorem trans₁Condition_primrec : PrimrecPred Trans₁Condition := by
  have hd : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℚ × ℚ × ℚ) (d : RationalPresentation) =>
      (ijk.1, ijk.2.1) ∈ d.r₁ →
        (ijk.2.1, ijk.2.2) ∈ d.r₁ → (ijk.1, ijk.2.2) ∈ d.r₁) :=
    imp_primrec (edge₁_primrec hd hi hj)
      (imp_primrec (edge₁_primrec hd hj hk) (edge₁_primrec hd hi hk))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

private theorem trans₂Condition_primrec : PrimrecPred Trans₂Condition := by
  have hd : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℚ × ℚ × ℚ) (d : RationalPresentation) =>
      (ijk.1, ijk.2.1) ∈ d.r₂ →
        (ijk.2.1, ijk.2.2) ∈ d.r₂ → (ijk.1, ijk.2.2) ∈ d.r₂) :=
    imp_primrec (edge₂_primrec hd hi hj)
      (imp_primrec (edge₂_primrec hd hj hk) (edge₂_primrec hd hi hk))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

private theorem convex₁Condition_primrec : PrimrecPred Convex₁Condition := by
  have hd : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℚ × ℚ × ℚ) (d : RationalPresentation) =>
      ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
        (ijk.1, ijk.2.2) ∈ d.r₁ → (ijk.1, ijk.2.1) ∈ d.r₁) :=
    imp_primrec (PrimitiveRationalData.rat_le.comp hi hj)
      (imp_primrec (PrimitiveRationalData.rat_le.comp hj hk)
        (imp_primrec (edge₁_primrec hd hi hk) (edge₁_primrec hd hi hj)))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

private theorem respect₂Condition_primrec : PrimrecPred Respect₂Condition := by
  have hd : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.2) := Primrec.snd
  have hi : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : (ℚ × ℚ × ℚ) × RationalPresentation => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hp : PrimrecRel (fun (ijk : ℚ × ℚ × ℚ) (d : RationalPresentation) =>
      ijk.1 ≤ ijk.2.1 → ijk.2.1 ≤ ijk.2.2 →
        (ijk.1, ijk.2.2) ∈ d.r₂ → (ijk.2.1, ijk.2.2) ∈ d.r₁ →
          (ijk.1, ijk.2.1) ∈ d.r₂) :=
    imp_primrec (PrimitiveRationalData.rat_le.comp hi hj)
      (imp_primrec (PrimitiveRationalData.rat_le.comp hj hk)
        (imp_primrec (edge₂_primrec hd hi hk)
          (imp_primrec (edge₁_primrec hd hj hk) (edge₂_primrec hd hi hj))))
  exact (forall_triples_primrec hp).of_eq fun _ => Iff.rfl

/-- A primitive-recursive certificate for every one of the eight fields. -/
private theorem patternCondition_primrec : PrimrecPred PatternCondition :=
  (le₁Condition_primrec.and (sub₂Condition_primrec.and (refl₁Condition_primrec.and
    (refl₂Condition_primrec.and (trans₁Condition_primrec.and (trans₂Condition_primrec.and
      (convex₁Condition_primrec.and respect₂Condition_primrec))))))).of_eq fun _ => Iff.rfl

private theorem patternConditions_iff (P : RationalPresentation) :
    PatternCondition P ↔ P.toStr.IsPattern := by
  rw [Str.isPattern_iff_conditions]
  simp only [PatternCondition, Le₁Condition, Sub₂Condition,
    Refl₁Condition, Refl₂Condition, Trans₁Condition,
    Trans₂Condition, Convex₁Condition, Respect₂Condition,
    forall_product_iff, RationalPresentation.toStr_U,
    RationalPresentation.toStr_r₁, RationalPresentation.toStr_r₂]

/-- Patternhood is primitive recursive for the original rational presentations. -/
theorem checkPattern_primrec : Primrec RationalPresentation.checkPattern :=
  patternCondition_primrec.decide.of_eq fun P => by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, RationalPresentation.checkPattern_eq_true]
    exact patternConditions_iff P

/-- Restriction preserves the original tables and their codecs. -/
theorem restrict_primrec :
    Primrec₂ RationalPresentation.restrict :=
  mk_primrec Primrec.snd (relation₁_primrec.comp Primrec.fst)
    (relation₂_primrec.comp Primrec.fst)

/-- The initial span is computed by a primitive-recursive finite filter. -/
theorem initialSpan_primrec :
    Primrec₂ RationalPresentation.initialSpan := by
  have hBound : PrimrecRel (fun (s : Finset ℚ) x => ∃ p ∈ s, x ≤ p) :=
    PrimitiveFiniteOperations.exists_mem
      (PrimitiveRationalData.rat_le.comp Primrec.snd Primrec.fst)
  have hU : Primrec (fun q : RationalPresentation × Finset ℚ =>
      q.1.U.filter (fun x => ∃ p ∈ q.2, x ≤ p)) :=
    (PrimitiveFiniteOperations.finset_filter hBound).comp Primrec.snd
      (carrier_primrec.comp Primrec.fst)
  exact mk_primrec hU (relation₁_primrec.comp Primrec.fst)
    (relation₂_primrec.comp Primrec.fst)

/-- The original initial-span correctness obligation is primitive recursive. -/
theorem checkInitialSpanCorrect_primrec :
    Primrec₂ RationalPresentation.checkInitialSpanCorrect := by
  have hspan : Primrec (fun q : RationalPresentation × Finset ℚ =>
      (q.1.initialSpan q.2).U) := carrier_primrec.comp initialSpan_primrec
  have hU : Primrec (fun q : RationalPresentation × Finset ℚ => q.1.U) :=
    carrier_primrec.comp Primrec.fst
  have hp : PrimrecRel (fun (xy : ℚ × ℚ) (q : RationalPresentation × Finset ℚ) =>
      xy ∈ q.1.r₁ → xy.2 ∈ (q.1.initialSpan q.2).U) :=
    imp_primrec (relation₁_mem.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (PrimitiveFiniteData.finset_mem.comp (Primrec.snd.comp Primrec.fst)
        (hspan.comp Primrec.snd))
  have h : PrimrecPred (fun q : RationalPresentation × Finset ℚ =>
      ∀ x ∈ (q.1.initialSpan q.2).U, ∀ y ∈ q.1.U,
        q.1.toStr.r₁ x y → y ∈ (q.1.initialSpan q.2).U) :=
    ((PrimitiveFiniteOperations.forall_mem hp).comp
      (PrimitiveFiniteOperations.finset_product.comp hspan hU) Primrec.id).of_eq
        fun q => by simp only [forall_product_iff, id_eq,
          RationalPresentation.toStr_r₁]
  exact h.decide

/-- Every original generation code, including malformed ones, is handled by
one primitive-recursive exactness verifier. -/
theorem checkExact_primrec :
    Primrec (fun q : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkExact q.1.1 q.1.2 q.2) := by
  have hP : Primrec (fun q : (RationalPresentation × RationalPresentation) × ℕ =>
      q.1.1) := Primrec.fst.comp Primrec.fst
  have hQ : Primrec (fun q : (RationalPresentation × RationalPresentation) × ℕ =>
      q.1.2) := Primrec.snd.comp Primrec.fst
  have hU := carrier_primrec.comp hP
  have hspan := initialSpan_primrec.comp hQ hU
  have hPattern := checkPattern_primrec.comp hQ
  have hGeneration := PrimitiveDerivationRecognition.rational_generation_check_primrec.comp
    ((hP.pair hspan).pair Primrec.snd)
  have hCorrect := checkInitialSpanCorrect_primrec.comp hQ hU
  have h : PrimrecPred (fun q : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkExact q.1.1 q.1.2 q.2 = true) :=
    ((Primrec.eq.comp hPattern (Primrec.const true)).and
      ((Primrec.eq.comp hGeneration (Primrec.const true)).and
        (Primrec.eq.comp hCorrect (Primrec.const true)))).of_eq fun q => by
      simp only [RationalPresentation.checkExact, Bool.and_eq_true, and_assoc]
  exact h.decide.of_eq fun q => by simp only [Bool.decide_coe]

/-- The total exactness verifier has an actual partial-recursive machine,
using the original typed endpoint encodings and every raw certificate code. -/
theorem checkExact_program : ∃ machine : Nat.Partrec.Code,
    ∀ (P Q : RationalPresentation) (code : ℕ),
      machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkExact P Q code)) := by
  obtain ⟨machine, hm⟩ := exists_code checkExact_primrec
  exact ⟨machine, fun P Q code => hm ((P, Q), code)⟩

/-- Machine acceptance recognizes precisely original semantic exactness. -/
theorem exactness_machine : ∃ machine : Nat.Partrec.Code,
    ∀ P Q : RationalPresentation,
      (∀ code, machine.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkExact P Q code))) ∧
      (Str.Exact P.toStr Q.toStr ↔
        ∃ code : ℕ, machine.eval (encode ((P, Q), code)) = Part.some (encode true)) := by
  obtain ⟨machine, hm⟩ := checkExact_program
  refine ⟨machine, fun P Q => ⟨hm P Q, ?_⟩⟩
  rw [RationalPresentation.exact_iff_exists_code]
  simp only [hm P Q, Part.some_inj, encode_inj]

end Alexander313.Carlson.PrimitiveRationalExactness
