import Alexander313.Carlson.PrimitiveFiniteOperations
import Alexander313.Carlson.PrimitiveRationalCertificate

/-!
# Primitive-recursive endpoint isomorphism checks

`RationalWitness.check` accepts a rational certificate only after three
finite checks that do not inspect the stored derivation: the whole grid is
strictly increasing, and the grid labels map the source and target pattern
codes isomorphically onto the two claimed rational presentations. The grid
check is certified in `PrimitiveRationalCertificate`. This module certifies
both endpoint isomorphism checks, uniformly in the grid size.

The data-level test reads the lossless table view of a pattern code and
the list of all grid labels. It compares the image of the carrier with the
claimed rational carrier, checks strict order preservation on every
carrier pair, and compares both stored table entries with membership of
the labelled edge in the claimed relation sets. Off-carrier table entries
and stored off-carrier rational edges are never consulted, exactly as in
`Str.IsIso`. Its agreement with the original propositional check is proved
for every finite pattern code and every labeling.

Combined with a supplied primitive-recursive finite derivation checker,
these results certify the complete natural-number recognizer
`RationalPresentation.checkCertificate` on every raw certificate code.
The remaining obligation for `RationalPresentation.checkRule`,
`checkChain` and `checkGeneration` is therefore precisely the uniform
primitive recursiveness of the three finite derivation checkers,
including exhaustive minimality checking. That obligation is stated as a
hypothesis here and is not discharged.
-/

namespace Alexander313.Carlson.PrimitiveEndpointIso

open Encodable Finite PrimitivePatternCode

variable {σ : Type*} [Primcodable σ]

/-- The rational grid label at a natural index. The default value is
used only for indices outside the grid. -/
def labelAt (labels : List ℚ) (i : ℕ) : ℚ := (labels[i]?).getD 0

theorem labelAt_primrec : Primrec₂ labelAt :=
  (Primrec.option_getD.comp Primrec.list_getElem? (Primrec.const (0 : ℚ))).of_eq
    fun _ => rfl

@[simp] theorem labelAt_ofFn {n : ℕ} (labels : Fin n → ℚ) (i : Fin n) :
    labelAt (List.ofFn labels) i.val = labels i := by
  simp [labelAt]

/-- A first-table entry of the uniform data view; a missing entry reads
as `false`. -/
def entry₁ (d : Data) (ij : ℕ × ℕ) : Bool := (relation₁ d ij).getD false

/-- A second-table entry of the uniform data view; a missing entry reads
as `false`. -/
def entry₂ (d : Data) (ij : ℕ × ℕ) : Bool := (relation₂ d ij).getD false

theorem entry₁_primrec : Primrec₂ entry₁ :=
  (Primrec.option_getD.comp relation₁_primrec (Primrec.const false)).of_eq fun _ => rfl

theorem entry₂_primrec : Primrec₂ entry₂ :=
  (Primrec.option_getD.comp relation₂_primrec (Primrec.const false)).of_eq fun _ => rfl

@[simp] theorem entry₁_dataView {n : ℕ} (C : PatternCode n) (i j : Fin n) :
    entry₁ (dataView C) (i.val, j.val) = C.r₁ i j := by
  simp [entry₁]

@[simp] theorem entry₂_dataView {n : ℕ} (C : PatternCode n) (i j : Fin n) :
    entry₂ (dataView C) (i.val, j.val) = C.r₂ i j := by
  simp [entry₂]

/-- The order and relation conditions of `Str.IsIso` for one ordered pair
of natural carrier labels. -/
def PairCondition (d : Data) (labels : List ℚ) (P : RationalPresentation)
    (ij : ℕ × ℕ) : Prop :=
  (ij.1 < ij.2 → labelAt labels ij.1 < labelAt labels ij.2) ∧
    entry₁ d ij = decide ((labelAt labels ij.1, labelAt labels ij.2) ∈ P.r₁) ∧
    entry₂ d ij = decide ((labelAt labels ij.1, labelAt labels ij.2) ∈ P.r₂)

instance instDecidablePairCondition (d : Data) (labels : List ℚ)
    (P : RationalPresentation) (ij : ℕ × ℕ) :
    Decidable (PairCondition d labels P ij) := by
  unfold PairCondition
  infer_instance

/-- The data-level form of `Str.IsIso`: the labelled carrier is the claimed
carrier, and every carrier pair satisfies `PairCondition`. -/
def IsoData (d : Data) (labels : List ℚ) (P : RationalPresentation) : Prop :=
  d.1.image (labelAt labels) = P.U ∧ ∀ ij ∈ d.1 ×ˢ d.1, PairCondition d labels P ij

instance instDecidableIsoData (d : Data) (labels : List ℚ) (P : RationalPresentation) :
    Decidable (IsoData d labels P) := by
  unfold IsoData
  infer_instance

/-- The pair conditions are primitive recursive in uniformly supplied data,
labels, and presentations. -/
theorem pairCondition_primrec {d : σ → Data} {L : σ → List ℚ}
    {P : σ → RationalPresentation} (hd : Primrec d) (hL : Primrec L) (hP : Primrec P) :
    PrimrecRel (fun (ij : ℕ × ℕ) s => PairCondition (d s) (L s) (P s) ij) := by
  have hd' : Primrec (fun x : (ℕ × ℕ) × σ => d x.2) := hd.comp Primrec.snd
  have hL' : Primrec (fun x : (ℕ × ℕ) × σ => L x.2) := hL.comp Primrec.snd
  have hP' : Primrec (fun x : (ℕ × ℕ) × σ => P x.2) := hP.comp Primrec.snd
  have hi : Primrec (fun x : (ℕ × ℕ) × σ => x.1.1) := Primrec.fst.comp Primrec.fst
  have hj : Primrec (fun x : (ℕ × ℕ) × σ => x.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun x : (ℕ × ℕ) × σ => labelAt (L x.2) x.1.1) :=
    labelAt_primrec.comp hL' hi
  have hy : Primrec (fun x : (ℕ × ℕ) × σ => labelAt (L x.2) x.1.2) :=
    labelAt_primrec.comp hL' hj
  have horder : PrimrecPred (fun x : (ℕ × ℕ) × σ =>
      x.1.1 < x.1.2 → labelAt (L x.2) x.1.1 < labelAt (L x.2) x.1.2) :=
    ((Primrec.nat_lt.comp hi hj).not.or (PrimitiveRationalData.rat_lt.comp hx hy)).of_eq
      fun _ => imp_iff_not_or.symm
  have hfirst : PrimrecPred (fun x : (ℕ × ℕ) × σ =>
      entry₁ (d x.2) x.1 =
        decide ((labelAt (L x.2) x.1.1, labelAt (L x.2) x.1.2) ∈ (P x.2).r₁)) :=
    Primrec.eq.comp (entry₁_primrec.comp hd' Primrec.fst)
      (PrimitiveRationalPresentation.relation₁_mem.decide.comp hP' (hx.pair hy))
  have hsecond : PrimrecPred (fun x : (ℕ × ℕ) × σ =>
      entry₂ (d x.2) x.1 =
        decide ((labelAt (L x.2) x.1.1, labelAt (L x.2) x.1.2) ∈ (P x.2).r₂)) :=
    Primrec.eq.comp (entry₂_primrec.comp hd' Primrec.fst)
      (PrimitiveRationalPresentation.relation₂_mem.decide.comp hP' (hx.pair hy))
  exact (horder.and (hfirst.and hsecond)).of_eq fun _ => Iff.rfl

/-- The complete data-level isomorphism check is primitive recursive. -/
theorem isoData_primrec {d : σ → Data} {L : σ → List ℚ}
    {P : σ → RationalPresentation} (hd : Primrec d) (hL : Primrec L) (hP : Primrec P) :
    PrimrecPred (fun s => IsoData (d s) (L s) (P s)) := by
  have hU : Primrec (fun s => (d s).1) := Primrec.fst.comp hd
  have himage : Primrec (fun s => (d s).1.image (labelAt (L s))) :=
    (PrimitiveFiniteOperations.finset_image labelAt_primrec).comp hL hU
  exact ((Primrec.eq.comp himage
      (PrimitiveRationalPresentation.carrier_primrec.comp hP)).and
    ((PrimitiveFiniteOperations.forall_mem (pairCondition_primrec hd hL hP)).comp
      (PrimitiveFiniteOperations.finset_product.comp hU hU) Primrec.id)).of_eq
    fun _ => Iff.rfl

theorem mem_carrierView_iff {n : ℕ} (U : Finset (Fin n)) (i : ℕ) :
    i ∈ carrierView U ↔ ∃ x ∈ U, x.val = i := by
  constructor
  · intro hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_map.mp hi
    exact ⟨x, hx, hxi⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_carrierView U x).mpr hx

theorem image_carrierView {n : ℕ} (U : Finset (Fin n)) (g : ℕ → ℚ) :
    (carrierView U).image g = U.image (fun x => g x.val) := by
  ext q
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff U i).mp hi
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, (mem_carrierView U x).mpr hx, rfl⟩

private theorem bool_eq_decide_iff (b : Bool) (p : Prop) [Decidable p] :
    b = decide p ↔ (b = true ↔ p) := by
  cases b <;> by_cases hp : p <;> simp [hp]

/-- On the lossless view of a finite pattern code and the list of all its
grid labels, the data-level check is exactly `Str.IsIso`. -/
theorem isoData_dataView_iff {n : ℕ} (C : PatternCode n) (labels : Fin n → ℚ)
    (P : RationalPresentation) :
    IsoData (dataView C) (List.ofFn labels) P ↔ Str.IsIso C.toStr P.toStr labels := by
  have himage :
      (dataView C).1.image (labelAt (List.ofFn labels)) = C.U.image labels := by
    change (carrierView C.U).image (labelAt (List.ofFn labels)) = C.U.image labels
    rw [image_carrierView]
    congr 1
    funext x
    exact labelAt_ofFn labels x
  unfold IsoData Str.IsIso
  rw [himage]
  simp only [PatternCode.toStr_U, RationalPresentation.toStr_U, PatternCode.toStr_r₁,
    PatternCode.toStr_r₂, RationalPresentation.toStr_r₁, RationalPresentation.toStr_r₂]
  refine and_congr Iff.rfl ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · intro x hx y hy hxy
    have hpair : labelAt (List.ofFn labels) x.val < labelAt (List.ofFn labels) y.val :=
      (h (x.val, y.val) (Finset.mem_product.mpr
        ⟨(mem_carrierView C.U x).mpr hx, (mem_carrierView C.U y).mpr hy⟩)).1 hxy
    rwa [labelAt_ofFn, labelAt_ofFn] at hpair
  · intro x hx y hy
    have hpair : entry₁ (dataView C) (x.val, y.val) =
          decide ((labelAt (List.ofFn labels) x.val,
            labelAt (List.ofFn labels) y.val) ∈ P.r₁) ∧
        entry₂ (dataView C) (x.val, y.val) =
          decide ((labelAt (List.ofFn labels) x.val,
            labelAt (List.ofFn labels) y.val) ∈ P.r₂) :=
      (h (x.val, y.val) (Finset.mem_product.mpr
        ⟨(mem_carrierView C.U x).mpr hx, (mem_carrierView C.U y).mpr hy⟩)).2
    rw [entry₁_dataView, entry₂_dataView, labelAt_ofFn, labelAt_ofFn] at hpair
    exact ⟨(bool_eq_decide_iff _ _).mp hpair.1, (bool_eq_decide_iff _ _).mp hpair.2⟩
  · rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    obtain ⟨x, hx, rfl⟩ := (mem_carrierView_iff C.U i).mp hi
    obtain ⟨y, hy, rfl⟩ := (mem_carrierView_iff C.U j).mp hj
    unfold PairCondition
    refine ⟨fun hxy => ?_, ?_, ?_⟩
    · have hlt := h.1 x hx y hy hxy
      show labelAt (List.ofFn labels) x.val < labelAt (List.ofFn labels) y.val
      rwa [labelAt_ofFn, labelAt_ofFn]
    · show entry₁ (dataView C) (x.val, y.val) =
        decide ((labelAt (List.ofFn labels) x.val,
          labelAt (List.ofFn labels) y.val) ∈ P.r₁)
      rw [entry₁_dataView, labelAt_ofFn, labelAt_ofFn]
      exact (bool_eq_decide_iff _ _).mpr (h.2 x hx y hy).1
    · show entry₂ (dataView C) (x.val, y.val) =
        decide ((labelAt (List.ofFn labels) x.val,
          labelAt (List.ofFn labels) y.val) ∈ P.r₂)
      rw [entry₂_dataView, labelAt_ofFn, labelAt_ofFn]
      exact (bool_eq_decide_iff _ _).mpr (h.2 x hx y hy).2

/-- The source endpoint check performed by `RationalWitness.check`. -/
def checkSource (c : RationalCertificate) (P : RationalPresentation) : Bool :=
  RationalPresentation.checkIso c.2.source c.2.labels P

/-- The target endpoint check performed by `RationalWitness.check`. -/
def checkTarget (c : RationalCertificate) (Q : RationalPresentation) : Bool :=
  RationalPresentation.checkIso c.2.target c.2.labels Q

@[simp] theorem checkSource_eq_true (c : RationalCertificate) (P : RationalPresentation) :
    checkSource c P = true ↔ Str.IsIso c.2.source.toStr P.toStr c.2.labels :=
  RationalPresentation.checkIso_eq_true _ _ _

@[simp] theorem checkTarget_eq_true (c : RationalCertificate) (Q : RationalPresentation) :
    checkTarget c Q = true ↔ Str.IsIso c.2.target.toStr Q.toStr c.2.labels :=
  RationalPresentation.checkIso_eq_true _ _ _

/-- The source isomorphism check is primitive recursive in the raw
certificate and the claimed presentation, uniformly in the grid size. -/
theorem checkSource_primrec : Primrec₂ checkSource := by
  have h : PrimrecRel (fun (c : RationalCertificate) (P : RationalPresentation) =>
      IsoData (dataView c.2.source) (PrimitiveRationalCertificate.gridLabels c) P) :=
    isoData_primrec (PrimitiveRationalCertificate.sourceData_primrec.comp Primrec.fst)
      (PrimitiveRationalCertificate.gridLabels_primrec.comp Primrec.fst) Primrec.snd
  refine h.decide.of_eq fun c P => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_eq, checkSource_eq_true]
  exact isoData_dataView_iff c.2.source c.2.labels P

/-- The target isomorphism check is primitive recursive in the raw
certificate and the claimed presentation, uniformly in the grid size. -/
theorem checkTarget_primrec : Primrec₂ checkTarget := by
  have h : PrimrecRel (fun (c : RationalCertificate) (Q : RationalPresentation) =>
      IsoData (dataView c.2.target) (PrimitiveRationalCertificate.gridLabels c) Q) :=
    isoData_primrec (PrimitiveRationalCertificate.targetData_primrec.comp Primrec.fst)
      (PrimitiveRationalCertificate.gridLabels_primrec.comp Primrec.fst) Primrec.snd
  refine h.decide.of_eq fun c Q => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_eq, checkTarget_eq_true]
  exact isoData_dataView_iff c.2.target c.2.labels Q

/-- Every check of `RationalWitness.check` except the finite derivation:
the whole ordered grid and both endpoint isomorphisms. -/
def checkFrame (c : RationalCertificate) (P Q : RationalPresentation) : Bool :=
  PrimitiveRationalCertificate.checkGrid c && checkSource c P && checkTarget c Q

@[simp] theorem checkFrame_eq_true (c : RationalCertificate) (P Q : RationalPresentation) :
    checkFrame c P Q = true ↔
      0 < c.1 ∧ StrictMono c.2.labels ∧
        Str.IsIso c.2.source.toStr P.toStr c.2.labels ∧
        Str.IsIso c.2.target.toStr Q.toStr c.2.labels := by
  simp only [checkFrame, Bool.and_eq_true, PrimitiveRationalCertificate.checkGrid_eq_true,
    checkSource_eq_true, checkTarget_eq_true, and_assoc]

theorem checkFrame_primrec :
    Primrec (fun x : RationalCertificate × RationalPresentation × RationalPresentation =>
      checkFrame x.1 x.2.1 x.2.2) :=
  Primrec.and.comp
    (Primrec.and.comp (PrimitiveRationalCertificate.checkGrid_primrec.comp Primrec.fst)
      (checkSource_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (checkTarget_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

/-- The original witness check splits into the certified frame and the
supplied finite derivation check. -/
theorem witness_check_eq (finiteCheck : ∀ n, PatternCode n → PatternCode n → ℕ → Bool)
    (c : RationalCertificate) (P Q : RationalPresentation) :
    c.2.check (finiteCheck c.1) P Q =
      (checkFrame c P Q && finiteCheck c.1 c.2.source c.2.target c.2.derivation) := by
  rw [Bool.eq_iff_iff, RationalWitness.check_eq_true, Bool.and_eq_true, checkFrame_eq_true]
  simp only [and_assoc]

/-- The complete natural-number recognizer is primitive recursive on every
raw certificate code once its finite derivation check is primitive recursive
uniformly in the grid size. Failed decoding is included. -/
theorem checkCertificate_primrec
    {finiteCheck : ∀ n, PatternCode n → PatternCode n → ℕ → Bool}
    (hfinite : Primrec (fun c : RationalCertificate =>
      finiteCheck c.1 c.2.source c.2.target c.2.derivation)) :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkCertificate finiteCheck x.1.1 x.1.2 x.2) := by
  have hstep : Primrec₂ (fun (x : (RationalPresentation × RationalPresentation) × ℕ)
      (c : RationalCertificate) =>
        checkFrame c x.1.1 x.1.2 && finiteCheck c.1 c.2.source c.2.target c.2.derivation) :=
    Primrec.and.comp
      (checkFrame_primrec.comp (Primrec.snd.pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
      (hfinite.comp Primrec.snd)
  refine (Primrec.option_getD.comp
    (Primrec.option_map (Primrec.decode.comp Primrec.snd) hstep)
    (Primrec.const false)).of_eq ?_
  intro x
  unfold RationalPresentation.checkCertificate
  split
  next h =>
    rw [h]
    rfl
  next c h =>
    rw [h]
    exact (witness_check_eq finiteCheck c x.1.1 x.1.2).symm

/-- Conditional certification of rational generating-rule recognition. -/
theorem checkRule_primrec_of_finite
    (h : Primrec (fun c : RationalCertificate =>
      Alexander313.Carlson.Finite.checkRule c.2.source c.2.target c.2.derivation)) :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkRule x.1.1 x.1.2 x.2) :=
  checkCertificate_primrec (finiteCheck := fun n => @Alexander313.Carlson.Finite.checkRule n) h

/-- Conditional certification of rational exact-chain recognition. -/
theorem checkChain_primrec_of_finite
    (h : Primrec (fun c : RationalCertificate =>
      Alexander313.Carlson.Finite.checkChain c.2.source c.2.target c.2.derivation)) :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkChain x.1.1 x.1.2 x.2) :=
  checkCertificate_primrec (finiteCheck := fun n => @Alexander313.Carlson.Finite.checkChain n) h

/-- Conditional certification of rational generation recognition. -/
theorem checkGeneration_primrec_of_finite
    (h : Primrec (fun c : RationalCertificate =>
      Alexander313.Carlson.Finite.checkGeneration c.2.source c.2.target c.2.derivation)) :
    Primrec (fun x : (RationalPresentation × RationalPresentation) × ℕ =>
      RationalPresentation.checkGeneration x.1.1 x.1.2 x.2) :=
  checkCertificate_primrec
    (finiteCheck := fun n => @Alexander313.Carlson.Finite.checkGeneration n) h

/-- One machine checks the source endpoint of every typed certificate
against every presentation. -/
theorem source_check_program : ∃ p : Nat.Partrec.Code,
    ∀ (c : RationalCertificate) (P : RationalPresentation),
      p.eval (Nat.pair (encode c) (encode P)) = Part.some (encode (checkSource c P)) := by
  obtain ⟨p, hp⟩ := PrimitiveRationalPresentation.exists_code checkSource_primrec
  exact ⟨p, fun c P => hp (c, P)⟩

/-- One machine checks the whole grid and both endpoint isomorphisms. -/
theorem frame_check_program : ∃ p : Nat.Partrec.Code,
    ∀ (c : RationalCertificate) (P Q : RationalPresentation),
      p.eval (encode (c, P, Q)) = Part.some (encode (checkFrame c P Q)) := by
  obtain ⟨p, hp⟩ := PrimitiveRationalPresentation.exists_code checkFrame_primrec
  exact ⟨p, fun c P Q => hp (c, P, Q)⟩

/-- A certified finite rule checker would yield one total machine for
rational rule recognition on every raw certificate code. -/
theorem checkRule_program_of_finite
    (h : Primrec (fun c : RationalCertificate =>
      Alexander313.Carlson.Finite.checkRule c.2.source c.2.target c.2.derivation)) :
    ∃ p : Nat.Partrec.Code, ∀ (P Q : RationalPresentation) (code : ℕ),
      p.eval (encode ((P, Q), code)) =
        Part.some (encode (RationalPresentation.checkRule P Q code)) := by
  obtain ⟨p, hp⟩ := PrimitiveRationalPresentation.exists_code (checkRule_primrec_of_finite h)
  exact ⟨p, fun P Q code => hp ((P, Q), code)⟩

end Alexander313.Carlson.PrimitiveEndpointIso
