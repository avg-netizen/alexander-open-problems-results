import Alexander313.Carlson.ComputableFairLimit

/-!
# A decidable coded carrier for the computed fair limit

A rational point is coded by its first stage of appearance and its canonical
natural-number encoding. Validity is a total finite check: decode the point,
check that re-encoding gives the supplied code, verify membership at the
claimed stage, and exclude every earlier stage. Each point of the union has
exactly one valid code. This removes repeated appearances without deciding
membership of an arbitrary rational in the whole union.

The valid codes carry the rational order, and both relations can be decided
by reading their finite tables at the maximum of the two stored birth stages.
Invalid codes are rejected. The resulting ordered structure is exactly
isomorphic to the limit. Covered initial data therefore make it a well-order
with the actual ordinal relations on its ordinal initial segment.
A strict first-relation edge in a finite stage already forces infinitely
many valid codes, without a coveredness assumption.

This constructs a decidable subset of `Nat`, which may be empty or finite.
It does not assert an enumeration by all of `Nat`, representation of these
algorithms in `Program`, or finite tallness.
-/

namespace Alexander313.Carlson.Finite.ComputableFairCarrier

open ComputableFairSequence

/-- The stage component stored in a natural-number point code. -/
def birthStage (code : ℕ) : ℕ := (Nat.unpair code).1

/-- Decode the rational component. The fallback is rejected by the
canonical-code check unless the supplied code really encodes zero. -/
def value (code : ℕ) : ℚ :=
  (Encodable.decode (α := ℚ) (Nat.unpair code).2).getD 0

/-- A canonical code for a rational point with a claimed birth stage. -/
def encode (n : ℕ) (x : ℚ) : ℕ := Nat.pair n (Encodable.encode x)

@[simp] theorem birthStage_encode (n : ℕ) (x : ℚ) :
    birthStage (encode n x) = n := by
  simp only [birthStage, encode, Nat.unpair_pair]

@[simp] theorem value_encode (n : ℕ) (x : ℚ) : value (encode n x) = x := by
  simp only [value, encode, Nat.unpair_pair, Encodable.encodek, Option.getD_some]

/-- Check a canonical first-appearance code using only finite computations.
The round-trip check excludes any redundant or malformed rational encoding. -/
def valid (P : RationalPresentation) (code : ℕ) : Bool :=
  decide (encode (birthStage code) (value code) = code ∧
    value code ∈ (stage P (birthStage code)).U ∧
    containsBelow P (value code) (birthStage code) = false)

@[simp] theorem valid_eq_true (P : RationalPresentation) (code : ℕ) :
    valid P code = true ↔
      encode (birthStage code) (value code) = code ∧
      value code ∈ (stage P (birthStage code)).U ∧
      containsBelow P (value code) (birthStage code) = false := by
  simp only [valid, decide_eq_true_eq]

/-- Initial points have their canonical valid codes at stage zero. -/
@[simp] theorem valid_encode_zero (P : RationalPresentation) (x : ℚ) :
    valid P (encode 0 x) = true ↔ x ∈ P.U := by
  simp only [valid_eq_true, birthStage_encode, value_encode, stage_zero,
    containsBelow_zero, true_and, and_true]

/-- The point of a valid code is present at its stored stage. -/
theorem mem_birthStage {P : RationalPresentation} {code : ℕ}
    (h : valid P code = true) : value code ∈ (stage P (birthStage code)).U :=
  ((valid_eq_true P code).mp h).2.1

/-- No valid code's point occurs before its stored stage. -/
theorem not_mem_before {P : RationalPresentation} {code n : ℕ}
    (h : valid P code = true) (hn : n < birthStage code) :
    value code ∉ (stage P n).U := by
  intro hx
  have htrue := (containsBelow_eq_true P (value code) (birthStage code)).mpr
    ⟨n, hn, hx⟩
  rw [((valid_eq_true P code).mp h).2.2] at htrue
  exact Bool.false_ne_true htrue

/-- The birth stage is no later than any stage containing the point. -/
theorem birthStage_le {P : RationalPresentation} {code n : ℕ}
    (h : valid P code = true) (hx : value code ∈ (stage P n).U) :
    birthStage code ≤ n :=
  le_of_not_gt (fun hn => not_mem_before h hn hx)

/-- Canonical first appearances remove all duplicate codes for a point.
This does not require monotonicity or even patternhood of the input. -/
theorem value_injective {P : RationalPresentation} {a b : ℕ}
    (ha : valid P a = true) (hb : valid P b = true) (hvalue : value a = value b) :
    a = b := by
  have hab : birthStage a ≤ birthStage b :=
    birthStage_le ha (hvalue.symm ▸ mem_birthStage hb)
  have hba : birthStage b ≤ birthStage a :=
    birthStage_le hb (hvalue ▸ mem_birthStage ha)
  have hstage : birthStage a = birthStage b := hab.antisymm hba
  calc
    a = encode (birthStage a) (value a) := ((valid_eq_true P a).mp ha).1.symm
    _ = encode (birthStage b) (value b) := by rw [hstage, hvalue]
    _ = b := ((valid_eq_true P b).mp hb).1

/-- Find the first appearance of a point known to occur. The witness is
used to justify termination of the least-stage search. -/
def firstCode (P : RationalPresentation) (x : ℚ)
    (hx : ∃ n, x ∈ (stage P n).U) : ℕ :=
  encode (Nat.find hx) x

@[simp] theorem value_firstCode (P : RationalPresentation) (x : ℚ)
    (hx : ∃ n, x ∈ (stage P n).U) : value (firstCode P x hx) = x :=
  value_encode _ _

/-- The least occurrence always supplies a valid code. -/
theorem valid_firstCode (P : RationalPresentation) (x : ℚ)
    (hx : ∃ n, x ∈ (stage P n).U) : valid P (firstCode P x hx) = true := by
  rw [valid_eq_true]
  simp only [firstCode, birthStage_encode, value_encode, true_and]
  refine ⟨Nat.find_spec hx, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨n, hn, hmem⟩ := (containsBelow_eq_true P x (Nat.find hx)).mp h
  exact Nat.find_min hx hn hmem

/-- Exactly the points of the generated union have a unique valid code. -/
theorem mem_limit_iff_existsUnique (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (x : ℚ) :
    x ∈ (toGeneratingSequence P hP).carrier ↔
      ∃! code, valid P code = true ∧ value code = x := by
  constructor
  · intro hx
    refine ⟨firstCode P x hx, ⟨valid_firstCode P x hx, value_firstCode P x hx⟩, ?_⟩
    intro code hc
    exact value_injective hc.1 (valid_firstCode P x hx)
      (hc.2.trans (value_firstCode P x hx).symm)
  · rintro ⟨code, ⟨hvalid, rfl⟩, _⟩
    exact ⟨birthStage code, mem_birthStage hvalid⟩

/-- The decidable subset of natural-number codes, before any assumption
that the limit is infinite. Its order is defined from rational values below. -/
structure Label (P : RationalPresentation) where
  code : ℕ
  isValid : valid P code = true
  deriving DecidableEq

namespace Label

variable {P : RationalPresentation}

@[ext] theorem ext {a b : Label P} (h : a.code = b.code) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem value_injective : Function.Injective (fun a : Label P => value a.code) := by
  intro a b h
  exact ext (ComputableFairCarrier.value_injective a.isValid b.isValid h)

/-- Codes are ordered by their rational points, independently of their
numerical encodings or order of appearance. -/
instance instLinearOrder : LinearOrder (Label P) :=
  LinearOrder.lift' (fun a : Label P => value a.code) value_injective

end Label

/-- Interpret a valid code as a point of the actual computed union. -/
def toLimit (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (a : Label P) : (toGeneratingSequence P hP).Limit :=
  ⟨value a.code, birthStage a.code, mem_birthStage a.isValid⟩

/-- Code a union point at its first occurrence. -/
def ofLimit (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (x : (toGeneratingSequence P hP).Limit) : Label P :=
  ⟨firstCode P x.val x.property, valid_firstCode P x.val x.property⟩

@[simp] theorem toLimit_ofLimit (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (x : (toGeneratingSequence P hP).Limit) : toLimit P hP (ofLimit P hP x) = x := by
  apply Subtype.ext
  simp only [toLimit, ofLimit, value_firstCode]

@[simp] theorem ofLimit_toLimit (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (a : Label P) : ofLimit P hP (toLimit P hP a) = a := by
  apply Label.value_injective
  exact value_firstCode P (value a.code) (toLimit P hP a).property

/-- The first-appearance codes present the entire ordered limit exactly. -/
def limitOrderIso (P : RationalPresentation) (hP : P.toStr.IsPattern) :
    Label P ≃o (toGeneratingSequence P hP).Limit where
  toFun := toLimit P hP
  invFun := ofLimit P hP
  left_inv := ofLimit_toLimit P hP
  right_inv := toLimit_ofLimit P hP
  map_rel_iff' := by intro a b; rfl

@[simp] theorem limitOrderIso_apply (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (a : Label P) : limitOrderIso P hP a = toLimit P hP a := rfl

/-- A total comparison on raw codes. Invalid endpoints are rejected. -/
def less (P : RationalPresentation) (a b : ℕ) : Bool :=
  valid P a && valid P b && decide (value a < value b)

@[simp] theorem less_eq_true (P : RationalPresentation) (a b : ℕ) :
    less P a b = true ↔ valid P a = true ∧ valid P b = true ∧ value a < value b := by
  simp only [less, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

@[simp] theorem less_labels (P : RationalPresentation) (a b : Label P) :
    less P a.code b.code = true ↔ a < b := by
  simp only [less_eq_true, a.isValid, b.isValid, true_and]
  rfl

/-- Read the chosen relation from one finite stage containing both valid
endpoints. The bound is computed directly from their stored birth stages. -/
def relates (P : RationalPresentation) (level : Lvl) (a b : ℕ) : Bool :=
  valid P a && valid P b &&
    let Q := stage P (max (birthStage a) (birthStage b))
    match level with
    | .one => decide ((value a, value b) ∈ Q.r₁)
    | .two => decide ((value a, value b) ∈ Q.r₂)

@[simp] theorem relates_eq_true_iff_stage (P : RationalPresentation) (level : Lvl)
    (a b : ℕ) :
    relates P level a b = true ↔
      valid P a = true ∧ valid P b = true ∧
      (stage P (max (birthStage a) (birthStage b))).toStr.rel level (value a) (value b) := by
  cases level <;>
    simp only [relates, Bool.and_eq_true, decide_eq_true_eq, and_assoc,
      Str.rel, RationalPresentation.toStr]

/-- Both valid points are already captured at the computable common stage. -/
theorem mem_commonStage (P : RationalPresentation) (hP : P.toStr.IsPattern)
    {a b : ℕ} (ha : valid P a = true) (hb : valid P b = true) :
    value a ∈ (stage P (max (birthStage a) (birthStage b))).U ∧
      value b ∈ (stage P (max (birthStage a) (birthStage b))).U :=
  ⟨(toGeneratingSequence P hP).mem_mono (Nat.le_max_left _ _) (mem_birthStage ha),
    (toGeneratingSequence P hP).mem_mono (Nat.le_max_right _ _) (mem_birthStage hb)⟩

/-- The total finite-stage query decides the actual union relation between
valid codes, including negative answers. -/
theorem relates_eq_true (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (level : Lvl) (a b : ℕ) :
    relates P level a b = true ↔ valid P a = true ∧ valid P b = true ∧
      (toGeneratingSequence P hP).rel level (value a) (value b) := by
  rw [relates_eq_true_iff_stage]
  constructor
  · rintro ⟨ha, hb, hr⟩
    obtain ⟨hx, hy⟩ := mem_commonStage P hP ha hb
    exact ⟨ha, hb, ((toGeneratingSequence P hP).rel_iff _ hx hy level).mpr hr⟩
  · rintro ⟨ha, hb, hr⟩
    obtain ⟨hx, hy⟩ := mem_commonStage P hP ha hb
    exact ⟨ha, hb, ((toGeneratingSequence P hP).rel_iff _ hx hy level).mp hr⟩

/-- The order isomorphism also preserves and reflects both coded relations. -/
theorem relates_labels (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (level : Lvl) (a b : Label P) :
    relates P level a.code b.code = true ↔
      (toGeneratingSequence P hP).limitRel level
        (limitOrderIso P hP a) (limitOrderIso P hP b) := by
  simpa only [GeneratingSequence.limitRel, limitOrderIso_apply, toLimit,
    a.isValid, b.isValid, true_and] using relates_eq_true P hP level a.code b.code

/-- A strict first-relation edge in any finite stage forces infinitely
many valid codes. Fairness copies a singleton below its lower endpoint,
then copies two-point sets to find a still higher point below that endpoint.
Coveredness is not needed for this infinitude statement. -/
theorem infinite_of_stage_first (P : RationalPresentation) (hP : P.toStr.IsPattern)
    {n : ℕ} {a b : ℚ} (ha : a ∈ (stage P n).U) (hb : b ∈ (stage P n).U)
    (hab : a < b) (hr : (a, b) ∈ (stage P n).r₁) : Infinite (Label P) := by
  classical
  let S := toGeneratingSequence P hP
  let x : S.Limit := ⟨a, n, ha⟩
  let y : S.Limit := ⟨b, n, hb⟩
  have hxy : x < y := hab
  have hrel : S.limitRel .one x y := ⟨n, ha, hb, hr⟩
  have hfirst := (fair P hP).firstCondition hrel
  obtain ⟨f, hf⟩ := hfirst {x} (by
    intro z hz
    rcases Finset.mem_singleton.mp hz with rfl
    exact hxy)
  letI : Nonempty (Set.Iio x) := ⟨⟨f x, hf.1 x (by simp)⟩⟩
  letI : NoMaxOrder (Set.Iio x) := ⟨fun z => by
    obtain ⟨g, hg⟩ := hfirst {z.val, x} (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact z.property.trans hxy
      · rcases Finset.mem_singleton.mp hw with rfl
        exact hxy)
    refine ⟨⟨g x, hg.1 x (by simp)⟩, ?_⟩
    change z.val < g x
    have hlt := hg.2.2.1 z.val (by simp) x (by simp) z.property
    rwa [hg.2.1 z.val (by simp) z.property] at hlt⟩
  obtain ⟨g, hg⟩ := Nat.exists_strictMono (Set.Iio x)
  have hinfinite : Infinite S.Limit :=
    Infinite.of_injective (fun n => (g n).val) (Subtype.val_injective.comp hg.injective)
  exact (limitOrderIso P hP).toEquiv.infinite_iff.mpr hinfinite

/-- In particular, a strict first edge in the supplied seed guarantees
that its decidable code domain is infinite. -/
theorem infinite_of_initial_first (P : RationalPresentation) (hP : P.toStr.IsPattern)
    {a b : ℚ} (ha : a ∈ P.U) (hb : b ∈ P.U) (hab : a < b)
    (hr : (a, b) ∈ P.r₁) : Infinite (Label P) :=
  infinite_of_stage_first P hP (n := 0) ha hb hab hr

/-- Covered initial data make the decidable code order well-founded. -/
theorem wellFounded (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (hcovered : Str.Covered P.toStr) :
    WellFounded ((· < ·) : Label P → Label P → Prop) :=
  Subrelation.wf (fun h => (limitOrderIso P hP).strictMono h)
    (InvImage.wf (limitOrderIso P hP) ((toGeneratingSequence P hP).wellFounded
      (n := 0) hcovered))

/-- The valid natural-number codes present an exact ordinal initial
segment, including both actual ordinal relations. This is the semantic
consequence of coveredness, not an algorithm computing ordinal values. -/
theorem exists_ordinalRealization (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (hcovered : Str.Covered P.toStr) :
    ∃ (bound : Ordinal.{0}) (e : Label P ≃o Set.Iio bound),
      (∀ a b, relates P .one a.code b.code = true ↔ R1 (e a).val (e b).val) ∧
      (∀ a b, relates P .two a.code b.code = true ↔ R2 (e a).val (e b).val) := by
  obtain ⟨R⟩ := ordinalRealization P hP hcovered
  refine ⟨R.bound, (limitOrderIso P hP).trans R.orderIso, ?_, ?_⟩
  · intro a b
    exact (relates_labels P hP .one a b).trans (R.one _ _)
  · intro a b
    exact (relates_labels P hP .two a b).trans (R.two _ _)

end Alexander313.Carlson.Finite.ComputableFairCarrier
