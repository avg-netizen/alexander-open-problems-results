import Alexander313.Carlson.PartialPointedComparison

/-!
# A total effective pointed presentation of the common core

Decode the existing rational-presentation/point product codec, check both
patternhood and carrier membership, and replace invalid data by one fixed
pointed singleton. Every natural number now denotes a genuine pointed
pattern. Every pointed pattern occurs, including presentations with arbitrary
off-carrier edges. The five actual core comparisons have one total machine
on all pairs of natural codes. This presentation still has duplicates.
-/

namespace Alexander313.Carlson.ComputablePointedPresentation

open Finite

abbrev Data := RationalPresentation × ℚ

/-- Validity uses the existing pattern checker and actual carrier membership. -/
def Valid (d : Data) : Prop := d.1.checkPattern = true ∧ d.2 ∈ d.1.U

instance (d : Data) : Decidable (Valid d) :=
  inferInstanceAs (Decidable (d.1.checkPattern = true ∧ d.2 ∈ d.1.U))

theorem valid_primrec : PrimrecPred Valid :=
  ((Primrec.eq.comp
    (PrimitiveRationalExactness.checkPattern_primrec.comp Primrec.fst)
    (Primrec.const true)).and
    (PrimitiveFiniteData.finset_mem.comp Primrec.snd
      (PrimitiveRationalPresentation.carrier_primrec.comp Primrec.fst))).of_eq
    fun _ => Iff.rfl

/-- A fixed valid replacement, not a semantic choice of an ordinal label. -/
def fallback : Data := (⟨{0}, {(0, 0)}, {(0, 0)}⟩, 0)

theorem fallback_valid : Valid fallback := by decide

/-- Failed decoding and decoded but invalid presentations are distinguished
before both are replaced by the same fixed valid data. -/
def rawData (n : ℕ) : Data := (Encodable.decode n).getD fallback

def data (n : ℕ) : Data := if Valid (rawData n) then rawData n else fallback

theorem rawData_primrec : Primrec rawData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const fallback)

theorem data_primrec : Primrec data :=
  Primrec.ite (valid_primrec.comp rawData_primrec) rawData_primrec (Primrec.const fallback)

theorem data_valid (n : ℕ) : Valid (data n) := by
  unfold data
  split
  · assumption
  · exact fallback_valid

def point (n : ℕ) : PointedPattern :=
  ⟨⟨(data n).1, (RationalPresentation.checkPattern_eq_true _).mp (data_valid n).1⟩,
    (data n).2, (data_valid n).2⟩

def encodePoint (p : PointedPattern) : ℕ := Encodable.encode (p.seed.val, p.point)

theorem data_encodePoint (p : PointedPattern) :
    data (encodePoint p) = (p.seed.val, p.point) := by
  have hv : Valid (p.seed.val, p.point) :=
    ⟨(RationalPresentation.checkPattern_eq_true _).mpr p.seed.property, p.mem⟩
  simp only [data, rawData, encodePoint, Encodable.encodek, Option.getD_some, if_pos hv]

private theorem pointed_ext (p q : PointedPattern)
    (h : (p.seed.val, p.point) = (q.seed.val, q.point)) : p = q := by
  have hs : p.seed = q.seed := Subtype.ext (congrArg Prod.fst h)
  have hx : p.point = q.point := congrArg Prod.snd h
  cases p
  cases q
  cases hs
  cases hx
  rfl

theorem point_encodePoint (p : PointedPattern) : point (encodePoint p) = p := by
  apply pointed_ext (point (encodePoint p)) p
  dsimp only [point]
  rw [data_encodePoint]

theorem point_surjective : Function.Surjective point :=
  fun p => ⟨encodePoint p, point_encodePoint p⟩

/-- The semantic interpretation is used only in correctness proofs. -/
noncomputable def label (n : ℕ) : Ordinal.{0} := (point n).iota

theorem label_lt_coreBound (n : ℕ) : label n < coreBound := (point n).lt_coreBound

theorem label_surjective (a : Ordinal.{0}) (ha : a < coreBound) :
    ∃ n, label n = a := by
  obtain ⟨p, hp⟩ := (corePoint_iff_pointed a).mp ((corePoint_iff_lt_coreBound a).mpr ha)
  exact ⟨encodePoint p, by simpa only [label, point_encodePoint] using hp⟩

abbrev Answers := PartialPointedComparison.Answers

/-- All five answers are computed from finite data, with termination supplied
by the existing amalgamation theorem for the validated pointed inputs. -/
def comparison (m n : ℕ) : Answers :=
  PartialPointedComparison.answers (PointedPattern.compare (point m) (point n))

theorem comparison_computable : Computable₂ comparison := by
  have hi : Primrec (fun s : ℕ × ℕ => (data s.1, data s.2)) :=
    (data_primrec.comp Primrec.fst).pair (data_primrec.comp Primrec.snd)
  have h := PartialPointedComparison.compare_partrec.comp hi.to_comp
  exact h.of_eq fun s => PartialPointedComparison.compare_eq (point s.1) (point s.2)

theorem comparison_correct (m n : ℕ) :
    ((comparison m n).1 = true ↔ label m = label n) ∧
    ((comparison m n).2.1 = true ↔ label m ≤ label n) ∧
    ((comparison m n).2.2.1 = true ↔ label m < label n) ∧
    ((comparison m n).2.2.2.1 = true ↔ R1 (label m) (label n)) ∧
    ((comparison m n).2.2.2.2 = true ↔ R2 (label m) (label n)) :=
  PointedPattern.compare_correct (point m) (point n)

/-- A total equality algorithm on natural codes for actual core labels. -/
def same (m n : ℕ) : Bool := (comparison m n).1

theorem same_computable : Computable₂ same :=
  Computable.fst.comp comparison_computable

theorem same_eq_true (m n : ℕ) : same m n = true ↔ label m = label n :=
  (comparison_correct m n).1

theorem same_self (n : ℕ) : same n n = true := (same_eq_true n n).mpr rfl

/-- One machine terminates on every natural pair, including codes with failed
decoding, nonpatterns and off-carrier distinguished points. -/
theorem comparison_program : ∃ machine : Nat.Partrec.Code, ∀ m n : ℕ,
    machine.eval (Nat.pair m n) = Part.some (Encodable.encode (comparison m n)) := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp comparison_computable
  refine ⟨machine, fun m n => ?_⟩
  rw [hm]
  change (Part.bind (Part.ofOption (Encodable.decode (Encodable.encode (m, n))))
    (fun s : ℕ × ℕ => (Part.some (comparison s.1 s.2)).map Encodable.encode)) = _
  simp only [Encodable.encodek, Part.ofOption, Part.bind_some, Part.map_some]

/-- Decoder failure has an explicit, deterministic interpretation. -/
theorem data_of_decode_none {n : ℕ} (h : Encodable.decode (α := Data) n = none) :
    data n = fallback := by
  simp [data, rawData, h, fallback_valid]

/-- A well-formed code with invalid pointed data is also replaced, not sent
to the potentially diverging amalgamation search on nonpatterns. -/
theorem data_of_invalid (d : Data) (h : ¬ Valid d) :
    data (Encodable.encode d) = fallback := by
  simp [data, rawData, h]

end Alexander313.Carlson.ComputablePointedPresentation
