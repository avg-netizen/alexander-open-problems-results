import Alexander313.Carlson.GeneratingSequence

/-!
# Coverings and well-foundedness of generating-sequence unions

Carlson, *Patterns of resemblance of order 2*, Lemma 14.8(3--4, 6),
pure case. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 60--61 of the author's October 16, 2008 manuscript.

Successive validity extends a prescribed ordinal covering to a coherent
sequence of coverings. Agreement on earlier carriers makes their union
well-defined. The resulting map is strictly increasing and carries both
union relations forward. Consequently a generating sequence with a
covered stage has a well-founded limit order, order-isomorphic to an
ordinal. The extension theorem allows the prescribed covering to start
at any stage, strengthening the stage-zero statement by passage to a tail.

Every covering of a finite structure into the union is already a
covering into some finite stage. Finite-chain rigidity then implies
that a covering of a covered stage into the union cannot move any old
point downward. No fairness hypothesis or coveredness of all abstract
patterns is used.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

universe u

variable {α : Type u} [LinearOrder α]

/-- Coherent ordinal coverings of the tail beginning at stage `n`.
Only agreement on the old carrier is required; values elsewhere in the
ambient order have no structural significance. -/
structure CoveringThread (S : GeneratingSequence α) (n : ℕ) where
  map : ℕ → α → Ordinal.{0}
  covering : ∀ i, Str.CoveringR (S.stage (n + i)) (map i)
  compatible : ∀ i, Str.Extends (S.stage (n + i)) (map i) (map (i + 1))

private def nextCovering (S : GeneratingSequence α) (n i : ℕ)
    (p : {g : α → Ordinal.{0} // Str.CoveringR (S.stage (n + i)) g}) :
    {g : α → Ordinal.{0} // Str.CoveringR (S.stage (n + (i + 1))) g} :=
  ⟨Classical.choose ((S.step (n + i)).valid.2 p.val p.property), by
    simpa only [Nat.add_assoc] using
      (Classical.choose_spec ((S.step (n + i)).valid.2 p.val p.property)).1⟩

private theorem nextCovering_extends (S : GeneratingSequence α) (n i : ℕ)
    (p : {g : α → Ordinal.{0} // Str.CoveringR (S.stage (n + i)) g}) :
    Str.Extends (S.stage (n + i)) p.val (nextCovering S n i p).val :=
  (Classical.choose_spec ((S.step (n + i)).valid.2 p.val p.property)).2

private def coveringFamily (S : GeneratingSequence α) (n : ℕ)
    (h : α → Ordinal.{0}) (hh : Str.CoveringR (S.stage n) h) :
    (i : ℕ) → {g : α → Ordinal.{0} // Str.CoveringR (S.stage (n + i)) g}
  | 0 => ⟨h, by simpa only [Nat.add_zero] using hh⟩
  | i + 1 => nextCovering S n i (coveringFamily S n h hh i)

/-- Recursively extend the supplied covering using the validity of each
generating rule. This construction makes no independent covering choices
at different stages. -/
def CoveringThread.extend (S : GeneratingSequence α) (n : ℕ)
    (h : α → Ordinal.{0}) (hh : Str.CoveringR (S.stage n) h) : CoveringThread S n where
  map i := (coveringFamily S n h hh i).val
  covering i := (coveringFamily S n h hh i).property
  compatible i := nextCovering_extends S n i (coveringFamily S n h hh i)

@[simp]
theorem CoveringThread.extend_map_zero (S : GeneratingSequence α) (n : ℕ)
    (h : α → Ordinal.{0}) (hh : Str.CoveringR (S.stage n) h) :
    (CoveringThread.extend S n h hh).map 0 = h := rfl

namespace CoveringThread

variable {S : GeneratingSequence α} {n : ℕ} (C : CoveringThread S n)

/-- Successor agreement propagates through any finite interval. -/
theorem map_eq_of_le {i j : ℕ} (hij : i ≤ j) {x : α}
    (hx : x ∈ (S.stage (n + i)).U) : C.map j x = C.map i x := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
      exact (C.compatible j x (S.mem_mono (Nat.add_le_add_left hij n) hx)).trans ih

/-- Any two stage maps agree at every point belonging to both carriers. -/
theorem map_eq {i j : ℕ} {x : α}
    (hi : x ∈ (S.stage (n + i)).U) (hj : x ∈ (S.stage (n + j)).U) :
    C.map i x = C.map j x :=
  (C.map_eq_of_le (Nat.le_max_left i j) hi).symm.trans
    (C.map_eq_of_le (Nat.le_max_right i j) hj)

private def entryStage (x : S.Limit) : ℕ := Classical.choose x.property

private theorem mem_entryStage (x : S.Limit) :
    x.val ∈ (S.stage (entryStage x)).U := Classical.choose_spec x.property

/-- Evaluate a coherent family at any chosen stage containing the point.
`limitMap_eq` proves independence of that choice. -/
def limitMap (x : S.Limit) : Ordinal.{0} := C.map (entryStage x) x.val

/-- The union map agrees with each covering on its whole carrier. -/
theorem limitMap_eq (i : ℕ) (x : S.Limit)
    (hx : x.val ∈ (S.stage (n + i)).U) : C.limitMap x = C.map i x.val := by
  exact C.map_eq (S.mem_mono (by omega) (mem_entryStage x)) hx

/-- Every pair of points lies in a common tail stage, where the covering
is strictly increasing. -/
theorem strictMono : StrictMono C.limitMap := by
  intro x y hxy
  obtain ⟨i, hi⟩ := x.property
  obtain ⟨j, hj⟩ := y.property
  have hx : x.val ∈ (S.stage (n + max i j)).U := S.mem_mono (by omega) hi
  have hy : y.val ∈ (S.stage (n + max i j)).U := S.mem_mono (by omega) hj
  rw [C.limitMap_eq (max i j) x hx, C.limitMap_eq (max i j) y hy]
  exact (C.covering (max i j)).1 x.val hx y.val hy hxy

/-- The first union relation is preserved by the coherent ordinal map. -/
theorem preserves_one {x y : S.Limit} (hxy : S.limitRel .one x y) :
    R1 (C.limitMap x) (C.limitMap y) := by
  obtain ⟨i, hi, hj, hrel⟩ := hxy
  have hs := S.isSub (show i ≤ n + i by omega)
  have hx := hs.1 hi
  have hy := hs.1 hj
  rw [C.limitMap_eq i x hx, C.limitMap_eq i y hy]
  exact (C.covering i).2.1 x.val hx y.val hy ((hs.rel_iff hi hj .one).mp hrel)

/-- The second union relation is preserved by the same ordinal map. -/
theorem preserves_two {x y : S.Limit} (hxy : S.limitRel .two x y) :
    R2 (C.limitMap x) (C.limitMap y) := by
  obtain ⟨i, hi, hj, hrel⟩ := hxy
  have hs := S.isSub (show i ≤ n + i by omega)
  have hx := hs.1 hi
  have hy := hs.1 hj
  rw [C.limitMap_eq i x hx, C.limitMap_eq i y hy]
  exact (C.covering i).2.2 x.val hx y.val hy ((hs.rel_iff hi hj .two).mp hrel)

end CoveringThread

/-- An ordinal covering of the union: strict order preservation and
forward preservation of both Carlson relations on the limit carrier. -/
def LimitCoveringR (S : GeneratingSequence α) (f : S.Limit → Ordinal.{0}) : Prop :=
  StrictMono f ∧
  (∀ x y, S.limitRel .one x y → R1 (f x) (f y)) ∧
  (∀ x y, S.limitRel .two x y → R2 (f x) (f y))

theorem CoveringThread.limitCoveringR {S : GeneratingSequence α} {n : ℕ}
    (C : CoveringThread S n) : S.LimitCoveringR C.limitMap :=
  ⟨C.strictMono, fun _ _ => C.preserves_one, fun _ _ => C.preserves_two⟩

variable (S : GeneratingSequence α)

/-- Lemma 14.8(3), including any initial stage: every prescribed ordinal
covering extends to a covering of the complete union. -/
theorem exists_limitCovering_extension (n : ℕ) (h : α → Ordinal.{0})
    (hh : Str.CoveringR (S.stage n) h) :
    ∃ f : S.Limit → Ordinal.{0}, S.LimitCoveringR f ∧
      ∀ (x : α) (hx : x ∈ (S.stage n).U), f ⟨x, S.mem_carrier n hx⟩ = h x := by
  let C := CoveringThread.extend S n h hh
  refine ⟨C.limitMap, C.limitCoveringR, ?_⟩
  intro x hx
  exact (C.limitMap_eq 0 ⟨x, S.mem_carrier n hx⟩
    (by simpa only [Nat.add_zero] using hx)).trans
      (congrFun (CoveringThread.extend_map_zero S n h hh) x)

/-- Coveredness at any stage supplies an ordinal covering of the union. -/
theorem covered_limit {n : ℕ} (hP : Str.Covered (S.stage n)) :
    ∃ f : S.Limit → Ordinal.{0}, S.LimitCoveringR f := by
  obtain ⟨h, hh⟩ := hP
  obtain ⟨f, hf, _⟩ := S.exists_limitCovering_extension n h hh
  exact ⟨f, hf⟩

/-- The strict order on the union is well-founded whenever one stage is
covered. The ambient label order itself need not be well-founded. -/
theorem wellFounded {n : ℕ} (hP : Str.Covered (S.stage n)) :
    WellFounded ((· < ·) : S.Limit → S.Limit → Prop) := by
  obtain ⟨f, hf⟩ := S.covered_limit hP
  exact Subrelation.wf (fun hxy => hf.1 hxy) (InvImage.wf f Ordinal.lt_wf)

/-- Lemma 14.8(4): the limit carrier of a sequence with a covered stage
is order-isomorphic to an ordinal, presented as its strict initial segment. -/
theorem exists_ordinal_orderIso {n : ℕ} (hP : Str.Covered (S.stage n)) :
    ∃ o : Ordinal.{u}, Nonempty (S.Limit ≃o Set.Iio o) := by
  letI : WellFoundedLT S.Limit := ⟨S.wellFounded hP⟩
  exact ⟨Ordinal.type ((· < ·) : S.Limit → S.Limit → Prop),
    ⟨OrderIso.ofRelIsoLT (Ordinal.enum ((· < ·) : S.Limit → S.Limit → Prop)).symm⟩⟩

/-- A covering of a finite structure into the union, expressed on the
ambient label type to match the finite covering API. -/
def CoversIntoLimit (P : Str α) (f : α → α) : Prop :=
  (∀ x ∈ P.U, f x ∈ S.carrier) ∧ Str.IsCovering P (S.rel .one) (S.rel .two) f

/-- Finite source images and relation agreement put every finite
covering into a single finite stage. -/
theorem CoversIntoLimit.exists_stage {P : Str α} {f : α → α}
    (hf : S.CoversIntoLimit P f) : ∃ n, Str.CoversInto P (S.stage n) f := by
  classical
  obtain ⟨n, hn⟩ := S.finite_capture (P.U.image f) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf.1 x hx)
  have himage : ∀ x ∈ P.U, f x ∈ (S.stage n).U :=
    fun x hx => hn (Finset.mem_image_of_mem f hx)
  refine ⟨n, himage, hf.2.1, ?_, ?_⟩
  · intro x hx y hy hrel
    exact (S.rel_iff n (himage x hx) (himage y hy) .one).mp (hf.2.2.1 x hx y hy hrel)
  · intro x hx y hy hrel
    exact (S.rel_iff n (himage x hx) (himage y hy) .two).mp (hf.2.2.2 x hx y hy hrel)

/-- The capturing stage can be chosen beyond any prescribed stage. -/
theorem CoversIntoLimit.exists_stage_ge {P : Str α} {f : α → α}
    (hf : S.CoversIntoLimit P f) (n : ℕ) :
    ∃ m, n ≤ m ∧ Str.CoversInto P (S.stage m) f := by
  obtain ⟨m, hm⟩ := CoversIntoLimit.exists_stage S hf
  have hs := S.isSub (Nat.le_max_right n m)
  refine ⟨max n m, Nat.le_max_left n m, fun x hx => hs.1 (hm.1 x hx), hm.2.1, ?_, ?_⟩
  · intro x hx y hy hrel
    exact (hs.2 (f x) (hm.1 x hx) (f y) (hm.1 y hy)).1.mp (hm.2.2.1 x hx y hy hrel)
  · intro x hx y hy hrel
    exact (hs.2 (f x) (hm.1 x hx) (f y) (hm.1 y hy)).2.mp (hm.2.2.2 x hx y hy hrel)

/-- Lemma 14.8(6), in pointwise covering form: a covering of a covered
stage into the union cannot move any of its points downward. -/
theorem le_of_coversIntoLimit {n : ℕ} (hP : Str.Covered (S.stage n))
    {f : α → α} (hf : S.CoversIntoLimit (S.stage n) f)
    {x : α} (hx : x ∈ (S.stage n).U) : x ≤ f x := by
  obtain ⟨m, hnm, hm⟩ := CoversIntoLimit.exists_stage_ge S hf n
  exact (S.exactlyGenerates hnm).le_of_coversInto hP hm hx

end GeneratingSequence
end Alexander313.Carlson
