import Alexander313.Carlson.GeneratingSequenceCovering

/-!
# Ordinal realizations of generating-sequence limits

An ordinal realization identifies both relations of the limit, as well as
its order, with an initial segment of Carlson's ordinal structure. The
existence theorem for covered fair rational sequences is supplied separately.

Given such a realization, this module proves Carlson's Lemma 14.9(1--4),
pure case: every finite stage is isominimal, the ordinal limit is the least
strict bound of each stage, and neither ordinal relation can leave the
limit. Source:
https://people.math.osu.edu/carlson.6/research/patternstwofinal.pdf,
printed pp. 66--67 of the author's October 16, 2008 manuscript.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {α : Type*} [LinearOrder α]

/-- An exact realization of the limit as an initial ordinal structure. -/
structure OrdinalRealization (S : GeneratingSequence α) where
  bound : Ordinal.{0}
  orderIso : S.Limit ≃o Set.Iio bound
  one : ∀ x y, S.limitRel .one x y ↔ R1 (orderIso x).val (orderIso y).val
  two : ∀ x y, S.limitRel .two x y ↔ R2 (orderIso x).val (orderIso y).val

namespace OrdinalRealization

variable {S : GeneratingSequence α} (R : OrdinalRealization S)

/-- The ordinal value of a point of the limit. -/
def toOrdinal (x : S.Limit) : Ordinal.{0} := (R.orderIso x).val

/-- A total label map which agrees with the realization on its carrier.
The value zero outside the carrier has no structural significance. -/
def label (x : α) : Ordinal.{0} := by
  classical
  exact if hx : x ∈ S.carrier then R.toOrdinal ⟨x, hx⟩ else 0

theorem label_eq (x : S.Limit) : R.label x.val = R.toOrdinal x := by
  simp only [label, dif_pos x.property]

theorem toOrdinal_strictMono : StrictMono R.toOrdinal :=
  R.orderIso.strictMono

theorem toOrdinal_lt_bound (x : S.Limit) : R.toOrdinal x < R.bound :=
  (R.orderIso x).property

theorem label_lt_bound {x : α} (hx : x ∈ S.carrier) : R.label x < R.bound := by
  rw [R.label_eq ⟨x, hx⟩]
  exact R.toOrdinal_lt_bound ⟨x, hx⟩

/-- A strictly increasing map from an ordinal initial segment into the
ordinals is pointwise at least the inclusion map. -/
private theorem initial_segment_le_map {o : Ordinal.{0}}
    (f : Set.Iio o → Ordinal.{0}) (hf : StrictMono f) (x : Set.Iio o) :
    x.val ≤ f x := by
  have h : ∀ z (hz : z < o), z ≤ f ⟨z, hz⟩ := by
    intro z
    refine Ordinal.lt_wf.induction z
      (C := fun z => ∀ hz : z < o, z ≤ f ⟨z, hz⟩) ?_
    intro z ih hz
    apply le_of_forall_lt
    intro y hy
    exact (ih y hy (hy.trans hz)).trans_lt (hf (show
      (⟨y, hy.trans hz⟩ : Set.Iio o) < ⟨z, hz⟩ from hy))
  exact h x.val x.property

/-- The ordinal realization is pointwise no larger than any strictly
increasing ordinal map on the same limit. -/
theorem toOrdinal_le_of_strictMono {f : S.Limit → Ordinal.{0}}
    (hf : StrictMono f) (x : S.Limit) : R.toOrdinal x ≤ f x := by
  have h := initial_segment_le_map (fun z => f (R.orderIso.symm z))
    (hf.comp R.orderIso.symm.strictMono) (R.orderIso x)
  simpa only [toOrdinal, OrderIso.symm_apply_apply] using h

/-- The finite ordinal structure realized by one stage. -/
def stagePattern (n : ℕ) : Str Ordinal.{0} :=
  Str.ofOrdinals ((S.stage n).U.image R.label)

/-- Each finite stage is exactly isomorphic to its induced ordinal image. -/
theorem stage_isIso (n : ℕ) : Str.IsIso (S.stage n) (R.stagePattern n) R.label := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [R.label_eq ⟨x, S.mem_carrier n hx⟩, R.label_eq ⟨y, S.mem_carrier n hy⟩]
    exact R.toOrdinal_strictMono hxy
  · intro x hx y hy
    change ((S.stage n).r₁ x y ↔ R1 (R.label x) (R.label y)) ∧
      ((S.stage n).r₂ x y ↔ R2 (R.label x) (R.label y))
    rw [R.label_eq ⟨x, S.mem_carrier n hx⟩, R.label_eq ⟨y, S.mem_carrier n hy⟩]
    exact ⟨(S.rel_iff n hx hy .one).symm.trans
        (R.one ⟨x, S.mem_carrier n hx⟩ ⟨y, S.mem_carrier n hy⟩),
      (S.rel_iff n hx hy .two).symm.trans
        (R.two ⟨x, S.mem_carrier n hx⟩ ⟨y, S.mem_carrier n hy⟩)⟩

/-- The common realization map covers every stage. -/
theorem stage_covering (n : ℕ) : Str.CoveringR (S.stage n) R.label :=
  ⟨(R.stage_isIso n).2.1,
    fun x hx y hy => ((R.stage_isIso n).2.2 x hx y hy).1.mp,
    fun x hx y hy => ((R.stage_isIso n).2.2 x hx y hy).2.mp⟩

/-- Lemma 14.9(2): among all ordinal coverings of a stage, the realized
stage map is pointwise least. Extend the competing covering to the limit
and use the minimality of the ordinal order type. -/
theorem label_le_covering (n : ℕ) {h : α → Ordinal.{0}}
    (hh : Str.CoveringR (S.stage n) h) {x : α} (hx : x ∈ (S.stage n).U) :
    R.label x ≤ h x := by
  obtain ⟨f, hf, hfix⟩ := S.exists_limitCovering_extension n h hh
  rw [R.label_eq ⟨x, S.mem_carrier n hx⟩, ← hfix x hx]
  exact R.toOrdinal_le_of_strictMono hf.1 _

/-- Ordinal coverings of a realized finite stage are pointwise
inflationary on that stage. -/
theorem stage_le_covering (n : ℕ) {f : Ordinal.{0} → Ordinal.{0}}
    (hf : Str.CoveringR (R.stagePattern n) f)
    {z : Ordinal.{0}} (hz : z ∈ (R.stagePattern n).U) : z ≤ f z := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hmem (y : α) (hy : y ∈ (S.stage n).U) : R.label y ∈ (R.stagePattern n).U :=
    Finset.mem_image_of_mem R.label hy
  have hc := (R.stage_covering n).comp
    (fun y hy w hw hlt => hf.1 _ (hmem y hy) _ (hmem w hw) hlt)
    (fun y hy w hw hrel => hf.2.1 _ (hmem y hy) _ (hmem w hw) hrel)
    (fun y hy w hw hrel => hf.2.2 _ (hmem y hy) _ (hmem w hw) hrel)
  exact R.label_le_covering n hc hx

/-- Lemma 14.9(3), the explicit finite-map form of isominimality:
an isomorphic ordinal image pointwise below a realized stage has the
same carrier. All substructures are closed in the pure language. -/
theorem stage_isominimal (n : ℕ) {T : Finset Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}}
    (e : Str.IsIso (R.stagePattern n) (Str.ofOrdinals T) f)
    (hle : ∀ z ∈ (R.stagePattern n).U, f z ≤ z) : T = (R.stagePattern n).U := by
  have hc : Str.CoveringR (R.stagePattern n) f :=
    ⟨e.2.1, fun x hx y hy => (e.2.2 x hx y hy).1.mp,
      fun x hx y hy => (e.2.2 x hx y hy).2.mp⟩
  have hfix : ∀ z ∈ (R.stagePattern n).U, f z = z :=
    fun z hz => (hle z hz).antisymm (R.stage_le_covering n hc hz)
  calc
    T = (R.stagePattern n).U.image f := e.1.symm
    _ = (R.stagePattern n).U.image id := Finset.image_congr hfix
    _ = (R.stagePattern n).U := Finset.image_id

/-- Lemma 14.9(1): the ordinal limit is the least strict bound of any
fixed stage, including the initial stage and the empty case. -/
theorem bound_le_iff (n : ℕ) (c : Ordinal.{0}) :
    R.bound ≤ c ↔ ∀ x ∈ (S.stage n).U, R.label x < c := by
  constructor
  · intro hc x hx
    exact (R.label_lt_bound (S.mem_carrier n hx)).trans_le hc
  · intro hc
    apply le_of_forall_lt
    intro o ho
    let x : S.Limit := R.orderIso.symm ⟨o, ho⟩
    obtain ⟨p, hp, hxp⟩ := S.bounded n x.property
    have heq : R.toOrdinal x = o := congrArg Subtype.val (R.orderIso.apply_symm_apply ⟨o, ho⟩)
    have hle := R.toOrdinal_strictMono.monotone
      (show x ≤ (⟨p, S.mem_carrier n hp⟩ : S.Limit) from hxp)
    rw [heq, ← R.label_eq ⟨p, S.mem_carrier n hp⟩] at hle
    exact hle.trans_lt (hc p hp)

/-- An empty stage realizes precisely the zero ordinal. -/
theorem bound_eq_zero_iff (n : ℕ) : R.bound = 0 ↔ (S.stage n).U = ∅ := by
  constructor
  · intro hzero
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have h := R.label_lt_bound (S.mem_carrier n hx)
    rw [hzero] at h
    exact (not_lt_of_ge zero_le) h
  · intro hzero
    apply le_antisymm _ zero_le
    apply (R.bound_le_iff n 0).mpr
    simp only [hzero, Finset.notMem_empty, false_implies, implies_true]

/-- Lemma 14.9(4): no first-relation edge leaves the realized initial
segment. Such an edge would copy a whole finite stage below one of its
own points, contradicting the stage's pointwise minimality. -/
theorem lt_bound_of_R1 {a b : Ordinal.{0}} (ha : a < R.bound) (hab : R1 a b) :
    b < R.bound := by
  classical
  by_contra hb
  have hbound : R.bound ≤ b := le_of_not_gt hb
  let x : S.Limit := R.orderIso.symm ⟨a, ha⟩
  have heq : R.label x.val = a := by
    rw [R.label_eq x]
    exact congrArg Subtype.val (R.orderIso.apply_symm_apply ⟨a, ha⟩)
  obtain ⟨n, hx⟩ := x.property
  let F := (R.stagePattern n).U
  have hF : ∀ z ∈ F, z < b := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact (R.label_lt_bound (S.mem_carrier n hy)).trans_le hbound
  obtain ⟨f, hf⟩ := R1_copy' hab F hF
  have hc : Str.CoveringR (R.stagePattern n) f := ⟨hf.2.2.1, hf.2.2.2⟩
  have hxF : R.label x.val ∈ F := Finset.mem_image_of_mem R.label hx
  have hmin := R.stage_le_covering n hc hxF
  have hlt := hf.1 (R.label x.val) hxF
  rw [heq] at hmin hlt
  exact (not_le_of_gt hlt) hmin

/-- The second relation also cannot leave the realized initial segment. -/
theorem lt_bound_of_R2 {a b : Ordinal.{0}} (ha : a < R.bound) (hab : R2 a b) :
    b < R.bound :=
  R.lt_bound_of_R1 ha (R2_R1 hab)

end OrdinalRealization

end GeneratingSequence
end Alexander313.Carlson
