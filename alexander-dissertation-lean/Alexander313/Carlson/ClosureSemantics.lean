import Alexander313.Carlson.OmegaOneClosure

/-!
# Closure points satisfy Carlson's actual second relation

First establish `a ≤₁ ω₁` at every reflection point. This step is needed
before transporting a link `y ≤₁ b` to the unary flag `y ≤₁ ω₁`. Boundedness
cutoffs then transfer cofinal copy families through `ω₁` and between any two
reflection points. All relations here are the recursively defined ones.
-/

noncomputable section

namespace Alexander313.Carlson

open Ordinal Cardinal

/-- A finite copy over the fixed anchors at most `ξ`, preserving ambient
first-relation links as unary flags. -/
def AnchoredCopy (F : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (ξ a : Ordinal.{0}) : Prop :=
  (∀ z ∈ F, f z < a) ∧ (∀ z ∈ F, z ≤ ξ → f z = z) ∧
  (∀ z ∈ F, ∀ w ∈ F, z < w → f z < f w) ∧
  (∀ z ∈ F, ∀ w ∈ F, R1 z w → R1 (f z) (f w)) ∧
  (∀ z ∈ F, ∀ w ∈ F, R2 z w → R2 (f z) (f w)) ∧
  (∀ z ∈ F, ξ < z → ξ < f z) ∧
  (∀ z ∈ F, R1 z ω₁ → R1 (f z) ω₁)

theorem ReflectionPoint.finite_copy {a ξ : Ordinal.{0}} (ha : ReflectionPoint a)
    (hξ : ξ < a) (F : Finset Ordinal.{0}) (hF : ∀ z ∈ F, z < ω₁) :
    ∃ f, AnchoredCopy F f ξ a := by
  classical
  let e := F.orderEmbOfFin rfl
  let r : WitnessRequest ξ := ⟨F.card,
    (fun i => if h : e i ≤ ξ then some ⟨e i, h⟩ else none),
    (fun i j => e i < e j), (fun i j => R1 (e i) (e j)),
    (fun i j => R2 (e i) (e j)), (fun i => R1 (e i) ω₁)⟩
  have hr : r.Realizes ω₁ e := by
    refine ⟨fun i => hF _ (F.orderEmbOfFin_mem rfl i), ?_,
      fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩
    intro i
    dsimp [r]
    split_ifs with h
    · rfl
    · exact not_le.mp h
  obtain ⟨u, hu, hua⟩ := reflect_request hξ ha.below ha.witnesses r ⟨e, hr⟩
  obtain ⟨huκ, huanchors, huord, hu₁, hu₂, hulinks⟩ := hu
  let index (z : Ordinal.{0}) (hz : z ∈ F) := (F.orderIsoOfFin rfl).symm ⟨z, hz⟩
  have he (z : Ordinal.{0}) (hz : z ∈ F) : e (index z hz) = z := by
    exact congrArg Subtype.val ((F.orderIsoOfFin rfl).apply_symm_apply ⟨z, hz⟩)
  let f (z : Ordinal.{0}) := if hz : z ∈ F then u (index z hz) else z
  have hf (z : Ordinal.{0}) (hz : z ∈ F) : f z = u (index z hz) := by
    simp only [f, hz, ↓reduceDIte]
  refine ⟨f, ⟨fun z hz => (hf z hz) ▸ hua (index z hz), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz hzx
    rw [hf z hz]
    have hi : e (index z hz) ≤ ξ := (he z hz).symm ▸ hzx
    have := huanchors (index z hz)
    simpa [r, he z hz, hzx] using this
  · intro z hz w hw hzw
    rw [hf z hz, hf w hw]
    exact huord _ _ (by simpa only [r, he z hz, he w hw] using hzw)
  · intro z hz w hw hzw
    rw [hf z hz, hf w hw]
    exact hu₁ _ _ (by simpa only [r, he z hz, he w hw] using hzw)
  · intro z hz w hw hzw
    rw [hf z hz, hf w hw]
    exact hu₂ _ _ (by simpa only [r, he z hz, he w hw] using hzw)
  · intro z hz hxz
    rw [hf z hz]
    have hi : ¬e (index z hz) ≤ ξ := by simpa only [he z hz] using not_le.mpr hxz
    have := huanchors (index z hz)
    simpa only [r, hi, ↓reduceDIte] using this
  · intro z hz hlink
    rw [hf z hz]
    exact hulinks _ (by simpa only [r, he z hz] using hlink)

theorem ReflectionPoint.first {a : Ordinal.{0}} (ha : ReflectionPoint a) : R1 a ω₁ := by
  classical
  refine (R1_iff a ω₁).mpr ⟨ha.below.le, fun F hF => ?_⟩
  let X := F.filter (fun z => z < a)
  let ξ := X.sup id
  have hξ : ξ < a := (Finset.sup_lt_iff ha.pos).mpr fun z hz =>
    (Finset.mem_filter.mp hz).2
  obtain ⟨f, below, fixed, mono, first, second, _⟩ := ha.finite_copy hξ F hF
  have copy : CoveringCopy R1 R2 F f a := ⟨below, fun z hz hza =>
    fixed z hz (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hz, hza⟩)),
    mono, first, second⟩
  exact ⟨f, copy.prefix ha.below.le⟩

/-- Cofinal copy families in the ambient segment reflect down to every
reflection point containing their finite anchor set. -/
theorem ReflectionPoint.cofinal_down {a : Ordinal.{0}} (ha : ReflectionPoint a)
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < a) {n : ℕ}
    (P₁ P₂ : Fin n → Fin n → Prop) (cof : CofinalCopies R1 R2 X P₁ P₂ ω₁) :
    CofinalCopies R1 R2 X P₁ P₂ a := by
  classical
  intro ξ hξ
  let ρ := max ξ (X.sup id)
  have hρ : ρ < a := max_lt hξ ((Finset.sup_lt_iff ha.pos).mpr hX)
  obtain ⟨Y, hY, cover⟩ := cof ρ (hρ.trans ha.below)
  let F := X ∪ Y
  have hF : ∀ z ∈ F, z < ω₁ := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hX z hz).trans ha.below
    · exact (hY z hz).2
  obtain ⟨f, below, fixed, mono, first, second, above, _⟩ := ha.finite_copy hρ F hF
  have hx (x : Ordinal.{0}) (hx : x ∈ X) : f x = x :=
    fixed x (Finset.mem_union_left Y hx)
      ((Finset.le_sup (f := id) hx).trans (le_max_right _ _))
  refine ⟨Y.image f, fun y hy => ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(le_max_left _ _).trans_lt
      (above z (Finset.mem_union_right X hz) (hY z hz).1),
      below z (Finset.mem_union_right X hz)⟩
  · have himage : F.image f = X ∪ Y.image f := by
      rw [Finset.image_union]
      congr 1
      calc X.image f = X.image id := Finset.image_congr fun x hx' => hx x hx'
        _ = X := Finset.image_id
    rw [← himage]
    exact cover.transport f mono first second

/-- Closure under obstruction cutoffs excludes a copy family that is
cofinal locally but bounded in the ambient segment. -/
theorem ReflectionPoint.cofinal_up {a : Ordinal.{0}} (ha : ReflectionPoint a)
    (X : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < a) {n : ℕ}
    (P₁ P₂ : Fin n → Fin n → Prop) (cof : CofinalCopies R1 R2 X P₁ P₂ a) :
    CofinalCopies R1 R2 X P₁ P₂ ω₁ := by
  classical
  let ξ := X.sup id
  have hξ : ξ < a := (Finset.sup_lt_iff ha.pos).mpr hX
  letI := countable_cofinalRequest (hξ.trans ha.below)
  let A : Finset (Set.Iic ξ) := X.attach.image
    (fun x => ⟨x.1, Finset.le_sup (f := id) x.2⟩)
  let r : CofinalRequest ξ := ⟨n, A, P₁, P₂⟩
  have hanchors : r.anchors = X := by
    simp only [CofinalRequest.anchors, r, A, Finset.image_image]
    exact Finset.attach_image_val
  by_contra hnot
  have hr : ¬r.Unbounded := by simpa only [CofinalRequest.Unbounded, hanchors] using hnot
  have hblock : r.blocker < a :=
    (Ordinal.le_iSup (fun r : CofinalRequest ξ => r.blocker) r).trans_lt
      (ha.obstructions ξ hξ)
  obtain ⟨Y, hY, cover⟩ := cof r.blocker hblock
  apply r.blocker_blocks hr
  refine ⟨Y, fun y hy => ⟨(hY y hy).1, (hY y hy).2.trans ha.below⟩, ?_⟩
  simpa only [hanchors] using cover

/-- Any two increasing reflection points are related by Carlson's actual
second relation. -/
theorem ReflectionPoint.second {a b : Ordinal.{0}} (ha : ReflectionPoint a)
    (hb : ReflectionPoint b) (hab : a ≤ b) : R2 a b := by
  classical
  refine R2_of_global hab (fun F hF => ?_) (fun X hX n P₁ P₂ cof => ?_)
  · let X := F.filter (fun z => z < a)
    let ξ := X.sup id
    have hξ : ξ < a := (Finset.sup_lt_iff ha.pos).mpr fun z hz =>
      (Finset.mem_filter.mp hz).2
    obtain ⟨f, below, fixed, mono, first, second, above, flags⟩ :=
      ha.finite_copy hξ F (fun z hz => (hF z hz).trans hb.below)
    refine ⟨f, ⟨below, fun z hz hza =>
      fixed z hz (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hz, hza⟩)),
      mono, first, second⟩, fun z hz _ hzb => ?_⟩
    exact R1_between (flags z hz (R1_trans hzb hb.first)) (below z hz).le ha.below.le
  · exact hb.cofinal_down X (fun x hx => (hX x hx).trans_le hab) P₁ P₂
      (ha.cofinal_up X hX P₁ P₂ cof)

end Alexander313.Carlson
