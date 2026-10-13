import Alexander313.Wilken.PureRelationsSeparatedCopySupport
import Alexander313.Wilken.PureRelationsFiniteReflection
import Alexander313.Wilken.PureRelationsTransitivity

/-!
# Genuine cofinal separated copies preserving endpoint R1 connections

One literal existential-universal matrix expresses the complete finite
pattern, fixes all original lower points, puts fresh copied points above an
arbitrary prescribed lower cutoff, and asks for all designated R1 links to
every later point. Actual R2 elementarity constructs its witnesses. Actual
R1 interval connectedness verifies the upper witnesses; actual R1 right-limit
continuity converts the lower universal links into links to the lower
endpoint itself. This is the finite-copy statement of source Lemma 1.7(2).

No copy, room, reflection, relation, endpoint-link or stage-soundness oracle
is an input. The relations are the actual simultaneous ordinal recursion.
The coded effective adapter and global source-table construction remain
separate. This uncompiled draft stays outside the package at its checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations.SeparatedCopies

theorem lower_cofinal (α β : Ordinal.{0}) (hR : R1 α β) (hαβ : α < β)
    (c : Ordinal.{0}) (hc : c < α) : ∃ d : Ordinal.{0}, c < d ∧ d < α := by
  let F : Finset Ordinal.{0} := {c, α}
  have hF : ∀ x ∈ F, x < β := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc.trans hαβ
    · have he : x = α := Finset.mem_singleton.mp hx
      simpa only [he] using hαβ
  obtain ⟨f, below, fixed, pattern⟩ := PureRelations.finiteLabelReflection α β hR F hF
  have hcm : c ∈ F := Finset.mem_insert_self _ _
  have hαm : α ∈ F := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hcd := (pattern.2.1 c hcm α hαm).mpr hc
  rw [fixed c hcm hc] at hcd
  exact ⟨f α, hcd, below α hαm⟩

theorem lower_isSuccLimit (α β : Ordinal.{0}) (hR : R1 α β) (hαβ : α < β) :
    Order.IsSuccLimit α := by
  have hα : 0 < α := sigma1_nonzero_lower _ _ α β ((R1_iff α β).mp hR).2
    ((bot_le : (0 : Ordinal.{0}) ≤ α).trans_lt hαβ)
  refine ⟨fun hmin => hmin.not_lt hα, ?_⟩
  intro c hcov
  obtain ⟨d, hcd, hdα⟩ := lower_cofinal α β hR hαβ c hcov.lt
  exact (not_covBy_of_lt_of_lt hcd hdα) hcov

/-- The single universal block supplies EVERY selected endpoint link; the
complete finite copied tuple and its prescribed labels share one witness. -/
theorem tuple_separated {n : Nat} (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β)
    (c : Ordinal.{0}) (hc : c < α) (x : Fin n → Ordinal.{0}) (hx : TupleBelow β x) :
    ∃ w : Fin n → Ordinal.{0}, TupleBelow α w ∧
      (∀ i, x i < α → w i = x i) ∧ (∀ i, α ≤ x i → c < w i) ∧
      (∀ i j, w i = w j ↔ x i = x j) ∧ (∀ i j, w i < w j ↔ x i < x j) ∧
      (∀ i j, R1 (w i) (w j) ↔ R1 (x i) (x j)) ∧
      (∀ i j, R2 (w i) (w j) ↔ R2 (x i) (x j)) ∧
      (∀ i, R1 (x i) β → R1 (w i) α) := by
  have hlim := lower_isSuccLimit α β (R2_R1 hR) hαβ
  let p := parameters α c x
  let φ := diagram α β (prefixFirst β) (prefixSecond β) x
  have hp : TupleBelow α p := parameters_below α c hlim.pos hc x
  have hu : sigma2Truth (prefixFirst β) (prefixSecond β) β (n + 1) n 1 φ p := by
    refine ⟨x, hx, ?_⟩
    intro z hz
    apply (diagram_realize α β (prefixFirst β) (prefixSecond β) x p x z).mpr
    intro i
    refine ⟨?_, ?_, ?_, fun _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
    · exact parameters_original α c x i
    · intro hi
      simpa only [p, parameters_cut] using hc.trans_le hi
    · intro hi hiz
      exact ⟨hz 0, R1_between hi hiz (hz 0).le⟩
  obtain ⟨w, hw, hd⟩ := ((R2_iff α β).mp hR).2 (n + 1) n 1 φ p hp |>.mpr hu
  have hzero : TupleBelow α (fun _ : Fin 1 => (0 : Ordinal.{0})) := fun _ => hlim.pos
  have he := (diagram_realize α β (prefixFirst β) (prefixSecond β) x p w
    (fun _ => 0)).mp (hd (fun _ => 0) hzero)
  have hle (i j : Fin n) : w i ≤ w j ↔ x i ≤ x j := ((he i).2.2.2 j).2.1
  have hwβ (i : Fin n) : w i < β := (hw i).trans hαβ
  refine ⟨w, hw, ?_, ?_, (fun i j => ((he i).2.2.2 j).1), ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ((he i).1 hi).symm.trans (parameters_original α c x i hi)
  · intro i hi
    simpa only [p, parameters_cut] using (he i).2.1 hi
  · intro i j
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle i j, hle j i]
  · intro i j
    exact (prefixFirst_below (hwβ j)).symm.trans
      ((((he i).2.2.2 j).2.2.1).trans (prefixFirst_below (hx j)))
  · intro i j
    exact (prefixSecond_below (hwβ j)).symm.trans
      ((((he i).2.2.2 j).2.2.2).trans (prefixSecond_below (hx j)))
  · intro i hi
    apply R1_limit hlim (hw i)
    intro γ hiγ hγα
    have hz : TupleBelow α (fun _ : Fin 1 => γ) := fun _ => hγα
    have hγ := (diagram_realize α β (prefixFirst β) (prefixSecond β) x p w
      (fun _ => γ)).mp (hd (fun _ => γ) hz)
    exact ((hγ i).2.2.1 hi hiγ).2

/-- Actual source Lemma 1.7(2) in finite-set form. All existing lower
points stay fixed. Every fresh point is copied above any prescribed cutoff,
and every original R1 connection to beta becomes an R1 connection to alpha. -/
theorem finite_separated_copy (α β : Ordinal.{0}) (hR : R2 α β) (hαβ : α < β)
    (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < α)
    (hY : ∀ y ∈ Y, α ≤ y ∧ y < β) (c : Ordinal.{0}) (hc : c < α) :
    ∃ f : Ordinal.{0} → Ordinal.{0}, PreservesPattern (X ∪ Y) f ∧
      (∀ x ∈ X, f x = x) ∧ (∀ y ∈ Y, c < f y ∧ f y < α) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x < f y) ∧
      (∀ y ∈ Y, R1 y β → R1 (f y) α) := by
  let F := X ∪ Y
  let e : F ≃ Fin F.card := F.equivFin
  let x : Fin F.card → Ordinal.{0} := fun i => (e.symm i).val
  have xmem (i : Fin F.card) : x i ∈ F := (e.symm i).property
  have xindex (μ : Ordinal.{0}) (hμ : μ ∈ F) : x (e ⟨μ, hμ⟩) = μ :=
    congrArg Subtype.val (e.symm_apply_apply ⟨μ, hμ⟩)
  have hx : TupleBelow β x := by
    intro i
    rcases Finset.mem_union.mp (xmem i) with hi | hi
    · exact (hX _ hi).trans hαβ
    · exact (hY _ hi).2
  obtain ⟨w, hw, fixed, above, heq, hlt, h₁, h₂, links⟩ :=
    tuple_separated α β hR hαβ c hc x hx
  let f : Ordinal.{0} → Ordinal.{0} := fun μ => if hμ : μ ∈ F then w (e ⟨μ, hμ⟩) else μ
  have fmem (μ : Ordinal.{0}) (hμ : μ ∈ F) : f μ = w (e ⟨μ, hμ⟩) := by
    simp only [f, dif_pos hμ]
  have pattern : PreservesPattern F f := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro μ hμ ν hν
      simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
        heq (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
    · intro μ hμ ν hν
      simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
        hlt (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
    · intro μ hμ ν hν
      simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
        h₁ (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
    · intro μ hμ ν hν
      simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
        h₂ (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
  have fixedX (μ : Ordinal.{0}) (hμ : μ ∈ X) : f μ = μ := by
    have hm : μ ∈ F := Finset.mem_union.mpr (Or.inl hμ)
    rw [fmem μ hm]
    exact (fixed _ (by simpa only [xindex μ hm] using hX μ hμ)).trans (xindex μ hm)
  refine ⟨f, pattern, fixedX, ?_, ?_, ?_⟩
  · intro μ hμ
    have hm : μ ∈ F := Finset.mem_union.mpr (Or.inr hμ)
    rw [fmem μ hm]
    exact ⟨above _ (by simpa only [xindex μ hm] using (hY μ hμ).1), hw _⟩
  · intro μ hμ ν hν
    have hh := (pattern.2.1 μ (Finset.mem_union.mpr (Or.inl hμ))
      ν (Finset.mem_union.mpr (Or.inr hν))).mpr ((hX μ hμ).trans_le (hY ν hν).1)
    simpa only [fixedX μ hμ] using hh
  · intro μ hμ hlink
    have hm : μ ∈ F := Finset.mem_union.mpr (Or.inr hμ)
    rw [fmem μ hm]
    exact links _ (by simpa only [xindex μ hm] using hlink)

end Alexander313.Wilken.PureRelations.SeparatedCopies
