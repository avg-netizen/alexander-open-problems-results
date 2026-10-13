import Alexander313.Carlson.FiniteFrame
import Alexander313.Carlson.ReflectionRelabeling
import Alexander313.Carlson.LiftingRelabeling
import Alexander313.Carlson.FiniteCertificateExamples
import Alexander313.Carlson.FiniteDerivationNormalization
import Mathlib.Data.Rat.Lemmas

/-!
# Kernel-checked finite relabeling regressions

Nonconsecutive rational labels retain their order, their inverse images, and
the reflection witnesses previously checked on `Fin 4`. The examples also
cover an empty frame, a nonempty frame using every finite label, and the
irrelevance of relation-table entries away from a structure's carrier.
The accepted natural-number certificates then recover genuine rational
rules and generation witnesses through the common-label soundness theorem.
-/

noncomputable section

namespace Alexander313.Carlson.RelabelingExamples

open Finite Finite.CertificateExamples

/-- Four rational labels with unequal gaps and nonintegral endpoints. -/
def rationalFrame : Finset ℚ := {-7 / 2, 2 / 3, 5, 101 / 4}

theorem rationalFrame_card : rationalFrame.card = 4 := by decide +kernel

theorem rationalFrame_nonempty : rationalFrame.Nonempty := by decide +kernel

def rationalRanks := FiniteRelabeling.toFin rationalFrame

/-- Normalization preserves a strict comparison and recovers its original label. -/
theorem rational_normalization :
    rationalRanks.toFun (-7 / 2) < rationalRanks.toFun (101 / 4) ∧
    rationalRanks.invFun (rationalRanks.toFun (2 / 3)) = 2 / 3 := by
  constructor
  · exact rationalRanks.mono _ (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact rationalRanks.left_inv _ (by decide +kernel)

/-- Empty carriers require no chosen frame member and receive no image labels. -/
theorem empty_frame :
    (∅ : Finset ℚ).image (FiniteRelabeling.toFin (∅ : Finset ℚ)).toFun = ∅ ∧
    (FiniteRelabeling.toFin (∅ : Finset ℚ)).toFun (37 / 11) = Fin.last 0 := by
  constructor
  · simp only [Finset.image_empty]
  · exact FiniteRelabeling.toFin_toFun_of_not_mem _ (Finset.notMem_empty _)

def exactRanks := FiniteRelabeling.toFinOfNonempty rationalFrame rationalFrame_nonempty

/-- Exact-size normalization occupies all four labels and has a globally increasing inverse. -/
theorem exact_frame :
    rationalFrame.image exactRanks.toFun = Finset.univ ∧
    StrictMono exactRanks.invFun :=
  ⟨FiniteRelabeling.toFinOfNonempty_image_univ _ _,
    FiniteRelabeling.toFinOfNonempty_invFun_strictMono _ _⟩

/-- Use the increasing inverse of exact-size normalization to relabel all of `Fin 4`. -/
def rationalLabels : FiniteRelabeling (Finset.univ : Finset (Fin 4)) ℚ where
  toFun i := exactRanks.invFun (Fin.cast rationalFrame_card.symm i)
  invFun x := Fin.cast rationalFrame_card (exactRanks.toFun x)
  left_inv := by
    intro i _
    rw [exactRanks, FiniteRelabeling.toFinOfNonempty_right_inv]
    rfl
  mono := by
    intro i _ j _ hij
    exact (FiniteRelabeling.toFinOfNonempty_invFun_strictMono _ _) hij

private def listedLabel (i : Fin 4) : ℚ :=
  if i = 0 then -7 / 2 else if i = 1 then 2 / 3 else if i = 2 then 5 else 101 / 4

private theorem rationalLabels_eq : rationalLabels.toFun = listedLabel := by
  have h : listedLabel =
      rationalFrame.orderEmbOfFin rationalFrame_card := by
    apply Finset.orderEmbOfFin_unique rationalFrame_card
    · decide +kernel
    · decide +kernel
  have he : rationalLabels.toFun = rationalFrame.orderEmbOfFin rationalFrame_card := rfl
  exact he.trans h.symm

@[simp] theorem rationalLabels_zero : rationalLabels.toFun 0 = -7 / 2 := by
  rw [rationalLabels_eq]
  rfl
@[simp] theorem rationalLabels_one : rationalLabels.toFun 1 = 2 / 3 := by
  rw [rationalLabels_eq]
  rfl
@[simp] theorem rationalLabels_two : rationalLabels.toFun 2 = 5 := by
  rw [rationalLabels_eq]
  rfl
@[simp] theorem rationalLabels_three : rationalLabels.toFun 3 = 101 / 4 := by
  rw [rationalLabels_eq]
  rfl

@[simp] theorem rationalLabels_conjugate_const (i : Fin 4) :
    rationalLabels.conjugate (fun _ => i) = fun _ => rationalLabels.toFun i := rfl

def rationalBase : Str ℚ := base.toStr.map rationalLabels.toFun
def rationalLowerCopy : Str ℚ := downwardRule.target.toStr.map rationalLabels.toFun

private theorem checked_downward_data :
    Str.DownData base.toStr .two 1 3 {1} {0} (fun _ => 1) :=
  of_decide_eq_true downward_accepts

private theorem checked_upward_data :
    Str.UpData base.toStr downwardRule.target.toStr 1 3 {2} (fun _ => 0) := by
  have h := upward_accepts
  change (downwardRule.check && decide
    (Str.UpData base.toStr downwardRule.target.toStr 1 3 {2} (fun _ => 0))) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The checked lower copy at `0` becomes the rational point `-7/2`. -/
theorem rational_downward_data :
    Str.DownData rationalBase .two (2 / 3) (101 / 4) {2 / 3} {-7 / 2}
      (fun _ => 2 / 3) := by
  have h := rationalLabels.downwardData
    (Finset.subset_univ _) (Finset.subset_univ _) checked_downward_data
  simpa only [rationalBase, Finset.image_singleton, rationalLabels_conjugate_const,
    rationalLabels_zero, rationalLabels_one, rationalLabels_three] using h

/-- Downward reflection reconstructed over the rationals agrees with the checked finite result. -/
theorem rational_downward_isIso :
    Str.IsIso downwardRule.target.toStr
      (rationalBase.downward .two (2 / 3) (101 / 4) {-7 / 2} (fun _ => 2 / 3))
      rationalLabels.toFun := by
  have h := rationalLabels.downward_isIso
    (Finset.subset_univ _) (Finset.subset_univ _) checked_downward_data
  simpa only [downwardRule, RuleCertificate.target, PatternCode.toStr_downward,
    rationalBase, Finset.image_singleton, rationalLabels_conjugate_const,
    rationalLabels_zero, rationalLabels_one, rationalLabels_three] using h

/-- Comparing two constructions through the same finite map needs only carrier isomorphisms. -/
theorem rational_lower_copy_agrees :
    Str.IsIso rationalLowerCopy
      (rationalBase.downward .two (2 / 3) (101 / 4) {-7 / 2} (fun _ => 2 / 3)) id :=
  (rationalLabels.isIso (Finset.subset_univ _)).id_of_same_map rational_downward_isIso

/-- The checked upper copy at `2` becomes the rational point `5`. -/
theorem rational_upward_data :
    Str.UpData rationalBase rationalLowerCopy (2 / 3) (101 / 4) {5}
      (fun _ => -7 / 2) := by
  have h := rationalLabels.upwardData (Finset.subset_univ _)
    (Finset.subset_univ _) (Finset.subset_univ _) checked_upward_data
  simpa only [rationalBase, rationalLowerCopy, Finset.image_singleton,
    rationalLabels_conjugate_const, rationalLabels_zero, rationalLabels_one,
    rationalLabels_two, rationalLabels_three] using h

/-- The earlier downward endpoint remains the copied structure in upward reflection. -/
theorem rational_upward_isIso :
    Str.IsIso upwardRule.target.toStr
      (rationalBase.upward rationalLowerCopy (2 / 3) (101 / 4) {5} (fun _ => -7 / 2))
      rationalLabels.toFun := by
  have h := rationalLabels.upward_isIso (Finset.subset_univ _)
    (Finset.subset_univ _) (Finset.subset_univ _) checked_upward_data
  simpa only [upwardRule, RuleCertificate.target, RuleCertificate.source,
    PatternCode.toStr_upward, downwardRule, rationalBase, rationalLowerCopy,
    Finset.image_singleton, rationalLabels_conjugate_const, rationalLabels_zero,
    rationalLabels_one, rationalLabels_two, rationalLabels_three] using h

/-- Ambient tables can differ while the inverse relabeling identifies their induced structures. -/
theorem off_carrier_tables :
    base.toStr ≠ trimmedBase.toStr ∧ Str.IsIso base.toStr trimmedBase.toStr id := by
  have hchecked : base.toStr.IsPattern ∧ Str.IsSub base.toStr trimmedBase.toStr ∧
      trimmedBase.U = base.U := of_decide_eq_true arithmetic_accepts
  have e : Str.IsIso rationalBase base.toStr rationalLabels.invFun :=
    rationalLabels.inverse_isIso (Finset.subset_univ _)
  have e' : Str.IsIso rationalBase trimmedBase.toStr rationalLabels.invFun := by
    refine ⟨e.1, e.2.1, ?_⟩
    intro x hx y hy
    have he := e.2.2 x hx y hy
    have hs := hchecked.2.1.2 _ (e.mem hx) _ (e.mem hy)
    exact ⟨he.1.trans hs.1, he.2.trans hs.2⟩
  exact ⟨fun h => arithmetic_changes_off_carrier (PatternCode.toStr_injective h),
    e.id_of_same_map e'⟩

/-- A singleton relabeling may collapse the entire complement of its image. -/
def singletonLabels : FiniteRelabeling (Finset.univ : Finset (Fin 1)) ℚ where
  toFun _ := 2 / 3
  invFun _ := 0
  left_inv := fun i _ => Subsingleton.elim _ i
  mono := by
    intro i _ j _ hij
    have he : i = j := Subsingleton.elim _ _
    subst j
    exact (lt_irrefl _ hij).elim

def rationalSingleton : Str ℚ := singleton.toStr.map singletonLabels.toFun

private theorem checked_singleton_lifting :
    Str.ContinuousEmbedding singleton.toStr singleton.toStr id ∧
    PatternLifting singleton.toStr singleton.toStr singleton.toStr singleton.toStr id id ∧
    PatternLifting.IsMinimal singleton.toStr singleton.toStr singleton.toStr singleton.toStr id := by
  have h := lifting_accepts
  change (singletonArithmetic.check && decide
    (Str.ContinuousEmbedding singleton.toStr singleton.toStr id ∧
      PatternLifting singleton.toStr singleton.toStr singleton.toStr singleton.toStr id id ∧
      PatternLifting.IsMinimal singleton.toStr singleton.toStr singleton.toStr singleton.toStr id)) =
        true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Finite fixed-carrier minimality transports to an infinite ambient order;
the conjugated total map is constant away from the one-point carrier. -/
theorem rational_minimal_lifting :
    Str.ContinuousEmbedding rationalSingleton rationalSingleton (fun _ => 2 / 3) ∧
    PatternLifting rationalSingleton rationalSingleton rationalSingleton rationalSingleton
      (fun _ => 2 / 3) (fun _ => 2 / 3) ∧
    PatternLifting.IsMinimal rationalSingleton rationalSingleton rationalSingleton rationalSingleton
      (fun _ => 2 / 3) := by
  have h := checked_singleton_lifting
  exact ⟨singletonLabels.continuousEmbedding (Finset.subset_univ _) (Finset.subset_univ _) h.1,
    singletonLabels.patternLifting (Finset.subset_univ _) (Finset.subset_univ _) h.2.1,
    singletonLabels.isMinimal (Finset.subset_univ _) (Finset.subset_univ _) h.2.1 h.2.2⟩

theorem rationalLabels_strictMono : StrictMono rationalLabels.toFun :=
  fun _ _ h => rationalLabels.mono _ (Finset.mem_univ _) _ (Finset.mem_univ _) h

/-- An accepted natural-number code proves the reconstructed downward rule
on nonconsecutive rational labels, including its exact relations. -/
theorem rational_checked_downward_rule :
    Str.GeneratingRule rationalBase
      (rationalBase.downward .two (2 / 3) (101 / 4) {-7 / 2} (fun _ => 2 / 3)) :=
  checkRule_sound_of_labels (by decide) rationalLabels_strictMono
    (rationalLabels.isIso (Finset.subset_univ _)) rational_downward_isIso rule_nat_accepts

/-- The finite characterization carries the hidden two-step chain and its
proper final restriction into the rational ambient order. -/
theorem rational_generation_by_certificate : Str.Generates rationalBase rationalLowerCopy := by
  apply (generates_iff_finite_certificate _ _).mpr
  exact ⟨4, by decide, rationalLabels.toFun, generation.source, generation.target,
    Encodable.encode generation, rationalLabels_strictMono,
    rationalLabels.isIso (Finset.subset_univ _),
    rationalLabels.isIso (Finset.subset_univ _), generation_nat_accepts⟩

end Alexander313.Carlson.RelabelingExamples
