import Alexander313.Wilken.FiniteUpsilonDomain
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# The actual source-grammar upsilon iteration

Definition 1.5 continuously iterates the independently defined original
source grammar extension, with zero indexing endpoint and the original
T0=T1 convention. Ordinal limit recursion constructs this semantic
iteration at every ordinal index in the original universe. Genuine
successor growth and actual limit suprema prove normality. Its finite
and omega restrictions agree with the existing independently constructed
sequence, identifying the entire image below its omega value with that
finite image. No transfinite coding/effectivity, source-base epsilon
classification above omega, cross-context mu or tracking claim is made.
Uncompiled source candidate.
-/

namespace Alexander313.Wilken

noncomputable def sourceUpsilon (i : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.limitRecOn i 0 (fun _ previous => sourceBaseExtension previous)
    (fun limit _ previous => ⨆ j : Set.Iio limit, previous j.1 j.2)

@[simp]
theorem sourceUpsilon_zero : sourceUpsilon 0 = 0 :=
  Ordinal.limitRecOn_zero ..

@[simp]
theorem sourceUpsilon_succ (i : Ordinal.{0}) :
    sourceUpsilon (i + 1) = sourceBaseExtension (sourceUpsilon i) :=
  Ordinal.limitRecOn_add_one ..

theorem sourceUpsilon_limit (i : Ordinal.{0}) (hi : Order.IsSuccLimit i) :
    sourceUpsilon i = ⨆ j : Set.Iio i, sourceUpsilon j.1 :=
  Ordinal.limitRecOn_limit _ _ _ _ hi

theorem sourceUpsilon_step (i : Ordinal.{0}) :
    sourceUpsilon i < sourceUpsilon (i + 1) := by
  rw [sourceUpsilon_succ]
  exact sourceBaseExtension_gt _

/-- Normality follows from actual successor growth and genuine limit
continuity; no arbitrary-base monotonicity of the extension is assumed. -/
theorem sourceUpsilon_isNormal : Order.IsNormal sourceUpsilon := by
  refine Order.IsNormal.of_succ_lt (fun i => ?_) @fun i hi => ?_
  · simpa only [Order.succ_eq_add_one] using sourceUpsilon_step i
  · rw [sourceUpsilon_limit i hi, Set.image_eq_range]
    have := hi.nonempty_Iio.to_subtype
    exact isLUB_ciSup Ordinal.bddAbove_of_small

theorem sourceUpsilon_strictMono : StrictMono sourceUpsilon :=
  sourceUpsilon_isNormal.strictMono

theorem sourceUpsilon_nat (n : Nat) :
    sourceUpsilon (n : Ordinal.{0}) = sourceUpsilonFinite n := by
  induction n with
  | zero => simp only [Nat.cast_zero, sourceUpsilon_zero, sourceUpsilonFinite_zero]
  | succ n ih =>
    simpa only [Nat.cast_succ, sourceUpsilon_succ, sourceUpsilonFinite_succ, ih]

theorem sourceUpsilon_omega : sourceUpsilon Ordinal.omega0 = sourceUpsilonOmega := by
  calc
    sourceUpsilon Ordinal.omega0 = ⨆ n : Nat, sourceUpsilon (n : Ordinal.{0}) :=
      (Ordinal.apply_omega0_of_isNormal sourceUpsilon_isNormal).symm
    _ = sourceUpsilonOmega := by simp only [sourceUpsilon_nat, sourceUpsilonOmega]

/-- The actual semantic ordinal image of the constructed source iteration. -/
def SourceUpsilonImage (xi : Ordinal.{0}) : Prop :=
  ∃ i : Ordinal.{0}, xi = sourceUpsilon i

/-- Strict increase excludes every transfinite index from the actual
image below upsilon omega. This is a proved restriction of the real
ordinal recursion, rather than a stipulated finite image predicate. -/
theorem sourceUpsilon_image_below_omega (xi : Ordinal.{0}) (hxi : xi < sourceUpsilonOmega) :
    SourceUpsilonImage xi ↔ ∃ n : Nat, xi = sourceUpsilonFinite n := by
  constructor
  · rintro ⟨i, hi⟩
    have hindex : i < Ordinal.omega0 := sourceUpsilon_strictMono.lt_iff_lt.mp
      ((hi.symm.trans_lt hxi).trans_eq sourceUpsilon_omega.symm)
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hindex
    refine ⟨n, hi.trans ?_⟩
    simpa only [hn] using sourceUpsilon_nat n
  · rintro ⟨n, hn⟩
    exact ⟨(n : Ordinal.{0}), hn.trans (sourceUpsilon_nat n).symm⟩

end Alexander313.Wilken
