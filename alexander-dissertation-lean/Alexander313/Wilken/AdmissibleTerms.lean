import Alexander313.Wilken.FiniteNotations
import Alexander313.Wilken.RelativeTerms

/-!
# Source-admissible finite relative terms

Raw syntax is equipped with the actual restrictions of Wilken Lemma 2.6:
parameters below Ωₘ, collapsing indices m≤k<n, and arguments below Ωₖ₊₂.
Admissibility implies source notation membership, and every element of the
semantic finite domain has an admissible finite tree.

The trees here need not be unique or in additive normal form. This module
does not turn semantic ordinal comparisons into an effective recognizer,
nor identify arbitrary raw parameter leaves with the source star support.
All proof terms await external compilation.
-/

namespace Alexander313.Wilken

namespace RelativeTerm

variable {Parameter : Type}

inductive Admissible (parameters : Parameter → Ordinal)
    (omega : Nat → Ordinal) (theta : Nat → Ordinal → Ordinal) (n m : Nat) :
    RelativeTerm Parameter → Prop where
  | parameter {p} : parameters p < omega m → Admissible parameters omega theta n m (.parameter p)
  | sum {a b} : Admissible parameters omega theta n m a →
      Admissible parameters omega theta n m b → Admissible parameters omega theta n m (.sum a b)
  | theta {k a} : m ≤ k → k < n → a.eval parameters theta < omega (k + 2) →
      Admissible parameters omega theta n m a → Admissible parameters omega theta n m (.theta k a)

theorem Admissible.denote {parameters : Parameter → Ordinal}
    {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal} {n m : Nat}
    {t : RelativeTerm Parameter} (h : Admissible parameters omega theta n m t) :
    FiniteNotation omega theta n m (t.eval parameters theta) := by
  induction h with
  | parameter h => exact .parameter h
  | sum _ _ iha ihb => exact .add iha ihb
  | theta hmk hkn hsort _ ih => exact .collapse hmk hkn hsort ih

theorem Admissible.height_le {parameters : Parameter → Ordinal}
    {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal} {n m : Nat}
    {t : RelativeTerm Parameter} (h : Admissible parameters omega theta n m t) : t.height ≤ n := by
  induction h with
  | parameter h => exact Nat.zero_le _
  | sum _ _ iha ihb => exact max_le iha ihb
  | theta hmk hkn hsort _ ih => exact max_le (Nat.succ_le_of_lt hkn) ih

theorem Admissible.indices_between {parameters : Parameter → Ordinal}
    {omega : Nat → Ordinal} {theta : Nat → Ordinal → Ordinal} {n m : Nat}
    {t : RelativeTerm Parameter} (h : Admissible parameters omega theta n m t)
    {k : Nat} (hk : k ∈ t.indices) : m ≤ k ∧ k < n := by
  induction h with
  | parameter h => simp [indices] at hk
  | sum _ _ iha ihb =>
    simp only [indices, Finset.mem_union] at hk
    exact hk.elim iha ihb
  | theta hmk hkn hsort _ ih =>
    simp only [indices, Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact ⟨hmk, hkn⟩
    · exact ih hk

theorem Admissible.parameters_below [DecidableEq Parameter]
    {parameters : Parameter → Ordinal} {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n m : Nat} {t : RelativeTerm Parameter}
    (h : Admissible parameters omega theta n m t) {p : Parameter} (hp : p ∈ t.parameters) :
    parameters p < omega m := by
  induction h with
  | parameter h =>
    simp only [RelativeTerm.parameters, Finset.mem_singleton] at hp
    rcases hp with rfl
    exact h
  | sum _ _ iha ihb =>
    simp only [RelativeTerm.parameters, Finset.mem_union] at hp
    exact hp.elim iha ihb
  | theta hmk hkn hsort _ ih => exact ih hp

end RelativeTerm

/-- Actual parameters are indexed by the small type of the base ordinal.
This keeps raw `RelativeTerm` in its existing Type₀ universe. -/
abbrev SourceRelativeTerm (τ : Ordinal.{0}) (m : Nat) :=
  RelativeTerm (omegaSequence τ m).ToType

noncomputable def sourceParameters (τ : Ordinal.{0}) (m : Nat) : (omegaSequence τ m).ToType → Ordinal.{0} :=
  fun p => (Ordinal.ToType.mk.symm p).val

theorem sourceParameters_below (τ : Ordinal.{0}) (m : Nat)
    (p : (omegaSequence τ m).ToType) : sourceParameters τ m p < omegaSequence τ m :=
  (Ordinal.ToType.mk.symm p).property

theorem sourceParameters_mk (τ : Ordinal.{0}) (m : Nat) (ξ : Ordinal.{0})
    (hξ : ξ < omegaSequence τ m) :
    sourceParameters τ m (Ordinal.ToType.mk ⟨ξ, hξ⟩) = ξ := by
  simp only [sourceParameters, OrderIso.symm_apply_apply]

/-- Every semantic source notation has a finite term with all real sort
bounds present; conversely every such term denotes a source notation. -/
theorem sourceNotation_iff_relativeTerm (τ : Ordinal.{0}) (n m : Nat)
    (hm : m < n) (ξ : Ordinal.{0}) : sourceNotation τ n m ξ ↔
    ∃ t : SourceRelativeTerm τ m,
      RelativeTerm.Admissible (sourceParameters τ m) (omegaSequence τ) (sourceFiniteCollapse τ n) n m t ∧
      t.eval (sourceParameters τ m) (sourceFiniteCollapse τ n) = ξ := by
  rw [sourceNotation, if_pos hm]
  constructor
  · intro h
    induction h with
    | parameter h =>
      refine ⟨.parameter (Ordinal.ToType.mk ⟨_, h⟩), .parameter ?_, ?_⟩
      · exact sourceParameters_below τ m _
      · exact sourceParameters_mk τ m _ h
    | add _ _ iha ihb =>
      obtain ⟨a, ha, hvala⟩ := iha
      obtain ⟨b, hb, hvalb⟩ := ihb
      refine ⟨.sum a b, .sum ha hb, ?_⟩
      simp only [RelativeTerm.eval]
      rw [hvala, hvalb]
    | collapse hmk hkn hsort _ ih =>
      obtain ⟨a, ha, hvala⟩ := ih
      refine ⟨.theta _ a, .theta hmk hkn ?_ ha, ?_⟩
      · simpa only [hvala] using hsort
      · simp only [RelativeTerm.eval]
        rw [hvala]
  · rintro ⟨t, ht, rfl⟩
    exact ht.denote

end Alexander313.Wilken
