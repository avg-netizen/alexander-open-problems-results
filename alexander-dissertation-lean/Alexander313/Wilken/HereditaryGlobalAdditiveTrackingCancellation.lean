import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingCancellationSupport

/-!
# Executing the genuine global tracking lead-factor quotient

The independently executing exact divider terminates on every canonical
epsilon gamma strictly below the actual positive additive-principal input.
Its returned quotient is canonical, positive and additive principal, and
is the least (indeed unique) solution of gamma*delta=alpha. The small interval
bound is derived from the real source input when present. No chosen division
equation or quotient grammar is an additional caller. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.Cancellation

open CancellationSupport

def execute (gamma alpha : Nat) : Part Nat :=
  cond (inputCheck gamma alpha) (ExactDivision.divide gamma alpha) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp ExactDivision.divide_partrec Partrec.none).to₂

theorem execute_domain (gamma alpha : Nat) : (execute gamma alpha).Dom ↔ inputCheck gamma alpha = true := by
  constructor
  · intro hd
    cases hi : inputCheck gamma alpha with
    | true => rfl
    | false =>
      have hn : (Part.none : Part Nat).Dom := by simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hn)
  · intro hi
    have hd := (ExactDivision.divide_domain gamma alpha).mpr (division_caller gamma alpha hi)
    simpa only [execute, hi, Bool.cond_true] using hd

theorem execute_returns (gamma alpha : Nat) (hi : inputCheck gamma alpha = true) :
    ∃ out, out ∈ execute gamma alpha :=
  Part.dom_iff_mem.mp ((execute_domain gamma alpha).mpr hi)

/-- Positive left multiplication identifies the actual canonical quotient
with the mathematically constructed omega power, deriving its principalness. -/
theorem execute_spec (gamma alpha out : Nat) (ho : out ∈ execute gamma alpha) :
    inputCheck gamma alpha = true ∧ Canonical.check out = true ∧
      1 < unionInterpretation out ∧ Ordinal.IsPrincipal (· + ·) (unionInterpretation out) ∧
        unionInterpretation gamma * unionInterpretation out = unionInterpretation alpha ∧
          unionInterpretation out ≤ unionInterpretation alpha := by
  have hi := (execute_domain gamma alpha).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hd : out ∈ ExactDivision.divide gamma alpha := by simpa only [execute, hi, Bool.cond_true] using ho
  obtain ⟨hg, he, hc, hp, ha, hl⟩ := (inputCheck_exact gamma alpha).mp hi
  have hs := ExactDivision.divide_value gamma alpha out hd
  obtain ⟨delta, hpos, hprincipal, hproduct⟩ := epsilon_principal_quotient he hp ha hl.le
  have hv := ExactDivision.divide_eq_every_solution gamma alpha out hd delta hproduct
  have hone : 1 < unionInterpretation out := by
    by_contra hn
    have hle : unionInterpretation out ≤ 1 := le_of_not_gt hn
    have hmul : unionInterpretation gamma * unionInterpretation out ≤ unionInterpretation gamma :=
      by simpa only [Ordinal.mul_one] using mul_le_mul_right hle (unionInterpretation gamma)
    exact (not_le_of_gt hl) (hs.2.2.2.2.symm.trans_le hmul)
  exact ⟨hi, hs.2.2.2.1, hone, by rw [hv]; exact hprincipal,
    hs.2.2.2.2, ExactDivision.divide_bound gamma alpha out hd⟩

theorem execute_least_solution (gamma alpha out : Nat) (ho : out ∈ execute gamma alpha)
    (delta : Ordinal.{0}) (he : unionInterpretation gamma * delta = unionInterpretation alpha) :
    unionInterpretation out = delta ∧ unionInterpretation out ≤ delta := by
  have hi := (execute_spec gamma alpha out ho).1
  have hd : out ∈ ExactDivision.divide gamma alpha := by simpa only [execute, hi, Bool.cond_true] using ho
  have hv := ExactDivision.divide_eq_every_solution gamma alpha out hd delta he
  exact ⟨hv, le_of_eq hv⟩

/-- In the small Definition3.24 branch the actual final nu-index remains
below gamma^omega and satisfies the real cancellation equation. -/
theorem execute_small_interval (gamma alpha out : Nat) (ho : out ∈ execute gamma alpha)
    (hb : unionInterpretation alpha < unionInterpretation gamma ^ Ordinal.omega0) :
    1 < unionInterpretation out ∧ unionInterpretation out < unionInterpretation gamma ^ Ordinal.omega0 ∧
      unionInterpretation gamma * unionInterpretation out = unionInterpretation alpha := by
  have hs := execute_spec gamma alpha out ho
  exact ⟨hs.2.2.1, hs.2.2.2.2.2.trans_lt hb, hs.2.2.2.2.1⟩

theorem execute_output_invariant (gamma alpha otherGamma otherAlpha out otherOut : Nat)
    (ho : out ∈ execute gamma alpha) (ht : otherOut ∈ execute otherGamma otherAlpha)
    (hg : unionInterpretation gamma = unionInterpretation otherGamma)
    (ha : unionInterpretation alpha = unionInterpretation otherAlpha) : out = otherOut := by
  have hi := (execute_spec gamma alpha out ho).1
  have hj := (execute_spec otherGamma otherAlpha otherOut ht).1
  apply ExactDivision.divide_output_invariant gamma alpha otherGamma otherAlpha out otherOut
    (by simpa only [execute, hi, Bool.cond_true] using ho)
    (by simpa only [execute, hj, Bool.cond_true] using ht) hg ha

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.Cancellation
