import Alexander313.Wilken.GlobalBaseArithmetic
import Alexander313.Wilken.RelativeTermPublicCodes

/-!
# An actual low principal-successor code operation

The literal one tree is θ₀(0). Appending it to an admitted argument and
applying θₖ computes the next additive principal above θₖ of that argument
when the argument is below Ωₖ₊₁. The low restriction is executable using
the previously proved outer-sort test. Both typed construction and literal
code construction are primitive recursive.

The construction need not preserve additive normal form. It is a restricted
principal-successor operation on noncanonical base-one syntax, not a general
normalizer, hereditary principal classifier or ordinal edge algorithm.
Proof terms await external compilation.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.PrincipalSuccessor

def oneTree : RelativeTerm Nat := .theta 0 (.parameter 0)

theorem oneTree_admissible (n : Nat) (hn : 0 < n) : admissible n oneTree := by
  have hp : admissible n (.parameter 0) :=
    .parameter ((parameter_lt_base_iff 0).mpr rfl)
  apply Admissible.theta (Nat.zero_le 0) hn _ hp
  change (0 : Ordinal.{0}) < omegaSequence 1 2
  exact zero_lt_one.trans ((omegaSequence_base_lt 1).trans (omegaSequence_step 1 1))

theorem oneTree_denote (n : Nat) (hn : 0 < n) : denote n oneTree = 1 := by
  have h := sourceFiniteCollapse_zero 1 zero_lt_one
    (Hereditary.finiteBase_add_closed 0) n 0 hn
  simpa only [oneTree, denote, RelativeTerm.eval, SourceOne.parameters,
    Nat.cast_zero, omegaSequence_zero] using h

theorem oneTree_global_denote : PublicCodes.denote oneTree = 1 := by
  rw [PublicCodes.denote_eq_finite 1 oneTree (oneTree_admissible 1 (by omega))]
  exact oneTree_denote 1 (by omega)

def successorArgument (a : RelativeTerm Nat) : RelativeTerm Nat := .sum a oneTree

theorem successorArgument_admissible (n : Nat) (hn : 0 < n)
    (a : RelativeTerm Nat) (ha : admissible n a) : admissible n (successorArgument a) :=
  .sum ha (oneTree_admissible n hn)

theorem successorArgument_denote (n : Nat) (hn : 0 < n) (a : RelativeTerm Nat) :
    denote n (successorArgument a) = denote n a + 1 := by
  change denote n a + denote n oneTree = _
  rw [oneTree_denote n hn]

def principalSuccessor (k : Nat) (a : RelativeTerm Nat) : RelativeTerm Nat :=
  .theta k (successorArgument a)

theorem principalSuccessor_primrec : Primrec₂ principalSuccessor := by
  have hs : Primrec (fun p : Nat × RelativeTerm Nat => successorArgument p.2) :=
    RelativeTerm.sum_primrec.comp Primrec.snd (Primrec.const oneTree)
  exact (RelativeTerm.theta_primrec.comp Primrec.fst hs).to₂

/-- This is the literal constructor operation on all raw natural inputs.
Only the theorem on accepted source trees assigns it an ordinal meaning. -/
def principalSuccessorCode (k c : Nat) : Nat :=
  Nat.succ (Nat.pair 2 (Nat.pair k
    (Nat.succ (Nat.pair 1 (Nat.pair c oneTree.code)))))

theorem principalSuccessorCode_primrec : Primrec₂ principalSuccessorCode := by
  have hs : Primrec (fun p : Nat × Nat =>
      Nat.succ (Nat.pair 1 (Nat.pair p.2 oneTree.code))) :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp Primrec.snd (Primrec.const oneTree.code)))
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp Primrec.fst hs))).to₂

@[simp] theorem principalSuccessorCode_code (k : Nat) (a : RelativeTerm Nat) :
    principalSuccessorCode k a.code = (principalSuccessor k a).code := rfl

theorem principalSuccessor_admissible (n k : Nat) (hkn : k < n)
    (a : RelativeTerm Nat) (ha : admissible n a) (houter : a.outerSort ≤ k + 1) :
    admissible n (principalSuccessor k a) := by
  have hlow := (denote_lt_iff_outerSort_le n a ha (k + 1) (by omega)).mpr houter
  have hsucc : denote n a + 1 < omegaSequence 1 (k + 1) :=
    (omegaSequence_isSuccLimit 1 k).add_one_lt hlow
  have hn : 0 < n := by omega
  apply Admissible.theta (Nat.zero_le k) hkn _ (successorArgument_admissible n hn a ha)
  change denote n (successorArgument a) < omegaSequence 1 (k + 2)
  rw [successorArgument_denote n hn a]
  exact hsucc.trans (omegaSequence_step 1 (k + 1))

/-- Correctness uses the actual collapse minimum, not a supplied enumeration. -/
theorem principalSuccessor_denote (n k : Nat) (hkn : k < n)
    (a : RelativeTerm Nat) (ha : admissible n a) (houter : a.outerSort ≤ k + 1) :
    denote n (principalSuccessor k a) =
      nextAdditivePrincipal (denote n (.theta k a)) := by
  have hn : 0 < n := by omega
  have hlow := (denote_lt_iff_outerSort_le n a ha (k + 1) (by omega)).mpr houter
  change sourceFiniteCollapse 1 n k (denote n (successorArgument a)) = _
  rw [successorArgument_denote n hn a]
  exact sourceFiniteCollapse_succ_eq_nextAdditivePrincipal 1 n k hkn (denote n a) hlow

/-- The same literal output has this meaning for the real global family. -/
theorem principalSuccessor_global_denote (n k : Nat) (hkn : k < n)
    (a : RelativeTerm Nat) (ha : admissible n a) (houter : a.outerSort ≤ k + 1) :
    PublicCodes.denote (principalSuccessor k a) =
      nextAdditivePrincipal (PublicCodes.denote (.theta k a)) := by
  have hlow := (denote_lt_iff_outerSort_le n a ha (k + 1) (by omega)).mpr houter
  have htheta : admissible n (.theta k a) :=
    .theta (Nat.zero_le k) hkn (hlow.trans (omegaSequence_step 1 (k + 1))) ha
  rw [PublicCodes.denote_eq_finite n _ (principalSuccessor_admissible n k hkn a ha houter),
    PublicCodes.denote_eq_finite n _ htheta]
  exact principalSuccessor_denote n k hkn a ha houter

end Alexander313.Wilken.RelativeTerm.SourceOne.PrincipalSuccessor
