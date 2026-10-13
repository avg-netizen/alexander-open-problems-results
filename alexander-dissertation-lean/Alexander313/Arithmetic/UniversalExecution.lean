import Alexander313.Arithmetic.BetaExecution

/-!
# A fixed arithmetic formula for the actual universal program domain

The formula existentially supplies beta parameters and a finite prefix,
checks every record in that prefix by the actual local evaluator rules,
and designates a root record with the requested program code and input.
The standard truth theorem proves exactly `W`, and hygienic two-port
instantiation yields an actual `ArithmeticCoding` with arbitrary-model
coherence.

The bounded universal prefix check is not positive existential. The PA
proof of each true complete trace instance consequently remains separate
from the positive record/local-rule certificates already constructed.
-/

namespace Alexander313

namespace ArithmeticGraphs

/-- Move the seven local checker ports to the sequence-checking context.
    All moves form an explicit permutation of variable names. -/
def executionPorts : Equiv Nat Nat :=
  ((((((Equiv.swap 2 12).trans (Equiv.swap 2 4)).trans (Equiv.swap 3 13)).trans
    (Equiv.swap 3 5)).trans (Equiv.swap 0 10)).trans (Equiv.swap 1 11)).trans
    (Equiv.swap 6 9)

theorem localExecution_renamed_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P ((localExecution Owner).renameVariables executionPorts) s ↔
      EncodedTraceStep (s 2) (s 3) (s 9) (s 10) (s 11) (s 12) (s 13) := by
  rw [truth_arithmetic_renameVariables _
    (Formula.positiveExistential_arithmetic _ (localExecution_positive Owner))
    _ executionPorts.injective, localExecution_truth]
  simp [Function.comp_def, executionPorts, Equiv.trans_apply, Equiv.swap_apply_def]

theorem localExecution_renamed_variables (Owner : Type) :
    ((localExecution Owner).renameVariables executionPorts).freeVars = {2, 3, 9, 10, 11, 12, 13} := by
  rw [Formula.freeVars_renameVariables _ _ executionPorts.injective, localExecution_variables]
  ext v
  simp [executionPorts, Equiv.trans_apply, Equiv.swap_apply_def] <;> omega

/-- Ports 2,3 are the beta parameters and port 4 is the prefix length. -/
def sequenceExecution (Owner : Type) : Formula Owner :=
  .all 9 (.imp (less Owner (.var 9) (.var 4))
    (existsVariables [10, 11, 12, 13, 14]
      (.conj (beta Owner (.var 2) (.var 3) (.var 9) (.var 14))
        (.conj (record Owner (.var 10) (.var 11) (.var 12) (.var 13) (.var 14))
          ((localExecution Owner).renameVariables executionPorts)))))

theorem sequenceExecution_arithmetic (Owner : Type) :
    (sequenceExecution Owner).Arithmetic := by
  simp only [sequenceExecution, existsVariables, Formula.Arithmetic]
  exact ⟨Formula.positiveExistential_arithmetic _ (less_positive _ _ _),
    ⟨Formula.positiveExistential_arithmetic _ (beta_positive _ _ _ _ _),
      ⟨Formula.positiveExistential_arithmetic _ (record_positive _ _ _ _ _ _),
        (localExecution Owner).arithmetic_renameVariables
          (Formula.positiveExistential_arithmetic _ (localExecution_positive Owner)) _⟩⟩⟩

theorem sequenceExecution_variables (Owner : Type) :
    (sequenceExecution Owner).freeVars = {2, 3, 4} := by
  ext v
  simp [sequenceExecution, existsVariables, less, beta, record, pair, le,
    localExecution_renamed_variables, Formula.freeVars, Term.freeVars,
    Term.termsBound, Term.variableBound] <;> omega

theorem sequenceExecution_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (sequenceExecution Owner) s ↔
      BetaExecutionCorrect (s 2) (s 3) (s 4) := by
  simp only [sequenceExecution, existsVariables, truth, less_truth, beta_truth, record_truth,
    localExecution_renamed_truth, Term.eval, Function.update_apply,
    ite_true, ite_false, reduceCtorEq]
  change (∀ i, i < s 4 → (∃ fuel program input output row,
    s 2 % ((i + 1) * s 3 + 1) = row ∧
      row = Nat.pair fuel (Nat.pair program (Nat.pair input output)) ∧
      EncodedTraceStep (s 2) (s 3) i fuel program input output)) ↔
        BetaExecutionCorrect (s 2) (s 3) (s 4)
  simp only [exists_fields_iff_local, BetaExecutionCorrect]

/-- Ports 0,1 are exactly the actual program number and its input. -/
def universalExecution (Owner : Type) : Formula Owner :=
  existsVariables [2, 3, 4, 5, 6, 7, 8]
    (.conj (less Owner (.var 5) (.var 4))
      (.conj (beta Owner (.var 2) (.var 3) (.var 5) (.var 8))
        (.conj (record Owner (.var 6) (.var 0) (.var 1) (.var 7) (.var 8))
          (sequenceExecution Owner))))

theorem universalExecution_arithmetic (Owner : Type) :
    (universalExecution Owner).Arithmetic := by
  simp only [universalExecution, existsVariables, Formula.Arithmetic]
  exact ⟨Formula.positiveExistential_arithmetic _ (less_positive _ _ _),
    ⟨Formula.positiveExistential_arithmetic _ (beta_positive _ _ _ _ _),
      ⟨Formula.positiveExistential_arithmetic _ (record_positive _ _ _ _ _ _),
        sequenceExecution_arithmetic Owner⟩⟩⟩

theorem universalExecution_variables (Owner : Type) :
    (universalExecution Owner).freeVars = {0, 1} := by
  ext v
  simp [universalExecution, existsVariables, less, beta, record, pair, le,
    sequenceExecution_variables, Formula.freeVars, Term.freeVars,
    Term.termsBound, Term.variableBound] <;> omega

theorem universalExecution_truth {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (s : Assignment) :
    truth filtered P (universalExecution Owner) s ↔ W (s 0) (s 1) := by
  rw [W_iff_beta_execution]
  simp only [universalExecution, existsVariables, truth, less_truth, beta_truth,
    record_truth, sequenceExecution_truth]
  simp only [Term.eval, Function.update_apply]
  simp only [ite_true, ite_false, reduceCtorEq, TraceRecord.code,
    ← Nat.Partrec.Code.ofNatCode_eq, Denumerable.encode_ofNat]
  constructor
  · rintro ⟨a, b, length, i, fuel, output, row, hi, hbeta, hrow, hcorrect⟩
    exact ⟨a, b, length, i, fuel, output, hi, hbeta.trans hrow, hcorrect⟩
  · rintro ⟨a, b, length, i, fuel, output, hi, hbeta, hcorrect⟩
    exact ⟨a, b, length, i, fuel, output, _, hi, hbeta, rfl, hcorrect⟩

end ArithmeticGraphs

/-- Concrete canonical arithmetic template for the pinned universal evaluator. -/
def universalExecutionTemplate (Owner : Type) : ArithmeticTemplate Owner where
  body := ArithmeticGraphs.universalExecution Owner
  arithmetic := ArithmeticGraphs.universalExecution_arithmetic Owner
  «variables» := by
    intro v hv
    rw [ArithmeticGraphs.universalExecution_variables] at hv
    exact hv

theorem universalExecutionTemplate_correct (Owner : Type) (e n : Nat) :
    (universalExecutionTemplate Owner).relation (arithmeticStandardModel Owner) e n ↔ W e n := by
  rw [ArithmeticTemplate.relation]
  rw [generalTruth_arithmeticStandardModel _
    (universalExecutionTemplate Owner).arithmetic (fun _ _ => False) false]
  simpa only [universalExecutionTemplate, arithmeticStandardModel,
    ite_true, ite_false, reduceCtorEq] using
      (ArithmeticGraphs.universalExecution_truth false (fun (_ : Owner) _ => False)
        (fun v => if v = 0 then e else if v = 1 then n else 0))

/-- The arithmetic coding object is constructed from the actual trace formula,
    rather than supplied as a hypothesis. -/
def canonicalArithmeticCoding (Owner : Type) : ArithmeticCoding Owner :=
  (universalExecutionTemplate Owner).coding (universalExecutionTemplate_correct Owner)

def canonicalArithmeticCodingCoherent (Owner : Type) :
    CoherentArithmeticCoding (canonicalArithmeticCoding Owner) :=
  (universalExecutionTemplate Owner).codingCoherent (universalExecutionTemplate_correct Owner)

end Alexander313
