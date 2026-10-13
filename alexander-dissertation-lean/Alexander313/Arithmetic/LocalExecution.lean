import Alexander313.Arithmetic.ExpressionGraphs

/-!
# The arithmetic local execution-rule checker

The seven ports are cutoff, program code, input, output, the two beta
parameters and the current record position. The formula checks one of the
ten actual `evaln` rules and requires every child at a smaller position.
All auxiliary values and all graph witnesses are existential.
-/

namespace Alexander313

def EncodedEarlier (a b i fuel program input output : Nat) : Prop :=
  ∃ j, j < i ∧ a % ((j + 1) * b + 1) =
    Nat.pair fuel (Nat.pair program (Nat.pair input output))

/-- An explicit numerical disjunction of the ten evaluator rules.
    The shared existential variables may be unused in a particular rule. -/
def EncodedTraceStep (a b i fuel program input output : Nat) : Prop :=
  ∃ k c d x m u v p q r,
    fuel = k + 1 ∧ input ≤ k ∧
    ((program = 0 ∧ output = 0) ∨
    (program = 1 ∧ output = input + 1) ∨
    (program = 2 ∧ input = Nat.pair x m ∧ output = x) ∨
    (program = 3 ∧ input = Nat.pair x m ∧ output = m) ∨
    (program = 4 * Nat.pair c d + 4 ∧ output = Nat.pair u v ∧
      EncodedEarlier a b i fuel c input u ∧ EncodedEarlier a b i fuel d input v) ∨
    (program = 4 * Nat.pair c d + 6 ∧
      EncodedEarlier a b i fuel d input u ∧ EncodedEarlier a b i fuel c u output) ∨
    (program = 4 * Nat.pair c d + 5 ∧ input = Nat.pair x 0 ∧
      EncodedEarlier a b i fuel c x output) ∨
    (program = 4 * Nat.pair c d + 5 ∧ input = Nat.pair x (m + 1) ∧
      p = Nat.pair x m ∧ q = Nat.pair m u ∧ r = Nat.pair x q ∧
      EncodedEarlier a b i k program p u ∧ EncodedEarlier a b i fuel d r output) ∨
    (program = 4 * c + 7 ∧ input = Nat.pair x m ∧ output = m ∧
      EncodedEarlier a b i fuel c input 0) ∨
    (program = 4 * c + 7 ∧ input = Nat.pair x m ∧ p = Nat.pair x (m + 1) ∧
      EncodedEarlier a b i fuel c input (u + 1) ∧
      EncodedEarlier a b i k program p output))

private theorem ofNat_pair_program (c d : Nat) :
    Nat.Partrec.Code.ofNatCode (4 * Nat.pair c d + 4) =
      .pair (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d) := by
  have h := program_pair_encoding (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d)
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.encode_ofNat] at h
  rw [← h]
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode]

private theorem ofNat_comp_program (c d : Nat) :
    Nat.Partrec.Code.ofNatCode (4 * Nat.pair c d + 6) =
      .comp (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d) := by
  have h := program_comp_encoding (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d)
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.encode_ofNat] at h
  rw [← h]
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode]

private theorem ofNat_prec_program (c d : Nat) :
    Nat.Partrec.Code.ofNatCode (4 * Nat.pair c d + 5) =
      .prec (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d) := by
  have h := program_prec_encoding (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d)
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.encode_ofNat] at h
  rw [← h]
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode]

private theorem ofNat_search_program (c : Nat) :
    Nat.Partrec.Code.ofNatCode (4 * c + 7) = .rfind' (Nat.Partrec.Code.ofNatCode c) := by
  have h := program_rfind_encoding (Nat.Partrec.Code.ofNatCode c)
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.encode_ofNat] at h
  rw [← h]
  simp only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode]

theorem EncodedEarlier_record (a b i fuel code input output : Nat) :
    EncodedEarlier a b i fuel code input output ↔
      ∃ j, j < i ∧ a % ((j + 1) * b + 1) =
        (⟨fuel, Nat.Partrec.Code.ofNatCode code, input, output⟩ : TraceRecord).code := by
  simp only [EncodedEarlier, TraceRecord.code, ← Nat.Partrec.Code.ofNatCode_eq,
    Denumerable.encode_ofNat]

theorem encodedTraceStep_to_local (a b i fuel program input output : Nat)
    (h : EncodedTraceStep a b i fuel program input output) :
    LocalTraceStep (fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
      ⟨fuel, Nat.Partrec.Code.ofNatCode program, input, output⟩ := by
  obtain ⟨k, c, d, x, m, u, v, p, q, r, hfuel, hn, h⟩ := h
  subst fuel
  rcases h with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    simpa only [Nat.Partrec.Code.ofNatCode] using
      (LocalTraceStep.zero (earlier := fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
        k input hn)
  · obtain ⟨rfl, rfl⟩ := h
    simpa only [Nat.Partrec.Code.ofNatCode] using
      (LocalTraceStep.succ (earlier := fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
        k input hn)
  · obtain ⟨hprogram, hinput, houtput⟩ := h
    subst program input output
    simpa only [Nat.Partrec.Code.ofNatCode, Nat.unpair_pair] using
      (LocalTraceStep.left (earlier := fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
        k (Nat.pair x m) hn)
  · obtain ⟨hprogram, hinput, houtput⟩ := h
    subst program input output
    simpa only [Nat.Partrec.Code.ofNatCode, Nat.unpair_pair] using
      (LocalTraceStep.right (earlier := fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
        k (Nat.pair x m) hn)
  · obtain ⟨rfl, rfl, hc, hd⟩ := h
    rw [ofNat_pair_program]
    exact .pair k _ _ input u v hn
      ((EncodedEarlier_record _ _ _ _ _ _ _).mp hc)
      ((EncodedEarlier_record _ _ _ _ _ _ _).mp hd)
  · obtain ⟨rfl, hd, hc⟩ := h
    rw [ofNat_comp_program]
    exact .comp k _ _ input u output hn
      ((EncodedEarlier_record _ _ _ _ _ _ _).mp hd)
      ((EncodedEarlier_record _ _ _ _ _ _ _).mp hc)
  · obtain ⟨rfl, rfl, hc⟩ := h
    rw [ofNat_prec_program]
    exact .precZero k _ _ x output hn
      ((EncodedEarlier_record _ _ _ _ _ _ _).mp hc)
  · obtain ⟨he, rfl, rfl, rfl, rfl, hp, hd⟩ := h
    have he' : Nat.Partrec.Code.ofNatCode program =
        .prec (Nat.Partrec.Code.ofNatCode c) (Nat.Partrec.Code.ofNatCode d) := by
      rw [he, ofNat_prec_program]
    rw [he']
    apply LocalTraceStep.precSucc k _ _ x m u output hn
    · simpa only [he'] using (EncodedEarlier_record _ _ _ _ _ _ _).mp hp
    · exact (EncodedEarlier_record _ _ _ _ _ _ _).mp hd
  · obtain ⟨hprogram, hinput, houtput, hc⟩ := h
    subst program input output
    rw [ofNat_search_program]
    exact .searchZero k _ x m hn
      ((EncodedEarlier_record _ _ _ _ _ _ _).mp hc)
  · obtain ⟨he, rfl, rfl, hc, hs⟩ := h
    have he' : Nat.Partrec.Code.ofNatCode program = .rfind' (Nat.Partrec.Code.ofNatCode c) := by
      rw [he, ofNat_search_program]
    rw [he']
    apply LocalTraceStep.searchSucc k _ x m u output hn
    · exact (EncodedEarlier_record _ _ _ _ _ _ _).mp hc
    · simpa only [he'] using (EncodedEarlier_record _ _ _ _ _ _ _).mp hs

theorem localTraceStep_to_encoded (a b i : Nat) {s : TraceRecord}
    (h : LocalTraceStep (fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code) s) :
    EncodedTraceStep a b i s.fuel (Encodable.encode s.program) s.input s.output := by
  have child {k : Nat} {c : Program} {n v : Nat}
      (h : ∃ j, j < i ∧ a % ((j + 1) * b + 1) = (⟨k, c, n, v⟩ : TraceRecord).code) :
      EncodedEarlier a b i k (Encodable.encode c) n v := h
  cases h with
  | zero k n hn =>
    exact ⟨k, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, hn, Or.inl ⟨rfl, rfl⟩⟩
  | succ k n hn =>
    exact ⟨k, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, hn, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | left k n hn =>
    refine ⟨k, 0, 0, n.unpair.1, n.unpair.2, 0, 0, 0, 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inl ⟨rfl, (Nat.pair_unpair n).symm, rfl⟩))
  | right k n hn =>
    refine ⟨k, 0, 0, n.unpair.1, n.unpair.2, 0, 0, 0, 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, (Nat.pair_unpair n).symm, rfl⟩)))
  | pair k c d n u v hn hc hd =>
    refine ⟨k, Encodable.encode c, Encodable.encode d, 0, 0, u, v, 0, 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨program_pair_encoding c d, rfl, child hc, child hd⟩))))
  | comp k c d n u v hn hd hc =>
    refine ⟨k, Encodable.encode c, Encodable.encode d, 0, 0, u, 0, 0, 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨program_comp_encoding c d, child hd, child hc⟩)))))
  | precZero k c d x v hn hc =>
    refine ⟨k, Encodable.encode c, Encodable.encode d, x, 0, 0, 0, 0, 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨program_prec_encoding c d, rfl, child hc⟩))))))
  | precSucc k c d x m u v hn hp hd =>
    refine ⟨k, Encodable.encode c, Encodable.encode d, x, m, u, 0,
      Nat.pair x m, Nat.pair m u, Nat.pair x (Nat.pair m u), rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨program_prec_encoding c d, rfl, rfl, rfl, rfl, child hp, child hd⟩)))))))
  | searchZero k c x m hn hc =>
    refine ⟨k, Encodable.encode c, 0, x, m, 0, 0, 0, 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨program_rfind_encoding c, rfl, rfl, child hc⟩))))))))
  | searchSucc k c x m z v hn hc hs =>
    refine ⟨k, Encodable.encode c, 0, x, m, z, 0, Nat.pair x (m + 1), 0, 0, rfl, hn, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨program_rfind_encoding c, rfl, rfl, child hc, child hs⟩))))))))

theorem encodedTraceStep_iff_local (a b i fuel program input output : Nat) :
    EncodedTraceStep a b i fuel program input output ↔
    LocalTraceStep (fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
      ⟨fuel, Nat.Partrec.Code.ofNatCode program, input, output⟩ := by
  refine ⟨encodedTraceStep_to_local _ _ _ _ _ _ _, fun h => ?_⟩
  simpa only [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.encode_ofNat] using localTraceStep_to_encoded a b i h

namespace ArithmeticGraphs

def existsVariables {Owner : Type} : List Nat → Formula Owner → Formula Owner
  | [], φ => φ
  | x :: xs, φ => .ex x (existsVariables xs φ)

/-- The explicit local-rule formula, with ports 0 through 6. -/
def localExecution (Owner : Type) : Formula Owner :=
  let fuel : Term := .var 0
  let program : Term := .var 1
  let input : Term := .var 2
  let output : Term := .var 3
  let a : Term := .var 4
  let b : Term := .var 5
  let i : Term := .var 6
  let k : Term := .var 7
  let c : Term := .var 8
  let d : Term := .var 9
  let x : Term := .var 10
  let m : Term := .var 11
  let u : Term := .var 12
  let v : Term := .var 13
  let p : Term := .var 14
  let q : Term := .var 15
  let r : Term := .var 16
  existsVariables [7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    (.conj (.equal fuel (.succ k)) (.conj (le Owner input k)
    (.disj (.conj (.equal program .zero) (.equal output .zero))
    (.disj (.conj (.equal program (Term.numeral 1)) (.equal output (.succ input)))
    (.disj (.conj (.equal program (Term.numeral 2))
      (.conj (pair Owner x m input) (.equal output x)))
    (.disj (.conj (.equal program (Term.numeral 3))
      (.conj (pair Owner x m input) (.equal output m)))
    (.disj (.conj (binaryProgram Owner 4 c d program)
      (.conj (pair Owner u v output)
        (.conj (earlier Owner a b i fuel c input u) (earlier Owner a b i fuel d input v))))
    (.disj (.conj (binaryProgram Owner 6 c d program)
      (.conj (earlier Owner a b i fuel d input u) (earlier Owner a b i fuel c u output)))
    (.disj (.conj (binaryProgram Owner 5 c d program)
      (.conj (pair Owner x .zero input) (earlier Owner a b i fuel c x output)))
    (.disj (.conj (binaryProgram Owner 5 c d program)
      (.conj (pair Owner x (.succ m) input) (.conj (pair Owner x m p)
      (.conj (pair Owner m u q) (.conj (pair Owner x q r)
        (.conj (earlier Owner a b i k program p u) (earlier Owner a b i fuel d r output)))))))
    (.disj (.conj (.equal program (.add (.mul (Term.numeral 4) c) (Term.numeral 7)))
      (.conj (pair Owner x m input) (.conj (.equal output m)
        (earlier Owner a b i fuel c input .zero))))
    (.conj (.equal program (.add (.mul (Term.numeral 4) c) (Term.numeral 7)))
      (.conj (pair Owner x m input) (.conj (pair Owner x (.succ m) p)
        (.conj (earlier Owner a b i fuel c input (.succ u))
          (earlier Owner a b i k program p output))))))))))))))))

theorem localExecution_variables (Owner : Type) :
    (localExecution Owner).freeVars = {0, 1, 2, 3, 4, 5, 6} := by
  ext v
  simp [localExecution, existsVariables, less, le, pair, binaryProgram, earlier, record, beta,
    Formula.freeVars, Term.freeVars, Term.termsBound, Term.variableBound] <;> omega

theorem localExecution_positive (Owner : Type) :
    (localExecution Owner).PositiveExistential := by
  simp only [localExecution, existsVariables, Formula.PositiveExistential,
    le_positive, pair_positive, binaryProgram_positive, earlier_positive, and_self]

theorem localExecution_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (s : Assignment) :
    truth filtered P (localExecution Owner) s ↔
      EncodedTraceStep (s 4) (s 5) (s 6) (s 0) (s 1) (s 2) (s 3) := by
  simp [localExecution, existsVariables, truth, le_truth, pair_truth,
    binaryProgram_truth, earlier_truth, Term.eval, Function.update_apply,
    EncodedTraceStep, EncodedEarlier]

theorem localExecution_actual_rule {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (s : Assignment) :
    truth filtered P (localExecution Owner) s ↔
      LocalTraceStep (fun r => ∃ j, j < s 6 ∧ s 4 % ((j + 1) * s 5 + 1) = r.code)
        ⟨s 0, Nat.Partrec.Code.ofNatCode (s 1), s 2, s 3⟩ := by
  rw [localExecution_truth, encodedTraceStep_iff_local]

theorem pa_proves_local_execution_instance (Owner : Type) (s : Assignment)
    (h : EncodedTraceStep (s 4) (s 5) (s 6) (s 0) (s 1) (s 2) (s 3)) :
    Provable (PAInstance Owner) ((localExecution Owner).close s) :=
  pa_proves_positive_numeral_instance _ (localExecution_positive Owner) s
    ((localExecution_truth false (fun _ _ => False) s).mpr h)

end ArithmeticGraphs

end Alexander313
