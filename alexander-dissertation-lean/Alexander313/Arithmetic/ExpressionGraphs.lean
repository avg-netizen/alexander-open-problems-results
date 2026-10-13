import Alexander313.Arithmetic.ProgramConstructors
import Alexander313.Arithmetic.TraceSequence

/-!
# Hygienic arithmetic graphs for execution-record expressions

Every graph accepts actual argument terms. Its existential witnesses are
chosen above all variables in those terms, so its standard meaning is
independent of accidental binder capture. The record and earlier-record
graphs use the actual nested square pairing and beta convention.

These are positive existential formulas, with true numeral-instance PA
certificates. They do not yet perform the bounded universal check of every
record in a complete execution sequence.
-/

namespace Alexander313

namespace Term

def termsBound : List Term → Nat
  | [] => 0
  | t :: ts => max t.variableBound (termsBound ts)

theorem le_termsBound {t : Term} {ts : List Term} (h : t ∈ ts) :
    t.variableBound ≤ termsBound ts := by
  induction ts with
  | nil => simp at h
  | cons u us ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem eval_update_of_bound (t : Term) (s : Assignment) (x n : Nat)
    (h : t.variableBound ≤ x) : t.eval (Function.update s x n) = t.eval s := by
  have he := generalTermEval_eq_of_agree (arithmeticStandardModel Nat) t
    (Function.update s x n) s (by
      intro v hv
      have hvlt := t.lt_variableBound hv
      have hvne : v ≠ x := by omega
      simp only [Function.update_of_ne hvne])
  simpa only [generalTermEval_arithmeticStandardModel] using he

end Term

namespace ArithmeticGraphs

def less (Owner : Type) (a b : Term) : Formula Owner :=
  let q := Term.termsBound [a, b]
  .ex q (.equal b (.add a (.succ (.var q))))

def le (Owner : Type) (a b : Term) : Formula Owner :=
  let q := Term.termsBound [a, b]
  .ex q (.equal b (.add a (.var q)))

theorem less_positive (Owner : Type) (a b : Term) :
    (less Owner a b).PositiveExistential := by
  simp [less, Formula.PositiveExistential]

theorem le_positive (Owner : Type) (a b : Term) :
    (le Owner a b).PositiveExistential := by
  simp [le, Formula.PositiveExistential]

theorem less_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b : Term) (s : Assignment) :
    truth filtered P (less Owner a b) s ↔ a.eval s < b.eval s := by
  let q := Term.termsBound [a, b]
  have ha : a.variableBound ≤ q := Term.le_termsBound (by simp)
  have hb : b.variableBound ≤ q := Term.le_termsBound (by simp)
  have hea (z : Nat) := a.eval_update_of_bound s q z ha
  have heb (z : Nat) := b.eval_update_of_bound s q z hb
  dsimp only [q] at hea heb
  simp only [less, truth, Term.eval, Function.update_self,
    hea, heb]
  constructor
  · rintro ⟨z, hz⟩
    omega
  · intro h
    exact ⟨b.eval s - a.eval s - 1, by omega⟩

theorem le_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b : Term) (s : Assignment) :
    truth filtered P (le Owner a b) s ↔ a.eval s ≤ b.eval s := by
  let q := Term.termsBound [a, b]
  have ha : a.variableBound ≤ q := Term.le_termsBound (by simp)
  have hb : b.variableBound ≤ q := Term.le_termsBound (by simp)
  have hea (z : Nat) := a.eval_update_of_bound s q z ha
  have heb (z : Nat) := b.eval_update_of_bound s q z hb
  dsimp only [q] at hea heb
  simp only [le, truth, Term.eval, Function.update_self,
    hea, heb]
  constructor
  · rintro ⟨z, hz⟩
    omega
  · intro h
    exact ⟨b.eval s - a.eval s, by omega⟩

def pair (Owner : Type) (a b r : Term) : Formula Owner :=
  .disj
    (.conj (less Owner a b) (.equal r (.add (.mul b b) a)))
    (.conj (le Owner b a) (.equal r (.add (.add (.mul a a) a) b)))

theorem pair_positive (Owner : Type) (a b r : Term) :
    (pair Owner a b r).PositiveExistential :=
  ⟨⟨less_positive Owner a b, trivial⟩, ⟨le_positive Owner b a, trivial⟩⟩

theorem pair_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b r : Term) (s : Assignment) :
    truth filtered P (pair Owner a b r) s ↔ r.eval s = Nat.pair (a.eval s) (b.eval s) := by
  simp only [pair, truth, less_truth, le_truth, Term.eval]
  by_cases h : a.eval s < b.eval s
  · simp [Nat.pair, h, Nat.not_le_of_gt h]
  · have hle : b.eval s ≤ a.eval s := by omega
    simp [Nat.pair, h, hle]

/-- The actual two-payload program constructor uses `4 * pair + tag`. -/
def binaryProgram (Owner : Type) (tag : Nat) (a b r : Term) : Formula Owner :=
  let q := Term.termsBound [a, b, r]
  .ex q (.conj (pair Owner a b (.var q))
    (.equal r (.add (.mul (Term.numeral 4) (.var q)) (Term.numeral tag))))

theorem binaryProgram_positive (Owner : Type) (tag : Nat) (a b r : Term) :
    (binaryProgram Owner tag a b r).PositiveExistential :=
  ⟨pair_positive _ _ _ _, trivial⟩

theorem binaryProgram_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (tag : Nat) (a b r : Term) (s : Assignment) :
    truth filtered P (binaryProgram Owner tag a b r) s ↔
      r.eval s = 4 * Nat.pair (a.eval s) (b.eval s) + tag := by
  let q := Term.termsBound [a, b, r]
  have hval (t : Term) (ht : t ∈ [a, b, r]) (z : Nat) :
      t.eval (Function.update s q z) = t.eval s :=
    t.eval_update_of_bound s q z (Term.le_termsBound ht)
  dsimp only [q] at hval
  simp only [binaryProgram, truth, pair_truth,
    hval a (by simp), hval b (by simp), hval r (by simp),
    Term.eval, Term.eval_numeral, Function.update_self]
  constructor
  · rintro ⟨p, rfl, hr⟩
    exact hr
  · intro hr
    exact ⟨_, rfl, hr⟩

def beta (Owner : Type) (a b i r : Term) : Formula Owner :=
  let q := Term.termsBound [a, b, i, r]
  let modulus : Term := .succ (.mul (.succ i) b)
  .ex q (.conj (.equal a (.add (.mul (.var q) modulus) r))
    (.ex (q + 1) (.equal modulus (.add r (.succ (.var (q + 1)))))))

theorem beta_positive (Owner : Type) (a b i r : Term) :
    (beta Owner a b i r).PositiveExistential := by
  simp [beta, Formula.PositiveExistential]

theorem beta_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b i r : Term) (s : Assignment) :
    truth filtered P (beta Owner a b i r) s ↔
      a.eval s % ((i.eval s + 1) * b.eval s + 1) = r.eval s := by
  let q := Term.termsBound [a, b, i, r]
  have hsingle (t : Term) (ht : t ∈ [a, b, i, r]) (z : Nat) :
      t.eval (Function.update s q z) = t.eval s :=
    t.eval_update_of_bound s q z (Term.le_termsBound ht)
  have hdouble (t : Term) (ht : t ∈ [a, b, i, r]) (z w : Nat) :
      t.eval (Function.update (Function.update s q z) (q + 1) w) = t.eval s := by
    have htq := Term.le_termsBound ht
    rw [t.eval_update_of_bound _ (q + 1) w (by omega), hsingle t ht z]
  dsimp only [q] at hsingle hdouble
  simp only [beta, truth, Term.eval, Function.update_self,
    hsingle a (by simp), hsingle b (by simp), hsingle i (by simp), hsingle r (by simp),
    hdouble b (by simp), hdouble i (by simp), hdouble r (by simp)]
  exact remainder_witness_iff _ _ _ (by omega)

/-- A record is the actual nested encoding of cutoff, program code,
    input and output. The two internal values have fresh variable names. -/
def record (Owner : Type) (fuel program input output row : Term) : Formula Owner :=
  let q := Term.termsBound [fuel, program, input, output, row]
  .ex q (.ex (q + 1) (.conj (pair Owner input output (.var (q + 1)))
    (.conj (pair Owner program (.var (q + 1)) (.var q))
      (pair Owner fuel (.var q) row))))

theorem record_positive (Owner : Type) (fuel program input output row : Term) :
    (record Owner fuel program input output row).PositiveExistential :=
  ⟨pair_positive _ _ _ _, ⟨pair_positive _ _ _ _, pair_positive _ _ _ _⟩⟩

theorem record_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (fuel program input output row : Term) (s : Assignment) :
    truth filtered P (record Owner fuel program input output row) s ↔
      row.eval s = Nat.pair (fuel.eval s)
        (Nat.pair (program.eval s) (Nat.pair (input.eval s) (output.eval s))) := by
  let q := Term.termsBound [fuel, program, input, output, row]
  have hval (t : Term) (ht : t ∈ [fuel, program, input, output, row]) (z w : Nat) :
      t.eval (Function.update (Function.update s q z) (q + 1) w) = t.eval s := by
    have htq := Term.le_termsBound ht
    rw [t.eval_update_of_bound _ (q + 1) w (by omega),
      t.eval_update_of_bound s q z htq]
  have hqne : q ≠ q + 1 := by omega
  dsimp only [q] at hval hqne
  simp only [record, truth, pair_truth,
    hval fuel (by simp), hval program (by simp), hval input (by simp),
    hval output (by simp), hval row (by simp), Term.eval,
    Function.update_self, Function.update_of_ne hqne]
  constructor
  · rintro ⟨z, w, rfl, rfl, hr⟩
    exact hr
  · intro hr
    exact ⟨_, _, rfl, rfl, hr⟩

/-- A required child record must occur at a strictly earlier beta position. -/
def earlier (Owner : Type) (a b index fuel program input output : Term) : Formula Owner :=
  let q := Term.termsBound [a, b, index, fuel, program, input, output]
  .ex q (.ex (q + 1) (.conj (less Owner (.var q) index)
    (.conj (record Owner fuel program input output (.var (q + 1)))
      (beta Owner a b (.var q) (.var (q + 1))))))

theorem earlier_positive (Owner : Type) (a b index fuel program input output : Term) :
    (earlier Owner a b index fuel program input output).PositiveExistential :=
  ⟨less_positive _ _ _, ⟨record_positive _ _ _ _ _ _, beta_positive _ _ _ _ _⟩⟩

theorem earlier_truth {Owner : Type} (filtered : Bool) (P : RawPredicates Owner)
    (a b index fuel program input output : Term) (s : Assignment) :
    truth filtered P (earlier Owner a b index fuel program input output) s ↔
      ∃ j, j < index.eval s ∧
        a.eval s % ((j + 1) * b.eval s + 1) =
          Nat.pair (fuel.eval s)
            (Nat.pair (program.eval s) (Nat.pair (input.eval s) (output.eval s))) := by
  let q := Term.termsBound [a, b, index, fuel, program, input, output]
  have hval (t : Term) (ht : t ∈ [a, b, index, fuel, program, input, output]) (j r : Nat) :
      t.eval (Function.update (Function.update s q j) (q + 1) r) = t.eval s := by
    have htq := Term.le_termsBound ht
    rw [t.eval_update_of_bound _ (q + 1) r (by omega),
      t.eval_update_of_bound s q j htq]
  have hqne : q ≠ q + 1 := by omega
  dsimp only [q] at hval hqne
  simp only [earlier, truth, less_truth, record_truth, beta_truth,
    hval a (by simp), hval b (by simp), hval index (by simp),
    hval fuel (by simp), hval program (by simp), hval input (by simp),
    hval output (by simp), Term.eval, Function.update_self, Function.update_of_ne hqne]
  constructor
  · rintro ⟨j, r, hj, rfl, hr⟩
    exact ⟨j, hj, hr⟩
  · rintro ⟨j, hj, hr⟩
    exact ⟨j, _, hj, rfl, hr⟩

theorem pa_proves_record_instance (Owner : Type) (r : TraceRecord) :
    Provable (PAInstance Owner)
      ((record Owner (Term.numeral r.fuel) (Term.numeral (Encodable.encode r.program))
        (Term.numeral r.input) (Term.numeral r.output) (Term.numeral r.code)).close
          (fun _ => 0)) := by
  apply pa_proves_positive_numeral_instance _ (record_positive _ _ _ _ _ _)
  rw [record_truth]
  simp only [Term.eval_numeral, TraceRecord.code]

end ArithmeticGraphs

end Alexander313
