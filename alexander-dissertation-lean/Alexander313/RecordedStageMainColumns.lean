import Alexander313.RecordedStageMarkers

/-!
# Literal main-row columns in the actual stage interpretation

For every code row the nonactive, nonexternal target is a live head. Its raw
test is exactly the original source-family unary column, with the same formula,
input variable and code numeral. The row is therefore true precisely when each
accepted source assertion has a true recorded body. Marker padding introduces
no additional truth condition, by the actual marker theorem.

The mechanicalness reduction retains the literal existential and universal
binders and all parameter assignments. It identifies the remaining column
condition, rather than assuming that the filtered column is recursively
enumerable. Code rows with valid source bodies are actually verified from the
constructed stage model, even when those bodies contain active modal heads.
The same verification covers every finite consequence of modal PA. For a purely
arithmetic body, the old target's soundness alone suffices, without active-query
recovery or indexed-cut soundness.

General source-body truth, prescribed fixed-label reverse transport and guarded
main-row stage soundness remain separate. None is assumed as a new contract.
-/

namespace Alexander313

theorem arithmetic_record_truth {Owner Label : Type}
    (P : RawPredicates Owner) (Q : RawPredicates (RecordedHead Owner Label))
    (filtered : Bool) (φ : Formula Owner) (hφ : φ.Arithmetic)
    (head : Owner → Shape Owner → RecordedHead Owner Label) (s : Assignment) :
    truth filtered Q (φ.record head) s ↔ truth filtered P φ s := by
  revert hφ
  induction φ generalizing s with
  | falsum => intro _; rfl
  | equal t u => intro _; rfl
  | imp φ ψ ihφ ihψ =>
    intro hφ
    exact imp_congr (ihφ s hφ.1) (ihψ s hφ.2)
  | conj φ ψ ihφ ihψ =>
    intro hφ
    exact and_congr (ihφ s hφ.1) (ihψ s hφ.2)
  | disj φ ψ ihφ ihψ =>
    intro hφ
    exact or_congr (ihφ s hφ.1) (ihψ s hφ.2)
  | neg φ ih => intro hφ; exact not_congr (ih s hφ)
  | all x φ ih =>
    intro hφ
    exact forall_congr' (fun n => ih (Function.update s x n) hφ)
  | ex x φ ih =>
    intro hφ
    exact exists_congr (fun n => ih (Function.update s x n) hφ)
  | know a φ ih => intro hφ; exact False.elim hφ

theorem PAInstance.record {Owner Label : Type} {φ : Formula Owner}
    (hφ : PAInstance Owner φ) (head : Owner → Shape Owner → RecordedHead Owner Label) :
    PAInstance (RecordedHead Owner Label) (φ.record head) := by
  cases hφ with
  | successor_ne_zero => exact .successor_ne_zero
  | successor_injective => exact .successor_injective
  | add_zero => exact .add_zero
  | add_succ => exact .add_succ
  | mul_zero => exact .mul_zero
  | mul_succ => exact .mul_succ
  | induction ψ x =>
    simpa only [Formula.record_universalClosure, Formula.record,
      Formula.record_subst, Formula.record_substTerm] using
      PAInstance.induction (ψ.record head) x

theorem truth_all_foldr_elim_self {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (xs : List Nat) (φ : Formula Owner) (s : Assignment)
    (h : truth filtered P (xs.foldr Formula.all φ) s) : truth filtered P φ s := by
  revert h
  induction xs with
  | nil => intro h; exact h
  | cons x xs ih =>
    intro h
    have he : Function.update s x (s x) = s := by
      funext y
      by_cases hy : y = x
      · subst y
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hy]
    apply ih
    simpa only [he] using h (s x)

theorem truth_universalClosure_iff_all {Owner : Type} (filtered : Bool)
    (P : RawPredicates Owner) (φ : Formula Owner) :
    (∀ s, truth filtered P φ.universalClosure s) ↔ ∀ s, truth filtered P φ s :=
  ⟨fun h s => truth_all_foldr_elim_self filtered P _ φ s (h s),
    fun h => truth_universalClosure filtered P φ h⟩

namespace RecordedStage

variable {Label : Type} [LinearOrder Label] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (A E : Finset Nat)
    (R₁ R₂ : Label → Label → Prop)

theorem mainHeads_outside_live (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (j : Nat) (sh : Shape Nat)
    (outsideA : j ∉ A) (outsideE : j ∉ E) :
    mainHeads A E H labels j sh = .live j := by
  simp only [mainHeads, maskedHeads, outsideE, outsideA, ↓reduceIte]

theorem recorded_live_know_iff (P : RawPredicates Nat)
    (head : Nat → Shape Nat → RecordedHead Nat Label)
    (erase : ∀ a sh, (head a sh).erase = a) (j : Nat) (φ : Formula Nat)
    (live : head j φ.shape = .live j) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) ((Formula.know j φ).record head) s ↔
      P j (φ.close s) ∧ filteredTruth (predicates C A E R₁ R₂ P) (φ.record head) s := by
  rw [Formula.record, live]
  exact and_congr (live_query_record P (cuts C A E R₁ R₂) head erase j φ s) Iff.rfl

theorem recorded_member_truth (P : RawPredicates Nat)
    (head : Nat → Shape Nat → RecordedHead Nat Label) (e x : Term) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) ((C.arithmetic.member e x).record head) s ↔
      W (e.eval s) (x.eval s) :=
  (arithmetic_record_truth P _ true _ (C.arithmetic.arithmetic e x) head s).trans
    (C.arithmetic.correct e x P true s)

/-- The fixed numeral is arbitrary here. No new source column is compiled. -/
theorem recorded_code_truth_iff (P : RawPredicates Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (j : Nat) (outsideA : j ∉ A) (outsideE : j ∉ E)
    (φ : UnaryFormula Nat) (e : Nat) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      ((codeSentence C.arithmetic j φ e).record (mainHeads A E H labels)) s ↔
      ∀ n, ((P j (φ.body.close (Function.update s φ.input n)) ∧
        filteredTruth (predicates C A E R₁ R₂ P)
          (φ.body.record (mainHeads A E H labels)) (Function.update s φ.input n)) ↔ W e n) := by
  change (∀ n, (filteredTruth (predicates C A E R₁ R₂ P)
      ((Formula.know j φ.body).record (mainHeads A E H labels))
      (Function.update s φ.input n) →
      filteredTruth (predicates C A E R₁ R₂ P)
        ((C.arithmetic.member (Term.numeral e) (.var φ.input)).record
          (mainHeads A E H labels)) (Function.update s φ.input n)) ∧
    (filteredTruth (predicates C A E R₁ R₂ P)
        ((C.arithmetic.member (Term.numeral e) (.var φ.input)).record
          (mainHeads A E H labels)) (Function.update s φ.input n) →
      filteredTruth (predicates C A E R₁ R₂ P)
        ((Formula.know j φ.body).record (mainHeads A E H labels))
        (Function.update s φ.input n))) ↔ _
  apply forall_congr'
  intro n
  rw [recorded_live_know_iff C A E R₁ R₂ P _ (mainHeads_erase A E H labels) j φ.body
    (mainHeads_outside_live A E H labels j φ.body.shape outsideA outsideE),
    recorded_member_truth C A E R₁ R₂ P]
  simp only [Term.eval_numeral, Term.eval, Function.update_self]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- Exact local-truth reduction for every literal core/subordinate code row.
The source unary-column equation is already a theorem of the real compiler. -/
theorem source_code_truth_iff (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (j : Nat) (outsideA : j ∉ A) (outsideE : j ∉ E)
    (φ : UnaryFormula Nat) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
      ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
        (mainHeads A E H labels)) s ↔
      ∀ n, C.family.effective.proves j (φ.body.close (Function.update s φ.input n)) →
        filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
          (φ.body.record (mainHeads A E H labels)) (Function.update s φ.input n) := by
  rw [recorded_code_truth_iff C A E R₁ R₂ _ H labels j outsideA outsideE]
  apply forall_congr'
  intro n
  have hc := C.family.unaryColumn_equation j φ (Function.update s φ.input n)
  simp only [Function.update_self] at hc
  rw [hc]
  tauto

theorem source_code_padding_truth_iff (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (a j : Nat) (ms : List (Label × Nat))
    (outsideA : j ∉ A) (outsideE : j ∉ E) (φ : UnaryFormula Nat) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s ↔
      ∀ n, C.family.effective.proves j (φ.body.close (Function.update s φ.input n)) →
        filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
          (φ.body.record (mainHeads A E H labels)) (Function.update s φ.input n) :=
  (markerPadding_truth_iff C A E R₁ R₂ _ a ms _ s).trans
    (source_code_truth_iff C A E R₁ R₂ H labels j outsideA outsideE φ s)

/-- A concrete verified main-code class: source validity is transported by the
actual recording map and realized in the constructed full-cut model. -/
theorem source_code_valid_truth (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (a j : Nat) (ms : List (Label × Nat))
    (outsideA : j ∉ A) (outsideE : j ∉ E) (φ : UnaryFormula Nat)
    (hv : Valid φ.body) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s := by
  apply (source_code_padding_truth_iff C A E R₁ R₂ H labels a j ms
    outsideA outsideE φ s).mpr
  intro n _
  exact validity_truth C A E R₁ R₂ _ C.family.rawAlphabetic _
    (hv.record (mainHeads A E H labels)) (Function.update s φ.input n)

theorem pa_recorded_truth (head : Nat → Shape Nat → RecordedHead Nat Label)
    {φ : Formula Nat} (hp : Provable (PAInstance Nat) φ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves) (φ.record head) s := by
  have hr : Provable (PAInstance (RecordedHead Nat Label)) (φ.record head) :=
    hp.record head (fun _ h => h.record head)
  apply ((sourceRealization C A E R₁ R₂).truth_eq (φ.record head) s).mp
  apply provable_sound (sourceRealization C A E R₁ R₂).model hr
  intro θ hθ t
  exact ((sourceRealization C A E R₁ R₂).truth_eq θ t).mpr (truth_pa_instance true _ hθ t)

/-- Modal PA induction is transported literally, including its actual numerical
base and successor substitutions. No soundness of any source machine is used. -/
theorem source_code_pa_truth (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (a j : Nat) (ms : List (Label × Nat))
    (outsideA : j ∉ A) (outsideE : j ∉ E) (φ : UnaryFormula Nat)
    (hp : Provable (PAInstance Nat) φ.body) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s := by
  apply (source_code_padding_truth_iff C A E R₁ R₂ H labels a j ms
    outsideA outsideE φ s).mpr
  intro n _
  exact pa_recorded_truth C A E R₁ R₂ (mainHeads A E H labels) hp
    (Function.update s φ.input n)

theorem source_code_arithmetic_truth (H : Finset (Nat × Shape Nat))
    (labels : Nat → Shape Nat → Label) (a j : Nat) (ms : List (Label × Nat))
    (outsideA : j ∉ A) (outsideE : j ∉ E) (φ : UnaryFormula Nat)
    (hφ : φ.body.Arithmetic) (old_sound : RawSound C.family.effective.proves j)
    (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ C.family.effective.proves)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s := by
  apply (source_code_padding_truth_iff C A E R₁ R₂ H labels a j ms
    outsideA outsideE φ s).mpr
  intro n hn
  exact (arithmetic_record_truth C.family.effective.proves _ true φ.body hφ
    (mainHeads A E H labels) (Function.update s φ.input n)).mpr
      (old_sound φ.body (Function.update s φ.input n) hn)

/-- In a genericity application only the old code target is retained in full.
Other old predicates may be arbitrary; no agreement under the body is assumed. -/
theorem retained_code_padding_truth_iff (P : RawPredicates Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a j : Nat) (ms : List (Label × Nat)) (outsideA : j ∉ A) (outsideE : j ∉ E)
    (retained : ∀ θ, P j θ ↔ C.family.effective.proves j θ)
    (φ : UnaryFormula Nat) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s ↔
      ∀ n, P j (φ.body.close (Function.update s φ.input n)) →
        filteredTruth (predicates C A E R₁ R₂ P)
          (φ.body.record (mainHeads A E H labels)) (Function.update s φ.input n) := by
  rw [markerPadding_truth_iff, recorded_code_truth_iff C A E R₁ R₂ P H labels j
    outsideA outsideE]
  apply forall_congr'
  intro n
  have hc := C.family.unaryColumn_equation j φ (Function.update s φ.input n)
  simp only [Function.update_self] at hc
  rw [hc, ← retained]
  tauto

theorem retained_code_valid_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a j : Nat) (ms : List (Label × Nat)) (outsideA : j ∉ A) (outsideE : j ∉ E)
    (retained : ∀ θ, P j θ ↔ C.family.effective.proves j θ)
    (φ : UnaryFormula Nat) (hv : Valid φ.body) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s := by
  apply (retained_code_padding_truth_iff C A E R₁ R₂ P H labels a j ms
    outsideA outsideE retained φ s).mpr
  intro n _
  exact validity_truth C A E R₁ R₂ P hP _ (hv.record (mainHeads A E H labels))
    (Function.update s φ.input n)

theorem pa_recorded_truth_of_alphabetic (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (head : Nat → Shape Nat → RecordedHead Nat Label) {φ : Formula Nat}
    (hp : Provable (PAInstance Nat) φ) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P) (φ.record head) s := by
  have hr : Provable (PAInstance (RecordedHead Nat Label)) (φ.record head) :=
    hp.record head (fun _ h => h.record head)
  apply ((filteredRealization C A E R₁ R₂ P hP).truth_eq (φ.record head) s).mp
  apply provable_sound (filteredRealization C A E R₁ R₂ P hP).model hr
  intro θ hθ t
  exact ((filteredRealization C A E R₁ R₂ P hP).truth_eq θ t).mpr
    (truth_pa_instance true _ hθ t)

theorem retained_code_pa_truth (P : RawPredicates Nat) (hP : RawAlphabetic P)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a j : Nat) (ms : List (Label × Nat)) (outsideA : j ∉ A) (outsideE : j ∉ E)
    (retained : ∀ θ, P j θ ↔ C.family.effective.proves j θ)
    (φ : UnaryFormula Nat) (hp : Provable (PAInstance Nat) φ.body) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s := by
  apply (retained_code_padding_truth_iff C A E R₁ R₂ P H labels a j ms
    outsideA outsideE retained φ s).mpr
  intro n _
  exact pa_recorded_truth_of_alphabetic C A E R₁ R₂ P hP (mainHeads A E H labels) hp
    (Function.update s φ.input n)

theorem retained_code_arithmetic_truth (P : RawPredicates Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a j : Nat) (ms : List (Label × Nat)) (outsideA : j ∉ A) (outsideE : j ∉ E)
    (retained : ∀ θ, P j θ ↔ C.family.effective.proves j θ)
    (φ : UnaryFormula Nat) (hφ : φ.body.Arithmetic) (old_sound : RawSound P j)
    (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      (markerPadding a ms
        ((codeSentence C.arithmetic j φ (C.family.unaryColumnIndex j φ)).record
          (mainHeads A E H labels))) s := by
  apply (retained_code_padding_truth_iff C A E R₁ R₂ P H labels a j ms
    outsideA outsideE retained φ s).mpr
  intro n hn
  exact (arithmetic_record_truth P _ true φ.body hφ (mainHeads A E H labels)
    (Function.update s φ.input n)).mpr (old_sound φ.body (Function.update s φ.input n) hn)

/-- Literal mechanicalness matrix, before the surrounding universal closure.
The existential witness may depend on all the displayed parameter values. -/
theorem recorded_mechanical_matrix_truth_iff (P : RawPredicates Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (j x e : Nat) (distinct : e ≠ x) (φ : Formula Nat) (s : Assignment) :
    filteredTruth (predicates C A E R₁ R₂ P)
      ((Formula.ex e (.all x (.iff (.know j φ)
        (C.arithmetic.member (.var e) (.var x))))).record (mainHeads A E H labels)) s ↔
      ∃ c, ∀ n, (filteredTruth (predicates C A E R₁ R₂ P)
        ((Formula.know j φ).record (mainHeads A E H labels))
        (Function.update (Function.update s e c) x n) ↔ W c n) := by
  change (∃ c, ∀ n, (filteredTruth (predicates C A E R₁ R₂ P)
      ((Formula.know j φ).record (mainHeads A E H labels))
      (Function.update (Function.update s e c) x n) →
      filteredTruth (predicates C A E R₁ R₂ P)
        ((C.arithmetic.member (.var e) (.var x)).record (mainHeads A E H labels))
        (Function.update (Function.update s e c) x n)) ∧
    (filteredTruth (predicates C A E R₁ R₂ P)
        ((C.arithmetic.member (.var e) (.var x)).record (mainHeads A E H labels))
        (Function.update (Function.update s e c) x n) →
      filteredTruth (predicates C A E R₁ R₂ P)
        ((Formula.know j φ).record (mainHeads A E H labels))
        (Function.update (Function.update s e c) x n))) ↔ _
  apply exists_congr
  intro c
  apply forall_congr'
  intro n
  rw [recorded_member_truth C A E R₁ R₂ P]
  simp only [Term.eval, Function.update_self, Function.update_of_ne distinct]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- This is an equivalence, not an assumed effective filtered-column contract. -/
theorem source_mechanical_padding_truth_iff (P : RawPredicates Nat)
    (H : Finset (Nat × Shape Nat)) (labels : Nat → Shape Nat → Label)
    (a j x e : Nat) (ms : List (Label × Nat)) (distinct : e ≠ x) (φ : Formula Nat) :
    (∀ s, filteredTruth (predicates C A E R₁ R₂ P)
      (markerPadding a ms
        ((parameterMechanicalSentence C.arithmetic j x e φ).record
          (mainHeads A E H labels))) s) ↔
      ∀ s, ∃ c, ∀ n, (filteredTruth (predicates C A E R₁ R₂ P)
        ((Formula.know j φ).record (mainHeads A E H labels))
        (Function.update (Function.update s e c) x n) ↔ W c n) := by
  have hm : (∀ s, filteredTruth (predicates C A E R₁ R₂ P)
      (markerPadding a ms
        ((parameterMechanicalSentence C.arithmetic j x e φ).record
          (mainHeads A E H labels))) s) ↔
      ∀ s, filteredTruth (predicates C A E R₁ R₂ P)
        ((parameterMechanicalSentence C.arithmetic j x e φ).record
          (mainHeads A E H labels)) s :=
    forall_congr' (fun s => markerPadding_truth_iff C A E R₁ R₂ P a ms _ s)
  rw [hm, parameterMechanicalSentence, Formula.record_universalClosure,
    truth_universalClosure_iff_all]
  exact forall_congr' (fun s =>
    recorded_mechanical_matrix_truth_iff C A E R₁ R₂ P H labels j x e distinct φ s)

end RecordedStage
end Alexander313
