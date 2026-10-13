import Alexander313.Arithmetic.LocalExecution

/-!
# Beta-coded execution sequences represent the actual domain predicate

A finite beta prefix is checked at every position, with child references
restricted to earlier positions. Strong induction reconstructs actual
bounded-evaluator traces. Conversely, every constructed predecessor-first
execution list has actual beta parameters and satisfies this checker.
-/

namespace Alexander313

namespace CertifiedTraceSequence

theorem local_get {Γ : List TraceRecord} (hΓ : CertifiedTraceSequence Γ)
    (i : Nat) (hi : i < Γ.length) :
    LocalTraceStep (fun r => ∃ j, ∃ hj : j < i, Γ[j]'(lt_trans hj hi) = r) Γ[i] := by
  induction hΓ generalizing i with
  | nil => simp at hi
  | @snoc Γ hΓ r hr ih =>
    by_cases hlt : i < Γ.length
    · rw [List.getElem_append_left hlt]
      apply (ih i hlt).mono
      rintro s ⟨j, hj, hget⟩
      exact ⟨j, hj, by simpa only [List.getElem_append_left (lt_trans hj hlt)] using hget⟩
    · have hieq : i = Γ.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
      apply hr.mono
      intro s hs
      obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hs
      exact ⟨j, hj, by simpa only [List.getElem_append_left hj] using hget⟩

end CertifiedTraceSequence

def BetaExecutionCorrect (a b length : Nat) : Prop :=
  ∀ i, i < length →
    LocalTraceStep (fun r => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = r.code)
      (TraceRecord.decode (a % ((i + 1) * b + 1)))

theorem BetaExecutionCorrect.trace {a b length : Nat}
    (h : BetaExecutionCorrect a b length) (i : Nat) (hi : i < length) :
    let r := TraceRecord.decode (a % ((i + 1) * b + 1))
    Nonempty (BoundedTrace r.fuel r.program r.input r.output) := by
  have all : ∀ i, i < length →
      let r := TraceRecord.decode (a % ((i + 1) * b + 1))
      Nonempty (BoundedTrace r.fuel r.program r.input r.output) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      apply (h i hi).trace
      rintro r ⟨j, hj, hcode⟩
      have hr : TraceRecord.decode (a % ((j + 1) * b + 1)) = r := by
        rw [hcode, TraceRecord.decode_code]
      simpa only [hr] using ih j hj (lt_trans hj hi)
  exact all i hi

theorem betaExecutionCorrect_from_sequence {Γ : List TraceRecord}
    (hΓ : CertifiedTraceSequence Γ) (a b : Nat)
    (hcode : ∀ i, ∀ hi : i < Γ.length, a % ((i + 1) * b + 1) = Γ[i].code) :
    BetaExecutionCorrect a b Γ.length := by
  intro i hi
  rw [hcode i hi, TraceRecord.decode_code]
  apply (hΓ.local_get i hi).mono
  rintro r ⟨j, hj, hget⟩
  refine ⟨j, hj, ?_⟩
  rw [hcode j (lt_trans hj hi), hget]

theorem finite_record_beta_parameters (Γ : List TraceRecord) :
    ∃ a b, ∀ i, ∀ hi : i < Γ.length, a % ((i + 1) * b + 1) = Γ[i].code := by
  let z := Nat.unbeta (Γ.map TraceRecord.code)
  refine ⟨z.unpair.1, z.unpair.2, ?_⟩
  intro i hi
  have h := Nat.beta_unbeta_coe (Γ.map TraceRecord.code)
    ⟨i, by simpa only [List.length_map] using hi⟩
  simpa only [z, Nat.beta, Fin.getElem_fin, List.getElem_map] using h

theorem W_iff_beta_execution (e n : Nat) :
    W e n ↔ ∃ a b length i fuel output,
      i < length ∧ a % ((i + 1) * b + 1) =
        (⟨fuel, Nat.Partrec.Code.ofNatCode e, n, output⟩ : TraceRecord).code ∧
      BetaExecutionCorrect a b length := by
  constructor
  · intro h
    obtain ⟨Γ, hΓ, fuel, output, hr⟩ := (W_iff_certified_sequence e n).mp h
    obtain ⟨a, b, hcode⟩ := finite_record_beta_parameters Γ
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hr
    refine ⟨a, b, Γ.length, i, fuel, output, hi, ?_,
      betaExecutionCorrect_from_sequence hΓ a b hcode⟩
    rw [hcode i hi, hget]
  · rintro ⟨a, b, length, i, fuel, output, hi, hcode, hcorrect⟩
    apply (W_iff_boundedTrace e n).mpr
    refine ⟨fuel, output, ?_⟩
    simpa only [hcode, TraceRecord.decode_code] using hcorrect.trace i hi

/-- Decode an arithmetic record graph followed by its actual local rule.
    This is the standard meaning of the existential record-field checker. -/
theorem exists_fields_iff_local (a b i row : Nat) :
    (∃ fuel program input output r,
      row = r ∧ r = Nat.pair fuel (Nat.pair program (Nat.pair input output)) ∧
      EncodedTraceStep a b i fuel program input output) ↔
    LocalTraceStep (fun s => ∃ j, j < i ∧ a % ((j + 1) * b + 1) = s.code)
      (TraceRecord.decode row) := by
  constructor
  · rintro ⟨fuel, program, input, output, r, rfl, rfl, hstep⟩
    simpa only [TraceRecord.decode, Nat.unpair_pair] using
      (encodedTraceStep_iff_local a b i fuel program input output).mp hstep
  · intro h
    let r := TraceRecord.decode row
    refine ⟨r.fuel, Encodable.encode r.program, r.input, r.output, row, rfl, ?_, ?_⟩
    · exact (TraceRecord.code_decode row).symm
    · exact localTraceStep_to_encoded a b i h

end Alexander313
