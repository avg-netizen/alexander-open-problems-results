import Alexander313.Carlson.ComputableRequests
import Alexander313.Carlson.ComputablePatternLifting
import Alexander313.Carlson.FairSequence

/-!
# Executable fair generating sequences

At step `k`, the natural-number schedule supplies an earlier source stage,
a finite rational target presentation, and a finite derivation certificate.
The certificate checker terminates on every request. Accepted certificates
are realized by the computable minimal lifting; rejected requests leave the
current presentation unchanged.

The stage data are defined by primitive recursion, independently of any
pattern proof. Soundness of the checker certifies every step. Completeness
of certificate recognition and the pairing schedule prove the original
fairness condition for every rational structure, including structures with
arbitrary off-carrier relation values.

These are executable Lean definitions. Their representation in the
project's `Program` language is a separate obligation.
-/

namespace Alexander313.Carlson.Finite.ComputableFairSequence

open ComputableRequests

/-- Carry out one scheduled request, or retain the current presentation
when its finite certificate is rejected. -/
def next (source current : RationalPresentation) (k : ℕ) : RationalPresentation :=
  if ComputableRequests.check source k = true then
    (RationalPresentation.lift source (target k) current id).1
  else current

theorem next_of_check (source current : RationalPresentation) (k : ℕ)
    (hc : ComputableRequests.check source k = true) :
    next source current k = (RationalPresentation.lift source (target k) current id).1 := by
  simp only [next, hc, if_true]

theorem next_of_reject (source current : RationalPresentation) (k : ℕ)
    (hc : ComputableRequests.check source k = false) :
    next source current k = current := by
  simp only [next, hc, Bool.false_eq_true, if_false]

/-- An accepted request is realized by a continuous minimal lifting. -/
theorem next_spec {source current : RationalPresentation} {k : ℕ}
    (hc : ComputableRequests.check source k = true)
    (hcurrent : current.toStr.IsPattern)
    (hE : Str.ContinuousEmbedding source.toStr current.toStr id) :
    PatternLifting source.toStr (target k).toStr current.toStr
      (next source current k).toStr id
      (RationalPresentation.lift source (target k) current id).2 ∧
    PatternLifting.IsMinimal source.toStr (target k).toStr current.toStr
      (next source current k).toStr id ∧
    Str.Continuous current.toStr (next source current k).toStr := by
  rw [next_of_check source current k hc]
  have d := ComputableRequests.check_sound hc
  exact RationalPresentation.lift_spec d.target_pattern hcurrent d.continuous hE

/-- The scheduled operation always gives a generating step from a pattern
whenever the earlier source is continuously included in the current stage. -/
theorem next_rule {source current : RationalPresentation} {k : ℕ}
    (hcurrent : current.toStr.IsPattern)
    (hE : Str.ContinuousEmbedding source.toStr current.toStr id) :
    Str.GeneratingRule current.toStr (next source current k).toStr := by
  by_cases hc : ComputableRequests.check source k = true
  · rw [next_of_check source current k hc]
    exact RationalPresentation.lift_generatingRule
      (ComputableRequests.check_sound hc) hcurrent hE
  · simp only [next, hc]
    exact Str.GeneratingRule.refl hcurrent

/-- After `k` steps, the first `k + 1` presentations are retained, and the
uncomputed tail is constant. This total finite approximation uses no proofs. -/
def approximation (P : RationalPresentation) : ℕ → ℕ → RationalPresentation
  | 0 => fun _ => P
  | k + 1 =>
      let S := approximation P k
      let Q := next (S (sourceIndex k)) (S k) k
      fun n => if n ≤ k then S n else Q

@[simp] theorem approximation_zero (P : RationalPresentation) (n : ℕ) :
    approximation P 0 n = P := rfl

theorem approximation_succ_agrees (P : RationalPresentation)
    (k : ℕ) {n : ℕ} (hn : n ≤ k) :
    approximation P (k + 1) n = approximation P k n := by
  simp only [approximation, if_pos hn]

theorem approximation_agrees (P : RationalPresentation)
    {k l n : ℕ} (hn : n ≤ k) (hkl : k ≤ l) :
    approximation P l n = approximation P k n := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
      exact (approximation_succ_agrees P l (hn.trans hkl)).trans ih

theorem approximation_step (P : RationalPresentation) (hP : P.toStr.IsPattern)
    (k n : ℕ) :
    Str.GeneratingRule (approximation P k n).toStr
      (approximation P k (n + 1)).toStr := by
  induction k generalizing n with
  | zero => exact Str.GeneratingRule.refl hP
  | succ k ih =>
      let S : GeneratingSequence ℚ :=
        { stage := fun n => (approximation P k n).toStr
          step := ih }
      have hE := (S.continuous (sourceIndex_le k)).inclusionEmbedding
      have hr := next_rule (k := k) (S.pattern k) hE
      have hs := (S.extendAt k
        (next (approximation P k (sourceIndex k)) (approximation P k k) k).toStr hr).step n
      simpa only [GeneratingSequence.extendAt, S, approximation,
        apply_ite RationalPresentation.toStr] using hs

/-- Compute the finite rational presentation at an arbitrary stage. -/
def stage (P : RationalPresentation) (n : ℕ) : RationalPresentation :=
  approximation P n n

@[simp] theorem stage_zero (P : RationalPresentation) : stage P 0 = P := rfl

theorem stage_agrees (P : RationalPresentation) {n k : ℕ} (hn : n ≤ k) :
    stage P n = approximation P k n :=
  (approximation_agrees P le_rfl hn).symm

/-- The recursive data obey the expected one-step update, using only an
already computed source stage. -/
theorem stage_succ (P : RationalPresentation) (k : ℕ) :
    stage P (k + 1) = next (stage P (sourceIndex k)) (stage P k) k := by
  rw [stage_agrees P (sourceIndex_le k)]
  simp only [stage, approximation, Nat.not_succ_le_self, if_false]

theorem stage_step (P : RationalPresentation) (hP : P.toStr.IsPattern) (n : ℕ) :
    Str.GeneratingRule (stage P n).toStr (stage P (n + 1)).toStr := by
  have hs := approximation_step P hP (n + 1) n
  rw [approximation_succ_agrees P n le_rfl] at hs
  exact hs

/-- Certify the computed presentations as a generating sequence. The
initial pattern proof is used only for the proof of its step condition. -/
def toGeneratingSequence (P : RationalPresentation) (hP : P.toStr.IsPattern) :
    GeneratingSequence ℚ where
  stage n := (stage P n).toStr
  step := stage_step P hP

@[simp] theorem toGeneratingSequence_stage (P : RationalPresentation)
    (hP : P.toStr.IsPattern) (n : ℕ) :
    (toGeneratingSequence P hP).stage n = (stage P n).toStr := rfl

@[simp] theorem toGeneratingSequence_zero (P : RationalPresentation)
    (hP : P.toStr.IsPattern) : (toGeneratingSequence P hP).stage 0 = P.toStr := rfl

/-- At every accepted schedule index, the next computed stage realizes
that request by a continuous minimal lifting. -/
theorem stage_lifting (P : RationalPresentation) (hP : P.toStr.IsPattern) (k : ℕ)
    (hc : ComputableRequests.check (stage P (sourceIndex k)) k = true) :
    PatternLifting (stage P (sourceIndex k)).toStr (target k).toStr
      (stage P k).toStr (stage P (k + 1)).toStr id
      (RationalPresentation.lift (stage P (sourceIndex k)) (target k) (stage P k) id).2 ∧
    PatternLifting.IsMinimal (stage P (sourceIndex k)).toStr (target k).toStr
      (stage P k).toStr (stage P (k + 1)).toStr id ∧
    Str.Continuous (stage P k).toStr (stage P (k + 1)).toStr := by
  rw [stage_succ]
  let S := toGeneratingSequence P hP
  exact next_spec hc (S.pattern k)
    ((S.continuous (sourceIndex_le k)).inclusionEmbedding)

/-- Every generating request is eventually realized. Certificates are
dovetailed with their source stages and targets, so a rejected request
cannot block or exhaust the search for a later valid certificate. -/
theorem fair (P : RationalPresentation) (hP : P.toStr.IsPattern) :
    (toGeneratingSequence P hP).Fair := by
  intro n Q hQ
  obtain ⟨k, hsource, hnk, hc, e⟩ := ComputableRequests.complete (stage P n) n Q hQ
  have hcheck : ComputableRequests.check (stage P (sourceIndex k)) k = true := by
    simpa only [hsource] using hc
  have L := (stage_lifting P hP k hcheck).1
  rw [hsource] at L
  exact ⟨k, hnk, _, L.of_source_identity_iso e⟩

/-- Every supplied finite rational pattern has an explicitly computed fair
sequence with exactly that initial presentation. -/
theorem specification (P : RationalPresentation) (hP : P.toStr.IsPattern) :
    (toGeneratingSequence P hP).stage 0 = P.toStr ∧
      (toGeneratingSequence P hP).Fair :=
  ⟨rfl, fair P hP⟩

end Alexander313.Carlson.Finite.ComputableFairSequence
