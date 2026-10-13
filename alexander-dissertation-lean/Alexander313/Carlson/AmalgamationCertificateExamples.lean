import Alexander313.Carlson.ComputablePointedComparison
import Alexander313.Carlson.PartialPointedComparison
import Alexander313.Carlson.RationalExactnessExamples

/-!
# Controls for certificate search and its comparison answers

The covered union control passes every finite frame check and fails only
exactness. Accepted code encodings are handled symbolically, avoiding
evaluation of enormous nested certificate numbers by the kernel.
-/

namespace Alexander313.Carlson.Finite.AmalgamationCertificateExamples

open RationalExactnessExamples AmalgamationCertificate

set_option maxRecDepth 8192

theorem first_duplicate_key_wins :
    RationalMap.eval [(1, 3), (1, 7)] 1 = 3 := by decide

theorem missing_key_defaults_to_zero :
    RationalMap.eval [(1, 3)] 2 = 0 := by decide

def noInputs : Fin 0 → RationalPresentation := Fin.elim0

theorem empty_family_certificate_accepts :
    check noInputs (ComputableAmalgamation.emptyCertificate 0) = true := by decide

theorem empty_family_nonempty_target_rejects :
    check noInputs ((crossing, (fun _ => []), (fun _ => 0)) : AmalgamationCertificate 0) = false := by decide

def singletonAt (a : ℚ) : RationalPresentation := ⟨{a}, {(a, a)}, {(a, a)}⟩

def singletonInputs (i : Fin 2) := singletonAt (i.val : ℚ)

def coalesced : AmalgamationCertificate 2 :=
  (singleton, fun i => [(i.val, 0)], fun _ => RationalCertificateExamples.generationCode)

private theorem coalesced_image (i : Fin 2) :
    coalesced.image singletonInputs i = singleton := by
  refine Fin.cases (by decide) (fun i => ?_) i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  decide

private theorem singleton_exactness_accepts :
    RationalPresentation.checkExact singleton singleton
      RationalCertificateExamples.generationCode = true := by
  apply (RationalPresentation.checkExact_eq_true _ _ _).mpr
  refine ⟨(RationalPresentation.checkPattern_eq_true _).mp (by decide), ?_,
    (RationalPresentation.checkInitialSpanCorrect_eq_true _ _).mp (by decide)⟩
  have hs : RationalExactnessExamples.singleton.initialSpan RationalExactnessExamples.singleton.U =
      RationalExactnessExamples.singleton := by decide
  rw [hs]
  exact RationalCertificateExamples.generation_accepts

/-- Different rational singleton carriers coalesce in the accepted target. -/
theorem coalesced_certificate_accepts : coalesced.check singletonInputs = true := by
  apply (check_eq_true _ _).mpr
  refine ⟨(RationalPresentation.checkPattern_eq_true _).mp (by decide),
    (checkEmbeddings_eq_true _ _).mp (by decide), by decide, ?_⟩
  intro i
  rw [coalesced_image]
  exact singleton_exactness_accepts

theorem coalesced_encoded_certificate_accepts :
    checkCode singletonInputs (Encodable.encode coalesced) = true :=
  (checkCode_encode _ _).trans coalesced_certificate_accepts

/-- Termination has a concrete, accepted witness bound on this input. -/
theorem coalesced_search_has_witness_bound :
    ComputableAmalgamation.leastCode singletonInputs (by intro i; exact (show ∀ i, (singletonInputs i).toStr.IsPattern from by decide) i) ≤
      Encodable.encode coalesced :=
  ComputableAmalgamation.leastCode_le _ coalesced_encoded_certificate_accepts

def crossingInputs (i : Fin 2) : RationalPresentation :=
  Fin.cases singleton (fun _ => crossing) i

def crossingUnion (codes : Fin 2 → ℕ) : AmalgamationCertificate 2 :=
  (crossing, fun _ => [(0, 0), (1, 1)], codes)

/-- An ordinary covered union satisfies the entire pattern/embedding/union
frame while a first-relation edge crosses one input's initial span. -/
theorem covered_union_frame_passes (codes : Fin 2 → ℕ) :
    (crossingUnion codes).1.checkPattern = true ∧
    (crossingUnion codes).checkEmbeddings crossingInputs = true ∧
    (crossingUnion codes).1.U = Finset.univ.biUnion
      (fun i => (crossingInputs i).U.image ((crossingUnion codes).maps i)) := by
  change (crossingUnion (fun _ => 0)).1.checkPattern = true ∧
    (crossingUnion (fun _ => 0)).checkEmbeddings crossingInputs = true ∧
    (crossingUnion (fun _ => 0)).1.U = Finset.univ.biUnion
      (fun i => (crossingInputs i).U.image ((crossingUnion (fun _ => 0)).maps i))
  decide

theorem covered_union_exactness_rejects (codes : Fin 2 → ℕ) :
    (crossingUnion codes).check crossingInputs = false := by
  cases hb : (crossingUnion codes).check crossingInputs with
  | false => rfl
  | true =>
    have hx := ((check_eq_true _ _).mp hb).2.2.2 0
    have hU : ((crossingUnion codes).image crossingInputs 0).U = singleton.U := by
      change ((crossingUnion (fun _ => 0)).image crossingInputs 0).U =
        RationalExactnessExamples.singleton.U
      decide
    change RationalPresentation.checkExact ((crossingUnion codes).image crossingInputs 0)
      crossing (codes 0) = true at hx
    simp only [RationalPresentation.checkExact, hU, crossing_correctness_rejects,
      Bool.and_false] at hx
    cases hx

theorem malformed_candidate_code_rejects {n : ℕ} (P : Fin n → RationalPresentation)
    (code : ℕ) (hd : Encodable.decode (α := AmalgamationCertificate n) code = none) :
    checkCode P code = false := by simp only [checkCode, hd]

theorem malformed_two_input_zero_rejects (P : Fin 2 → RationalPresentation) :
    checkCode P 0 = false :=
  malformed_candidate_code_rejects P 0 (by decide +kernel)

/-- The finite answer reader coalesces different input carriers, using
the actual pinned candidate decoder rather than a hand-supplied target. -/
theorem coalesced_five_answers :
    PartialPointedComparison.read ((singletonAt 0, 0), (singletonAt 1, 1))
      (Encodable.encode coalesced) = (true, true, false, true, true) := by
  unfold PartialPointedComparison.read
  rw [Encodable.encodek]
  decide

end Alexander313.Carlson.Finite.AmalgamationCertificateExamples

namespace Alexander313.Carlson.PointedPattern

/-- Reflexive comparison uses the real terminating search, including its
two positive reflection answers and negative strict-order answer. -/
theorem compare_self (p : PointedPattern) :
    (compare p p).eq = true ∧ (compare p p).le = true ∧
    (compare p p).lt = false ∧ (compare p p).one = true ∧ (compare p p).two = true := by
  obtain ⟨he, hl, ht, h₁, h₂⟩ := compare_correct p p
  refine ⟨he.mpr rfl, hl.mpr le_rfl, ?_, h₁.mpr (R1_refl _), h₂.mpr (R2_refl _)⟩
  cases hb : (compare p p).lt with
  | false => rfl
  | true => exact (lt_irrefl _ (ht.mp hb)).elim

/-- A strict pair gives all three negative answers in the reverse direction. -/
theorem compare_reverse_of_lt (p q : PointedPattern) (h : p.iota < q.iota) :
    (compare p q).eq = false ∧ (compare p q).le = true ∧ (compare p q).lt = true ∧
    (compare q p).le = false ∧ (compare q p).one = false ∧ (compare q p).two = false := by
  obtain ⟨he, hl, ht, _, _⟩ := compare_correct p q
  obtain ⟨_, hr, _, h₁, h₂⟩ := compare_correct q p
  have hf : ∀ b : Bool, (b = true → False) → b = false := by
    intro b hn
    cases b with
    | false => rfl
    | true => exact (hn rfl).elim
  exact ⟨hf _ (fun hb => h.ne (he.mp hb)), hl.mpr h.le, ht.mpr h,
    hf _ (fun hb => (not_le_of_gt h) (hr.mp hb)),
    hf _ (fun hb => (not_le_of_gt h) (R1_le (h₁.mp hb))),
    hf _ (fun hb => (not_le_of_gt h) (R2_le (h₂.mp hb)))⟩

/-- One actual machine produces the full reflexive tuple for every pointed
input, independently of how the finite seed is placed among the rationals. -/
theorem self_comparison_machine : ∃ machine : Nat.Partrec.Code, ∀ p : PointedPattern,
    machine.eval (Encodable.encode ((p.seed.val, p.point), (p.seed.val, p.point))) =
      Part.some (Encodable.encode (true, true, false, true, true)) := by
  obtain ⟨machine, hm⟩ := PartialPointedComparison.comparison_program
  refine ⟨machine, fun p => ?_⟩
  obtain ⟨he, hl, ht, h₁, h₂⟩ := compare_self p
  simpa only [PartialPointedComparison.input, PartialPointedComparison.answers,
    he, hl, ht, h₁, h₂] using hm p p

end Alexander313.Carlson.PointedPattern
