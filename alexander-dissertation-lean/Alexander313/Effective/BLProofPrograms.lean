import Alexander313.Effective.BLAdmission
import Alexander313.Alexander.NativeProofChecker

/-!
# An actual positive program for source BL derivations

Every witness contains a finite list of actual BL candidates and a numerical
native Hilbert proof. The exact domain is derivability from the closed native
BL theory of the sorted universal Δ sentence. Accepted source formulas are
valid. The converse semantic completeness theorem is not assumed here and
has not yet been proved; this is consequently not an exact `Valid` program.
-/

noncomputable section

namespace Alexander313.Delta.BLProofProgram

abbrev NativeFormula := Delta.NativeFormula.Syntax 0

def target (φ : Formula Nat) : NativeFormula :=
  FirstOrderCalculus.sentenceFormula (FirstOrderClosure.universalSentence (formula φ))

theorem target_primrec : Primrec target :=
  NativeClosedLabels.sentenceFormula_primrec.comp
    (FirstOrderClosure.universalSentence_primrec.comp formula_primrec)

def Derivable (φ : Formula Nat) : Prop :=
  FirstOrderCalculus.Derivation (BLTheory Nat) (target φ)

private theorem derivation_mono {T U : (language Nat).Theory}
    {φ : NativeFormula} (h : FirstOrderCalculus.Derivation T φ) (ht : T ⊆ U) :
    FirstOrderCalculus.Derivation U φ := by
  induction h with
  | logical h => exact .logical h
  | theory σ hσ => exact .theory σ (ht hσ)
  | mp hp hq ihp ihq => exact .mp ihp ihq
  | generalize x h ih => exact .generalize x ih

theorem finite_candidates {φ : NativeFormula}
    (h : FirstOrderCalculus.Derivation (BLTheory Nat) φ) :
    ∃ cs : List (BLCandidate Nat), FirstOrderCalculus.Derivation
      {σ | σ ∈ candidateSentences cs} φ := by
  induction h with
  | logical h => exact ⟨[], .logical h⟩
  | theory σ hσ =>
    obtain ⟨c, hc⟩ := candidateSentence?_complete σ hσ
    refine ⟨[c], .theory σ ?_⟩
    simp [candidateSentences, hc]
  | mp hp hq ihp ihq =>
    obtain ⟨cs, hcs⟩ := ihp
    obtain ⟨ds, hds⟩ := ihq
    refine ⟨cs ++ ds, .mp (derivation_mono hcs ?_) (derivation_mono hds ?_)⟩
    · intro σ hσ
      simp only [candidateSentences, List.filterMap_append, List.mem_append]
      exact Or.inl hσ
    · intro σ hσ
      simp only [candidateSentences, List.filterMap_append, List.mem_append]
      exact Or.inr hσ
  | generalize x h ih =>
    obtain ⟨cs, hcs⟩ := ih
    exact ⟨cs, .generalize x hcs⟩

theorem finite_candidates_iff (φ : NativeFormula) :
    (∃ cs : List (BLCandidate Nat), FirstOrderCalculus.Derivation
      {σ | σ ∈ candidateSentences cs} φ) ↔
      FirstOrderCalculus.Derivation (BLTheory Nat) φ :=
  ⟨fun ⟨cs, h⟩ => derivation_mono h (candidateSentences_subset cs), finite_candidates⟩

theorem Derivable.valid {φ : Formula Nat} (h : Derivable φ) : Valid φ := by
  intro D hD M s
  letI : Nonempty D := hD
  letI : (language Nat).Structure D := structureOfModal M
  letI : FirstOrder.Language.Theory.Model D (BLTheory Nat) :=
    (model_BLTheory_iff (structureOfModal M)).mpr (structureOfModal_satisfiesBL M)
  have hsentence := (FirstOrderCalculus.sentenceFormula_realize
    (FirstOrderClosure.universalSentence (formula φ)) s).mp
      (FirstOrderCalculus.Derivation.sound h s)
  have hformula := (FirstOrderClosure.universalSentence_realize (formula φ)).mp hsentence s
  exact (formula_realize M φ s).mp hformula

abbrev Certificate := List (BLCandidate Nat) × Nat

def certificate (φ : Formula Nat) (w : Certificate) : Bool :=
  NativeProofChecker.acceptsFinite (candidateSentences w.1) (Delta.NativeFormula.code (target φ)) w.2

theorem certificate_primrec : Primrec₂ certificate := by
  have hcs : Primrec (fun p : Formula Nat × Certificate => candidateSentences p.2.1) :=
    candidateSentences_primrec.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun p : Formula Nat × Certificate => Delta.NativeFormula.code (target p.1)) :=
    (Delta.NativeFormula.code_primrec 0).comp (target_primrec.comp Primrec.fst)
  have hp : Primrec (fun p : Formula Nat × Certificate => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (NativeProofChecker.acceptsFinite_joint_primrec.comp ((hcs.pair ht).pair hp)).to₂

theorem certificate_iff (φ : Formula Nat) (w : Certificate) :
    certificate φ w = true ↔
      NativeProofChecker.checkFinite (candidateSentences w.1) w.2 = some (target φ) :=
  NativeProofChecker.acceptsFinite_code_iff (candidateSentences w.1) (target φ) w.2

theorem exists_certificate_iff (φ : Formula Nat) :
    (∃ w : Certificate, certificate φ w = true) ↔ Derivable φ := by
  change (∃ w : List (BLCandidate Nat) × Nat,
    NativeProofChecker.acceptsFinite (candidateSentences w.1)
      (Delta.NativeFormula.code (target φ)) w.2 = true) ↔ _
  simp only [Prod.exists, NativeProofChecker.exists_acceptsFinite_iff_derivation]
  exact finite_candidates_iff (target φ)

theorem certificate_valid (φ : Formula Nat) (w : Certificate)
    (h : certificate φ w = true) : Valid φ :=
  ((exists_certificate_iff φ).mp ⟨w, h⟩).valid

abbrev Witness := Formula Nat × Certificate

def decodeWitness (n : Nat) : Witness :=
  (Encodable.decode (α := Witness) n).getD (.falsum, [], 0)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ((.falsum, [], 0) : Witness))

@[simp] theorem decodeWitness_encode (w : Witness) :
    decodeWitness (Encodable.encode w) = w := by simp [decodeWitness]

def check (query witness : Nat) : Bool :=
  let w := decodeWitness witness
  (query == w.1.code id) && certificate w.1 w.2

theorem check_primrec : Primrec₂ check := by
  have hw : Primrec (fun p : Nat × Nat => decodeWitness p.2) :=
    decodeWitness_primrec.comp Primrec.snd
  have hφ := Primrec.fst.comp hw
  have hc := Primrec.snd.comp hw
  exact (Primrec.and.comp
    (Primrec.beq.comp Primrec.fst (Formula.code_primrec.comp hφ))
    (certificate_primrec.comp hφ hc)).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (check query witness))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind check_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) :
    (evaluation query).Dom ↔ ∃ witness, check query witness = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (φ : Formula Nat) :
    (evaluation (φ.code id)).Dom ↔ Derivable φ := by
  rw [evaluation_domain, ← exists_certificate_iff]
  constructor
  · rintro ⟨witness, h⟩
    let w := decodeWitness witness
    have hc : φ.code id = w.1.code id ∧ certificate w.1 w.2 = true := by
      simpa only [check, Bool.and_eq_true, beq_iff_eq] using h
    have he : φ = w.1 := Formula.code_injective id Function.injective_id hc.1
    exact ⟨w.2, he.symm ▸ hc.2⟩
  · rintro ⟨w, hw⟩
    exact ⟨Encodable.encode (φ, w), by
      simp only [check, decodeWitness_encode, beq_self_eq_true, hw, Bool.true_and]⟩

theorem evaluation_only_formulas (query : Nat) (h : (evaluation query).Dom) :
    ∃ φ : Formula Nat, query = φ.code id ∧ Derivable φ := by
  obtain ⟨witness, hw⟩ := (evaluation_domain query).mp h
  let w := decodeWitness witness
  have hc : query = w.1.code id ∧ certificate w.1 w.2 = true := by
    simpa only [check, Bool.and_eq_true, beq_iff_eq] using hw
  exact ⟨w.1, hc.1, (exists_certificate_iff w.1).mp ⟨w.2, hc.2⟩⟩

theorem program_exists : ∃ p : Program,
    (∀ φ : Formula Nat, p.domain (φ.code id) ↔ Derivable φ) ∧
    (∀ query, p.domain query → ∃ φ : Formula Nat,
      query = φ.code id ∧ Derivable φ) := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, ?_, ?_⟩
  · intro φ
    simpa only [Program.domain, hp] using evaluation_correct φ
  · intro query h
    exact evaluation_only_formulas query (by simpa only [Program.domain, hp] using h)

/-- A genuine sound executing program. Semantic completeness of the native
Hilbert calculus is the remaining converse, not a premise of its construction. -/
theorem sound_program_exists : ∃ p : Program,
    (∀ φ : Formula Nat, p.domain (φ.code id) ↔ Derivable φ) ∧
    (∀ query, p.domain query → ∃ φ : Formula Nat, query = φ.code id ∧ Valid φ) := by
  obtain ⟨p, hp, hsyntax⟩ := program_exists
  refine ⟨p, hp, ?_⟩
  intro query h
  obtain ⟨φ, he, hφ⟩ := hsyntax query h
  exact ⟨φ, he, hφ.valid⟩

end Alexander313.Delta.BLProofProgram
