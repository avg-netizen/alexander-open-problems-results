import Alexander313.Effective.BLCandidateFormation
import Alexander313.Alexander.EffectiveClosure
import Alexander313.Computability

/-!
# Effective finite BL admission and its actual positive premise program

Candidate formation uses the original sorted native universal sentence.
The real program below recognizes exactly the closed native BL theory. Its
search ranges over ordinary finite candidate data, with no semantic validity
decision and no Hilbert completeness premise.
-/

noncomputable section

namespace Alexander313.Delta

theorem candidateSentence?_eq (c : BLCandidate Nat) :
    candidateSentence? c = cond c.accepted
      (some (FirstOrderClosure.universalSentence c.matrix)) none := by
  cases c <;> simp [candidateSentence?, BLCandidate.accepted, BLCandidate.matrix,
    Formula.AlphaEquivalent]

theorem candidateSentence?_primrec : Primrec (candidateSentence? (Owner := Nat)) :=
  (BLCandidate.accepted_primrec.cond
    (Primrec.option_some.comp
      (FirstOrderClosure.universalSentence_primrec.comp BLCandidate.matrix_primrec))
    (Primrec.const none)).of_eq (fun c => (candidateSentence?_eq c).symm)

theorem candidateSentences_primrec : Primrec (candidateSentences (Owner := Nat)) :=
  Primrec.listFilterMap Primrec.id (candidateSentence?_primrec.comp Primrec.snd).to₂

theorem candidateAdmission_primrec : Primrec₂ (candidateAdmission (Owner := Nat)) := by
  classical
  have he : PrimrecRel (fun σ τ : (language Nat).Sentence => σ = τ) := Primrec.eq
  have hm := he.exists_mem_list.comp
    (candidateSentences_primrec.comp Primrec.fst) Primrec.snd
  exact hm.decide.of_eq (fun p => by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, candidateAdmission_eq_true, exists_eq_right])

namespace BLPremiseProgram

def decodeCandidate (n : Nat) : BLCandidate Nat :=
  (Encodable.decode (α := BLCandidate Nat) n).getD (.alphabetic 0 .falsum .falsum)

theorem decodeCandidate_primrec : Primrec decodeCandidate :=
  Primrec.option_getD.comp Primrec.decode
    (Primrec.const (.alphabetic 0 .falsum .falsum : BLCandidate Nat))

@[simp] theorem decodeCandidate_encode (c : BLCandidate Nat) :
    decodeCandidate (Encodable.encode c) = c := by simp [decodeCandidate]

def check (query certificate : Nat) : Bool :=
  ((candidateSentence? (decodeCandidate certificate)).map
    (fun σ => Encodable.encode σ == query)).getD false

theorem check_primrec : Primrec₂ check := by
  have hc : Primrec (fun p : Nat × Nat => candidateSentence? (decodeCandidate p.2)) :=
    candidateSentence?_primrec.comp (decodeCandidate_primrec.comp Primrec.snd)
  have ht : Primrec (fun p : (Nat × Nat) × (language Nat).Sentence =>
      Encodable.encode p.2 == p.1.1) :=
    Primrec.beq.comp (Primrec.encode.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  exact (Primrec.option_getD.comp (hc.option_map ht.to₂) (Primrec.const false)).to₂

def evaluation (query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check query certificate))

theorem evaluation_partrec : Partrec evaluation :=
  Partrec.rfind check_primrec.to_comp.partrec.to₂

theorem evaluation_domain (query : Nat) :
    (evaluation query).Dom ↔ ∃ certificate, check query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (σ : (language Nat).Sentence) :
    (evaluation (Encodable.encode σ)).Dom ↔ σ ∈ BLTheory Nat := by
  rw [evaluation_domain]
  constructor
  · rintro ⟨certificate, h⟩
    cases hc : candidateSentence? (decodeCandidate certificate) with
    | none => simp [check, hc] at h
    | some τ =>
      have he : Encodable.encode τ = Encodable.encode σ := by
        simpa [check, hc] using h
      have ht : τ = σ := Encodable.encode_injective he
      exact ht ▸ candidateSentence?_sound (decodeCandidate certificate) τ hc
  · intro h
    obtain ⟨c, hc⟩ := candidateSentence?_complete σ h
    exact ⟨Encodable.encode c, by simp [check, hc]⟩

theorem evaluation_only_sentences (query : Nat) (h : (evaluation query).Dom) :
    ∃ σ : (language Nat).Sentence, query = Encodable.encode σ ∧ σ ∈ BLTheory Nat := by
  obtain ⟨certificate, hc⟩ := (evaluation_domain query).mp h
  cases hs : candidateSentence? (decodeCandidate certificate) with
  | none => simp [check, hs] at hc
  | some σ =>
    have he : Encodable.encode σ = query := by simpa [check, hs] using hc
    exact ⟨σ, he.symm,
      candidateSentence?_sound (decodeCandidate certificate) σ hs⟩

theorem program_exists : ∃ p : Program,
    (∀ σ : (language Nat).Sentence, p.domain (Encodable.encode σ) ↔ σ ∈ BLTheory Nat) ∧
    (∀ query, p.domain query → ∃ σ : (language Nat).Sentence,
      query = Encodable.encode σ ∧ σ ∈ BLTheory Nat) := by
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp evaluation_partrec)
  refine ⟨p, ?_, ?_⟩
  · intro σ
    simpa only [Program.domain, hp] using evaluation_correct σ
  · intro query h
    exact evaluation_only_sentences query (by simpa only [Program.domain, hp] using h)

end BLPremiseProgram
end Alexander313.Delta
