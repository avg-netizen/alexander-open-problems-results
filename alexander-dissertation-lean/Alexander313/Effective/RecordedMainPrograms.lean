import Alexander313.Effective.RecordedFiniteMasks
import Alexander313.Effective.RecordedRecording
import Alexander313.Effective.RecordedMarkerFormation
import Alexander313.Effective.RecordedMainSourcePrograms
import Alexander313.Effective.RecordedGuardPrograms

/-!
# Actual positive guarded-main compiler

One finite hereditary mask and one finite owner/source-shape label table
record the whole source sentence and its distinguished atom. Every original
source column numeral remains fixed. Fresh distinct marker tags, whole output
admission, actual source rows and every finite guard requirement are checked.
The uniform compiler uses only ordinary executing Program data. Exact semantic
source identification is separate; no guard/seed effectivity contract is assumed.

Effective labels use ordinary Nat order. This does not supply the actual
Wilken ordinal-domain, comparison or relation procedures.
-/

noncomputable section

namespace Alexander313.RecordedMainProgram

open RecordedFormula

abbrev Parameters := (List Nat × List Nat) × ((Program × Program) × (Program × Program))
abbrev Witness := (Nat × RecordedMainSourceProgram.Witness) ×
  ((RecordedTable.Mask × RecordedTable.Labels) × List (Nat × Nat))
abbrev Certificate := Witness × (Nat × RecordedGuardProgram.Witness)

def recordData (p : Parameters) (w : Witness) : FiniteRecordData := (p.1, w.2.1)
def sourceFormula (p : Parameters) (w : Witness) : Formula Nat :=
  RecordedMainSourceProgram.formula p.2.1.1 w.1.1 w.1.2
def sourceAtom (w : Witness) : Formula Nat := RecordedMainSourceProgram.atom w.1.1 w.1.2
def body (p : Parameters) (w : Witness) : Syntax := finiteRecord (recordData p w) (sourceFormula p w)
def guardedAtom (p : Parameters) (w : Witness) : Syntax := finiteRecord (recordData p w) (sourceAtom w)
def formula (p : Parameters) (a : Nat) (w : Witness) : Syntax := markerPadding a w.2.2 (body p w)
def guardData (p : Parameters) (w : Witness) : RecordedGuardProgram.Parameters :=
  ((p.1.2, w.2.2.map Prod.fst), p.2.2)
def requirements (p : Parameters) (w : Witness) : GuardRequirements Nat :=
  mainRequirementsCode p.1.2 ((guardedAtom p w).code RecordedHead.code)

theorem recordData_primrec : Primrec₂ recordData :=
  ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).to₂

theorem sourceFormula_primrec : Primrec₂ sourceFormula :=
  (RecordedMainSourceProgram.formula_primrec.comp
    (((Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).to₂

theorem sourceAtom_primrec : Primrec sourceAtom :=
  RecordedMainSourceProgram.atom_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)

theorem body_primrec : Primrec₂ body :=
  (finiteRecord_primrec.comp recordData_primrec sourceFormula_primrec).to₂

theorem guardedAtom_primrec : Primrec₂ guardedAtom :=
  (finiteRecord_primrec.comp recordData_primrec (sourceAtom_primrec.comp Primrec.snd)).to₂

theorem formula_primrec : Primrec (fun p : (Parameters × Nat) × Witness =>
    formula p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × Witness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Parameters × Nat) × Witness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × Witness => p.2) := Primrec.snd
  exact RecordedFormula.markerPadding_primrec.comp
    ((ha.pair (Primrec.snd.comp (Primrec.snd.comp hw))).pair (body_primrec.comp hp hw))

theorem guardData_primrec : Primrec₂ guardData := by
  have hE : Primrec (fun p : Parameters × Witness => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hms : Primrec (fun p : Parameters × Witness => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpoints := Primrec.list_map hms ((Primrec.fst.comp Primrec.snd).to₂)
  exact ((hE.pair hpoints).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂

theorem requirements_primrec : Primrec₂ requirements :=
  (mainRequirementsCode_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (code_primrec.comp guardedAtom_primrec)).to₂

def disjointCheck (AE : List Nat × List Nat) : Bool :=
  RecordedGuardProgram.allCheck (fun a => !(listMember AE.2 a)) AE.1

theorem disjointCheck_primrec : Primrec disjointCheck := by
  have ht : Primrec₂ (fun (E : List Nat) (a : Nat) => !(listMember E a)) :=
    Primrec.not.comp₂ listMember_primrec
  exact (RecordedGuardProgram.allCheck_primrec _ ht).comp Primrec.snd Primrec.fst

theorem disjointCheck_exact (AE : List Nat × List Nat) :
    disjointCheck AE = true ↔ Disjoint AE.1.toFinset AE.2.toFinset := by
  simp [disjointCheck, RecordedGuardProgram.allCheck_iff, listMember,
    Finset.disjoint_left]

def structural (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  HereditaryQueries (RecordedTable.mask w.2.1.1) ∧ Disjoint p.1.1.toFinset p.1.2.toFinset ∧
    (w.2.2.map Prod.snd).Nodup ∧
    (∀ q ∈ w.2.2, (markerTag Nat q.2).shape ∉ (sourceFormula p w).shape.subshapes) ∧
    (formula p a w).RecordedAdmissible p.1.1.toFinset p.1.2.toFinset

def side (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  RecordedMainSourceProgram.sideCondition p.2.1.2 p.1.1 p.1.2 w.1.1 a w.1.2 ∧
    structural p a w ∧
    (guardedAtom p w).MainGuarded (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
      (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.2.toFinset (markerPoints w.2.2)

def admits (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w : Witness, side p a w ∧ σ = formula p a w

theorem admits_closed {p : Parameters} {a : Nat} {σ : Syntax} (h : admits p a σ) : σ.Closed := by
  obtain ⟨w, hs, rfl⟩ := h
  have hc : (sourceFormula p w).Closed := RecordedMainSourceProgram.admits_closed
    ⟨w.1.1, w.1.2, hs.1, rfl, rfl⟩
  exact markerPadding_closed a w.2.2 _
    ((Formula.closed_record _ _).mpr hc)

theorem admits_admissible {p : Parameters} {a : Nat} {σ : Syntax} (h : admits p a σ) :
    σ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset := by
  obtain ⟨w, hs, rfl⟩ := h
  exact hs.2.1.2.2.2.2

def structuralCheck (p : Parameters) (a : Nat) (w : Witness) : Bool :=
  RecordedTable.hereditaryCheck w.2.1.1 &&
    (disjointCheck p.1 &&
      (RecordedMarkerProgram.markerDistinctCheck w.2.2 &&
        (RecordedMarkerProgram.markerFreshCheck (sourceFormula p w) w.2.2 &&
          admissibleCode p.1 ((formula p a w).code RecordedHead.code))))

theorem structuralCheck_primrec : Primrec (fun p : (Parameters × Nat) × Witness =>
    structuralCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × Witness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Parameters × Nat) × Witness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × Witness => p.2) := Primrec.snd
  have hM := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hw))
  have hms := Primrec.snd.comp (Primrec.snd.comp hw)
  exact Primrec.and.comp (RecordedTable.hereditaryCheck_primrec.comp hM)
    (Primrec.and.comp (disjointCheck_primrec.comp (Primrec.fst.comp hp))
      (Primrec.and.comp (RecordedMarkerProgram.markerDistinctCheck_primrec.comp hms)
        (Primrec.and.comp (RecordedMarkerProgram.markerFreshCheck_primrec.comp (sourceFormula_primrec.comp hp hw) hms)
          (admissibleCode_primrec.comp (Primrec.fst.comp hp)
            (code_primrec.comp (formula_primrec.comp ((hp.pair ha).pair hw)))))))

theorem structuralCheck_exact (p : Parameters) (a : Nat) (w : Witness) :
    structuralCheck p a w = true ↔ structural p a w := by
  simp only [structuralCheck, Bool.and_eq_true, RecordedTable.hereditaryCheck_exact,
    disjointCheck_exact, RecordedMarkerProgram.markerDistinctCheck_iff,
    RecordedMarkerProgram.markerFreshCheck_iff, admissibleCode_code, structural]

def condition (p : Parameters) (a : Nat) (w : Witness) (cutoff : Nat)
    (guardWitness : RecordedGuardProgram.Witness) : Bool :=
  RecordedMainSourceProgram.condition p.2.1.2 p.1.1 p.1.2 w.1.1 a w.1.2 cutoff &&
    (structuralCheck p a w && RecordedGuardProgram.condition (guardData p w) (requirements p w) guardWitness)

set_option maxHeartbeats 800000 in
theorem condition_primrec : Primrec (fun p : ((Parameters × Nat) × Witness) ×
    (Nat × RecordedGuardProgram.Witness) => condition p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : ((Parameters × Nat) × Witness) ×
      (Nat × RecordedGuardProgram.Witness) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : ((Parameters × Nat) × Witness) ×
      (Nat × RecordedGuardProgram.Witness) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hw : Primrec (fun p : ((Parameters × Nat) × Witness) ×
      (Nat × RecordedGuardProgram.Witness) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun p : ((Parameters × Nat) × Witness) ×
      (Nat × RecordedGuardProgram.Witness) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun p : ((Parameters × Nat) × Witness) ×
      (Nat × RecordedGuardProgram.Witness) => p.2.2) := Primrec.snd.comp Primrec.snd
  have he := Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hp))
  have hsource := RecordedMainSourceProgram.condition_primrec.comp
    ((((he.pair (Primrec.fst.comp hp)).pair (Primrec.fst.comp (Primrec.fst.comp hw))).pair ha).pair
      ((Primrec.snd.comp (Primrec.fst.comp hw)).pair hk))
  have result := Primrec.and.comp hsource
    (Primrec.and.comp (structuralCheck_primrec.comp ((hp.pair ha).pair hw))
      (RecordedGuardProgram.condition_primrec.comp
        (((guardData_primrec.comp hp hw).pair (requirements_primrec.comp hp hw)).pair hg)))
  exact result.of_eq (fun _ => rfl)

theorem guard_condition_exact (p : Parameters) (w : Witness) :
    (∃ g, RecordedGuardProgram.condition (guardData p w) (requirements p w) g = true) ↔
      (guardedAtom p w).MainGuarded (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.2.toFinset (markerPoints w.2.2) := by
  rw [RecordedGuardProgram.condition_correct]
  simpa only [guardData, requirements, markerPoints] using
    RecordedFormula.mainRequirementsCode_exact
      (fun μ ν => p.2.2.1.domain (Nat.pair μ ν)) (fun μ ν => p.2.2.2.domain (Nat.pair μ ν))
      p.1.2 (w.2.2.map Prod.fst) (guardedAtom p w)

theorem condition_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ cutoff g, condition p a w cutoff g = true) ↔ side p a w := by
  constructor
  · rintro ⟨cutoff, g, h⟩
    have hs := (Bool.and_eq_true_iff.mp h).1
    have ht := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have hg := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
    exact ⟨(RecordedMainSourceProgram.condition_correct _ _ _ _ _ _).mp ⟨cutoff, hs⟩,
      (structuralCheck_exact _ _ _).mp ht, (guard_condition_exact _ _).mp ⟨g, hg⟩⟩
  · rintro ⟨hs, ht, hg⟩
    obtain ⟨cutoff, hc⟩ := (RecordedMainSourceProgram.condition_correct _ _ _ _ _ _).mpr hs
    obtain ⟨g, hgc⟩ := (guard_condition_exact _ _).mpr hg
    exact ⟨cutoff, g, by simp only [condition, hc, (structuralCheck_exact _ _ _).mpr ht,
      hgc, Bool.true_and]⟩

def defaultParameters : Parameters := (([], []),
  ((Nat.Partrec.Code.zero, Nat.Partrec.Code.zero), (Nat.Partrec.Code.zero, Nat.Partrec.Code.zero)))
def defaultWitness : Witness := ((0, (((0, 0), 0), .falsum)), (([], []), []))
def decodeParameters (n : Nat) : Parameters := (Encodable.decode (α := Parameters) n).getD defaultParameters
def decodeCertificate (n : Nat) : Certificate :=
  (Encodable.decode (α := Certificate) n).getD (defaultWitness, (0, ([], [])))

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

theorem decodeCertificate_primrec : Primrec decodeCertificate :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (defaultWitness, (0, ([], []))))

@[simp] theorem decodeParameters_encode (p : Parameters) : decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

@[simp] theorem decodeCertificate_encode (c : Certificate) : decodeCertificate (Encodable.encode c) = c := by
  simp only [decodeCertificate, Encodable.encodek, Option.getD_some]

def check (key query certificate : Nat) : Bool :=
  let p := decodeParameters key
  let c := decodeCertificate certificate
  condition p query.unpair.1 c.1 c.2.1 c.2.2 &&
    (query.unpair.2 == (formula p query.unpair.1 c.1).code RecordedHead.code)

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Nat × Nat) × Nat => decodeParameters p.1.1) :=
    decodeParameters_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have ha := Primrec.fst.comp hq
  have hc : Primrec (fun p : (Nat × Nat) × Nat => decodeCertificate p.2) :=
    decodeCertificate_primrec.comp Primrec.snd
  have hw := Primrec.fst.comp hc
  have result := Primrec.and.comp (condition_primrec.comp (((hp.pair ha).pair hw).pair (Primrec.snd.comp hc)))
    (Primrec.beq.comp (Primrec.snd.comp hq) (code_primrec.comp (formula_primrec.comp ((hp.pair ha).pair hw))))
  exact result.of_eq (fun _ => by simp only [check, Bool.beq_eq_decide_eq])

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ certificate, check key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff, Part.some_dom,
    implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (p : Parameters) (a : Nat) (σ : Syntax) :
    (evaluation (Encodable.encode p) (Nat.pair a (σ.code RecordedHead.code))).Dom ↔ admits p a σ := by
  rw [evaluation_domain]
  constructor
  · rintro ⟨certificate, hc⟩
    simp only [check, Nat.unpair_pair, decodeParameters_encode] at hc
    generalize hdecode : decodeCertificate certificate = c at hc
    have ht := Bool.and_eq_true_iff.mp hc
    exact ⟨c.1, (condition_correct _ _ _).mp ⟨c.2.1, c.2.2, ht.1⟩,
      Formula.code_injective RecordedHead.code RecordedHead.code_injective (beq_iff_eq.mp ht.2)⟩
  · rintro ⟨w, hs, rfl⟩
    obtain ⟨cutoff, g, hc⟩ := (condition_correct _ _ _).mpr hs
    exact ⟨Encodable.encode (w, (cutoff, g)), by
      simp only [check, Nat.unpair_pair, decodeParameters_encode, decodeCertificate_encode,
        hc, beq_self_eq_true, Bool.true_and]⟩

theorem evaluation_only_sentences (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ a, ∃ σ : Syntax, query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
      σ.RecordedAdmissible (decodeParameters key).1.1.toFinset (decodeParameters key).1.2.toFinset := by
  obtain ⟨certificate, hc⟩ := (evaluation_domain _ _).mp h
  simp only [check] at hc
  generalize hdecode : decodeCertificate certificate = c at hc
  have hs : admits (decodeParameters key) query.unpair.1 (formula (decodeParameters key) query.unpair.1 c.1) :=
    ⟨c.1, (condition_correct _ _ _).mp ⟨c.2.1, c.2.2, (Bool.and_eq_true_iff.mp hc).1⟩, rfl⟩
  have he := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2
  refine ⟨query.unpair.1, formula (decodeParameters key) query.unpair.1 c.1, ?_,
    admits_closed hs, admits_admissible hs⟩
  rw [← he]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admits p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        σ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Parameters → Program := fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : Parameters) (query : Nat) :
      (compiler p).eval query = evaluation (Encodable.encode p) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_, ?_⟩
  · intro p a σ
    change ((compiler p).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct p a σ
  · intro p query h
    change ((compiler p).eval query).Dom at h
    rw [heval] at h
    simpa only [decodeParameters_encode] using evaluation_only_sentences _ _ h

theorem admits_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.2.1.1)
    (hhierarchy : ∀ j i, p.2.1.2.domain (Nat.pair j i) ↔ R j i) (a : Nat) (σ : Syntax) :
    admits p a σ ↔ RecordedMain C p.1.1.toFinset p.1.2.toFinset a
      (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
      (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) σ := by
  rw [← RecordedFiniteMain_exact 0 C p.1.1.toFinset p.1.2.toFinset a]
  constructor
  · rintro ⟨w, hs, rfl⟩
    obtain ⟨hm, hd, hn, hf, ha⟩ := hs.2.1
    have hrow := (RecordedMainSourceProgram.admits_exact C p.2.1.1 p.2.1.2
      hArithmetic hsource hhierarchy p.1.1 p.1.2 a (sourceFormula p w) (sourceAtom w)).mp
        ⟨w.1.1, w.1.2, hs.1, rfl, rfl⟩
    exact ⟨sourceFormula p w, sourceAtom w, w.2.1.1, w.2.1.2, w.2.2,
      hrow, hm, hd, hn, hf, hs.2.2, rfl, ha⟩
  · rintro ⟨source, distinguished, M, T, ms, hrow, hm, hd, hn, hf, hg, he, ha⟩
    obtain ⟨tag, row, hs, hσ, hatom⟩ :=
      (RecordedMainSourceProgram.admits_exact C p.2.1.1 p.2.1.2 hArithmetic hsource
        hhierarchy p.1.1 p.1.2 a source distinguished).mpr hrow
    subst source
    subst distinguished
    rw [he] at ha
    let w : Witness := ((tag, row), ((M, T), ms))
    exact ⟨w, ⟨hs, ⟨hm, hd, hn, hf, ha⟩, hg⟩, he⟩

end Alexander313.RecordedMainProgram
