import Alexander313.Effective.RecordedOrderedSeedPrograms
import Alexander313.RecordedStagePredicates

/-!
# Executing programs for the actual full recorded label cuts

The supplied full-admission program is filtered before finite consequence
compilation. Every label in an admitted axiom must have a positive computation
in the supplied order program below the cutoff. Consequences are then computed
from exactly these filtered axioms; the support of a conclusion is not used to
filter an already compiled unbounded theory.

The construction preserves every numerical substitution instance. It supplies
primitive-recursive program compilers and owner columns, with exact typed and
raw-code domains. Identification with the actual recorded stages uses explicit
executing source, hierarchy, validity, order, R1 and R2 program data. Ordinal
relations, reflection and soundness are not constructed here.
-/

noncomputable section

namespace Alexander313.RecordedLabelCutProgram

open RecordedFormula
open RecordedBackgroundProgram (positive positive_primrec positive_iff)
open OrderedRecordedAdmissionProgram (orderPairsCheck orderPairsCheck_primrec
  orderPairsCheck_correct)

abbrev GeneratorParameters := (Program × Program) × Nat

def defaultGeneratorParameters : GeneratorParameters :=
  ((Nat.Partrec.Code.zero, Nat.Partrec.Code.zero), 0)

def decodeGeneratorParameters (n : Nat) : GeneratorParameters :=
  (Encodable.decode (α := GeneratorParameters) n).getD defaultGeneratorParameters

theorem decodeGeneratorParameters_primrec : Primrec decodeGeneratorParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultGeneratorParameters)

@[simp] theorem decodeGeneratorParameters_encode (p : GeneratorParameters) :
    decodeGeneratorParameters (Encodable.encode p) = p := by
  simp only [decodeGeneratorParameters, Encodable.encodek, Option.getD_some]

/-- Independent bounds witness admission and all finitely many order edges. -/
def condition (p : GeneratorParameters) (query certificate : Nat) : Bool :=
  positive certificate.unpair.1 p.1.1 query &&
    orderPairsCheck p.1.2 certificate.unpair.2
      (labelEdges p.2 (labelListCode query.unpair.2))

theorem condition_primrec :
    Primrec (fun q : (GeneratorParameters × Nat) × Nat =>
      condition q.1.1 q.1.2 q.2) := by
  have hp : Primrec (fun q : (GeneratorParameters × Nat) × Nat => q.1.1) := Primrec.fst.comp Primrec.fst
  have hquery : Primrec (fun q : (GeneratorParameters × Nat) × Nat => q.1.2) := Primrec.snd.comp Primrec.fst
  have hbounds : Primrec (fun q : (GeneratorParameters × Nat) × Nat => q.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hsource := Primrec.fst.comp (Primrec.fst.comp hp)
  have horder := Primrec.snd.comp (Primrec.fst.comp hp)
  have hcut := Primrec.snd.comp hp
  have hlabels := labelListCode_primrec.comp
    (Primrec.snd.comp (Primrec.unpair.comp hquery))
  have result := Primrec.and.comp
    (positive_primrec.comp
      (((Primrec.fst.comp hbounds).pair hsource).pair hquery))
    (orderPairsCheck_primrec.comp
      ((horder.pair (Primrec.snd.comp hbounds)).pair
        (labelEdges_primrec.comp hcut hlabels)))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : GeneratorParameters) (query : Nat) :
    (∃ certificate, condition p query certificate = true) ↔
      p.1.1.domain query ∧
        ∀ μ ∈ labelListCode query.unpair.2, p.1.2.domain (Nat.pair μ p.2) := by
  constructor
  · rintro ⟨certificate, h⟩
    have hc := Bool.and_eq_true_iff.mp h
    refine ⟨(positive_iff p.1.1 query).mp ⟨certificate.unpair.1, hc.1⟩, ?_⟩
    exact (NestingRequirements.holds_edges _ p.2 _).mp
      ((orderPairsCheck_correct p.1.2 _).mp ⟨certificate.unpair.2, hc.2⟩)
  · rintro ⟨hadmitted, hbelow⟩
    obtain ⟨a, ha⟩ := (positive_iff p.1.1 query).mpr hadmitted
    obtain ⟨b, hb⟩ := (orderPairsCheck_correct p.1.2 _).mpr
      ((NestingRequirements.holds_edges _ p.2 _).mpr hbelow)
    exact ⟨Nat.pair a b, by simp only [condition, Nat.unpair_pair, ha, labelEdges, hb, Bool.true_and]⟩

def check (key query certificate : Nat) : Bool :=
  condition (decodeGeneratorParameters key) query certificate

theorem check_primrec :
    Primrec (fun q : (Nat × Nat) × Nat => check q.1.1 q.1.2 q.2) :=
  condition_primrec.comp
    (((decodeGeneratorParameters_primrec.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_correct (p : GeneratorParameters) (query : Nat) :
    (evaluation (Encodable.encode p) query).Dom ↔
      p.1.1.domain query ∧
        ∀ μ ∈ labelListCode query.unpair.2, p.1.2.domain (Nat.pair μ p.2) := by
  have hd : (evaluation (Encodable.encode p) query).Dom ↔
      ∃ certificate, check (Encodable.encode p) query certificate = true := by
    simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
      Part.some_dom, implies_true, and_true, Bool.true_eq]
  rw [hd]
  simpa only [check, decodeGeneratorParameters_encode] using condition_correct p query

theorem generator_compiler_exists :
    ∃ compiler : GeneratorParameters → Program, Primrec compiler ∧
      ∀ p query, (compiler p).domain query ↔ p.1.1.domain query ∧
        ∀ μ ∈ labelListCode query.unpair.2, p.1.2.domain (Nat.pair μ p.2) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : GeneratorParameters → Program :=
    fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : GeneratorParameters) (query : Nat) :
      (compiler p).eval query = evaluation (Encodable.encode p) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler,
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_⟩
  intro p query
  change ((compiler p).eval query).Dom ↔ _
  rw [heval]
  exact evaluation_correct p query

abbrev Parameters := OrderedRecordedSeedProgram.Parameters × Nat

def admissions (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  letI : LT Nat := Program.orderLT p.1.2
  LabelCut (OrderedRecordedSeedProgram.admissions p.1 a) p.2 σ

theorem admission_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
      admissions p a σ) ∧
    (∀ p query, (compiler p).domain query ↔ ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧ admissions p a σ) := by
  obtain ⟨source, hsource, exactSource, rawSource⟩ :=
    OrderedRecordedSeedProgram.admission_compiler_exists
  obtain ⟨filter, hfilter, exactFilter⟩ := generator_compiler_exists
  let parameters : Parameters → GeneratorParameters :=
    fun p => ((source p.1, p.1.2), p.2)
  have hp : Primrec parameters :=
    ((hsource.comp Primrec.fst).pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  have typed (p : Parameters) (a : Nat) (σ : Syntax) :
      (filter (parameters p)).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
        admissions p a σ := by
    letI : LT Nat := Program.orderLT p.1.2
    change (filter (parameters p)).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
      OrderedRecordedSeedProgram.admissions p.1 a σ ∧
        ∀ μ ∈ σ.labelSupport, p.1.2.domain (Nat.pair μ p.2)
    simpa only [parameters, Nat.unpair_pair, labelListCode_code, exactSource,
      admissions, LabelCut, Formula.mem_labelList_iff] using
        exactFilter (parameters p) (Nat.pair a (σ.code RecordedHead.code))
  refine ⟨fun p => filter (parameters p), hfilter.comp hp, typed, ?_⟩
  intro p query
  constructor
  · intro h
    have hs := ((exactFilter (parameters p) query).mp h).1
    obtain ⟨a, σ, hquery, hclosed, _⟩ := rawSource p.1 query hs
    exact ⟨a, σ, hquery, hclosed, (typed p a σ).mp (hquery ▸ h)⟩
  · rintro ⟨a, σ, rfl, _, hσ⟩
    exact (typed p a σ).mpr hσ

theorem admissions_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.1.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    admissions p a σ ↔
      (letI : LT Nat := Program.orderLT p.1.2
       LabelCut (FullRecordedAdmissions C p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset a
         (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν))) p.2 σ) := by
  letI : LT Nat := Program.orderLT p.1.2
  exact and_congr
    (OrderedRecordedSeedProgram.admissions_exact C p.1
      hArithmetic hsource hhierarchy hvalid a σ) Iff.rfl

theorem theory_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters),
      C.arithmetic = canonicalArithmeticCoding Nat →
      C.family.effective.recognizes = p.1.1.1.2.1.1 →
      (∀ j i, p.1.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i) →
      (∀ φ : Formula Nat, p.1.1.2.domain (φ.code id) ↔ Valid φ) → ∀ a σ,
        (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
          (letI : LT Nat := Program.orderLT p.1.2
           σ.Closed ∧ Provable
             (LabelCut
               (FullRecordedAdmissions C p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset a
                 (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν))
                 (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν))) p.2) σ)) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed) := by
  obtain ⟨generators, hgen, exactGen, _⟩ := admission_compiler_exists
  obtain ⟨consequences, hcon, exactCon, rawCon⟩ := RecordedConsequenceProgram.compiler_exists
  let parameters : Parameters → Program × Program := fun p => (generators p, p.1.1.2)
  have hp : Primrec parameters := hgen.pair
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  refine ⟨fun p => consequences (parameters p), hcon.comp hp, ?_, ?_⟩
  · intro R C p hArithmetic hsource hhierarchy hvalid a σ
    letI : LT Nat := Program.orderLT p.1.2
    exact (exactCon (generators p) p.1.1.2 a σ).trans
      (RecordedConsequenceProgram.generated_exact (generators p) p.1.1.2 hvalid
        (fun b θ => LabelCut
          (FullRecordedAdmissions C p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset b
            (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν))
            (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν))) p.2 θ)
        (fun b θ => (exactGen p b θ).trans
          (admissions_exact C p hArithmetic hsource hhierarchy hvalid b θ))
        (fun _ _ h => h.1.closed) a σ)
  · intro p query h
    exact rawCon (parameters p) query h

def theoryCompiler : Parameters → Program := Classical.choose theory_compiler_exists

theorem theoryCompiler_primrec : Primrec theoryCompiler :=
  (Classical.choose_spec theory_compiler_exists).1

theorem theoryCompiler_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.1.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    (theoryCompiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
      (letI : LT Nat := Program.orderLT p.1.2
       σ.Closed ∧ Provable
         (LabelCut
           (FullRecordedAdmissions C p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset a
             (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν))
             (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν))) p.2) σ) :=
  (Classical.choose_spec theory_compiler_exists).2.1 C p
    hArithmetic hsource hhierarchy hvalid a σ

theorem theoryCompiler_raw_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.1.2.domain (φ.code id) ↔ Valid φ)
    (query : Nat) :
    (theoryCompiler p).domain query ↔ ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧
        (letI : LT Nat := Program.orderLT p.1.2
         σ.Closed ∧ Provable
           (LabelCut
             (FullRecordedAdmissions C p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset a
               (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν))
               (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν))) p.2) σ) := by
  constructor
  · intro h
    obtain ⟨a, σ, hquery, _⟩ := (Classical.choose_spec theory_compiler_exists).2.2 p query h
    exact ⟨a, σ, hquery,
      (theoryCompiler_exact C p hArithmetic hsource hhierarchy hvalid a σ).mp (hquery ▸ h)⟩
  · rintro ⟨a, σ, rfl, hσ⟩
    exact (theoryCompiler_exact C p hArithmetic hsource hhierarchy hvalid a σ).mpr hσ

def ownerColumn (p : Parameters) (a : Nat) : Program := (theoryCompiler p).column a

theorem ownerColumn_primrec : Primrec₂ ownerColumn :=
  (Program.column_primrec.comp (theoryCompiler_primrec.comp Primrec.fst) Primrec.snd).to₂

theorem ownerColumn_raw_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.1.2.domain (φ.code id) ↔ Valid φ)
    (a query : Nat) :
    (ownerColumn p a).domain query ↔ ∃ σ : Syntax,
      query = σ.code RecordedHead.code ∧
        (letI : LT Nat := Program.orderLT p.1.2
         σ.Closed ∧ Provable
           (LabelCut
             (FullRecordedAdmissions C p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset a
               (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν))
               (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν))) p.2) σ) := by
  rw [ownerColumn, Program.column_domain,
    theoryCompiler_raw_exact C p hArithmetic hsource hhierarchy hvalid]
  constructor
  · rintro ⟨b, σ, hquery, hσ⟩
    have hab : a = b := by
      simpa only [Nat.unpair_pair] using congrArg (fun n => n.unpair.1) hquery
    have hc : query = σ.code RecordedHead.code := by
      simpa only [Nat.unpair_pair] using congrArg (fun n => n.unpair.2) hquery
    exact ⟨σ, hc, hab.symm ▸ hσ⟩
  · rintro ⟨σ, hquery, hσ⟩
    exact ⟨a, σ, congrArg (Nat.pair a) hquery, hσ⟩

/-- Exact identification with the literal stage predicate under the supplied
    label order. No recursive decision of negative relation facts is required. -/
theorem stage_exact [labelOrder : LinearOrder Nat] {R : Nat → Nat → Prop}
    (C : CommonCorePresentation R) (p : Parameters) (R₁ R₂ : Nat → Nat → Prop)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.1.2.domain (φ.code id) ↔ Valid φ)
    (horder : ∀ μ ν, p.1.2.domain (Nat.pair μ ν) ↔ @LT.lt Nat labelOrder.toLT μ ν)
    (hR₁ : ∀ μ ν, p.1.1.1.2.2.1.domain (Nat.pair μ ν) ↔ R₁ μ ν)
    (hR₂ : ∀ μ ν, p.1.1.1.2.2.2.domain (Nat.pair μ ν) ↔ R₂ μ ν)
    (a : Nat) (σ : Syntax) :
    (theoryCompiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
      @RecordedStage.cuts Nat labelOrder R C
        p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset R₁ R₂ a p.2 σ := by
  have ho : Program.orderLT p.1.2 = labelOrder.toLT :=
    congrArg LT.mk (funext fun μ => funext fun ν => propext (horder μ ν))
  have hd : labelOrder.toDecidableEq = instDecidableEqNat :=
    Subsingleton.elim _ _
  have h₁ : (fun μ ν => p.1.1.1.2.2.1.domain (Nat.pair μ ν)) = R₁ :=
    funext fun μ => funext fun ν => propext (hR₁ μ ν)
  have h₂ : (fun μ ν => p.1.1.1.2.2.2.domain (Nat.pair μ ν)) = R₂ :=
    funext fun μ => funext fun ν => propext (hR₂ μ ν)
  have h := theoryCompiler_exact C p hArithmetic hsource hhierarchy hvalid a σ
  rw [ho, h₁, h₂] at h
  have hadmissions := congrArg (fun dec =>
    @LabelCut Nat Nat dec labelOrder.toLT
      (@FullRecordedAdmissions Nat dec labelOrder.toLT R C
        p.1.1.1.1.1.toFinset p.1.1.1.1.2.toFinset a R₁ R₂) p.2) hd.symm
  rw [hadmissions] at h
  simpa only [RecordedStage.cuts, RecordedStage.theory] using h

end Alexander313.RecordedLabelCutProgram
