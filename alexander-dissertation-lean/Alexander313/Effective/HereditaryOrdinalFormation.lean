import Alexander313.Effective.HereditaryThetaPrograms
import Alexander313.Effective.HereditaryOrdinalLabels
import Alexander313.Effective.RecordedOrderedFormation
import Alexander313.RecordedLabelMaps

/-!
# Recorded formation with actual hereditary ordinal labels

The order is the executing union-order Program, including both original
union-domain guards. A separate whole-support test checks isolated labels
as well as labels below live and ghost heads. On that domain, relabeling by
the actual ordinal interpretation preserves and reflects the existing whole
nesting and recorded admission predicates. Raw codes need no linear order
or injective interpretation. This does not construct either Wilken edge
relation or identify the finite-base limit with the prescribed endpoint.
-/

noncomputable section

namespace Alexander313.HereditaryOrdinalFormation

open RecordedFormula RecordedGuardProgram
open Wilken.RelativeTerm.Hereditary
open HereditaryOrdinalLabels (Label value labelOf labelOf_value labelOf_lt_iff label_lt_iff)

def ordinalOrder : Program := HereditaryThetaProgram.recognizerColumn 6

theorem ordinalOrder_domain (μ ν : Nat) :
    ordinalOrder.domain (Nat.pair μ ν) ↔
      unionCheck μ = true ∧ unionCheck ν = true ∧
        unionInterpretation μ < unionInterpretation ν :=
  HereditaryThetaProgram.union_order_domain μ ν

theorem orderLT_iff (μ ν : Nat) :
    @LT.lt Nat (Program.orderLT ordinalOrder) μ ν ↔
      unionCheck μ = true ∧ unionCheck ν = true ∧
        unionInterpretation μ < unionInterpretation ν :=
  ordinalOrder_domain μ ν

/-- Every indexed label in the whole literal formula belongs to the original
hereditary union domain. The support includes all modal contexts. -/
def Supported (φ : Syntax) : Prop :=
  ∀ μ ∈ φ.labelSupport, unionCheck μ = true

def labelCheckCode (n : Nat) : Bool :=
  allCheck unionCheck (RecordedFormula.labelListCode n)

theorem labelCheckCode_primrec : Primrec labelCheckCode := by
  have ht : Primrec₂ (fun (_ : Unit) (μ : Nat) => unionCheck μ) :=
    (Uniform.unionCheck_primrec.comp Primrec.snd).to₂
  exact (allCheck_primrec _ ht).comp (Primrec.const ()) labelListCode_primrec

def labelCheck (φ : Syntax) : Bool := labelCheckCode (φ.code RecordedHead.code)

theorem labelCheck_primrec : Primrec labelCheck :=
  labelCheckCode_primrec.comp code_primrec

theorem labelCheck_exact (φ : Syntax) : labelCheck φ = true ↔ Supported φ := by
  simp only [labelCheck, labelCheckCode, labelListCode_code, allCheck_iff,
    Formula.mem_labelList_iff, Supported]

@[simp] theorem supported_subst (φ : Syntax) (σ : NumericalSubstitution) :
    Supported (φ.subst σ) ↔ Supported φ := by
  simp only [Supported, Formula.labelSupport_subst]

@[simp] theorem supported_close (φ : Syntax) (s : Assignment) :
    Supported (φ.close s) ↔ Supported φ := by
  simp only [Supported, Formula.labelSupport_close]

/-- Literal label relabeling; arithmetic, owners, and binder names remain the
ones in the original recorded formula. -/
def denotation (φ : Syntax) : Formula (RecordedHead Nat Label) :=
  φ.relabel labelOf

@[simp] theorem denotation_subst (φ : Syntax) (σ : NumericalSubstitution) :
    denotation (φ.subst σ) = (denotation φ).subst σ := Formula.relabel_subst φ labelOf σ

@[simp] theorem denotation_close (φ : Syntax) (s : Assignment) :
    denotation (φ.close s) = (denotation φ).close s := Formula.relabel_close φ labelOf s

@[simp] theorem denotation_erase (φ : Syntax) : (denotation φ).erase = φ.erase :=
  Formula.erase_relabel φ labelOf

@[simp] theorem denotation_closed (φ : Syntax) : (denotation φ).Closed ↔ φ.Closed := by
  simp only [Formula.Closed, denotation, Formula.freeVars_relabel]

theorem support_below_exact (φ : Syntax) (hφ : Supported φ)
    (ν : Nat) (hν : unionCheck ν = true) :
    (letI : LT Nat := Program.orderLT ordinalOrder
     ∀ μ ∈ φ.labelSupport, μ < ν) ↔
      ∀ ξ ∈ (denotation φ).labelSupport, ξ < labelOf ν := by
  classical
  letI : LT Nat := Program.orderLT ordinalOrder
  rw [denotation, Formula.labelSupport_relabel]
  constructor
  · intro h ξ hξ
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hξ
    exact (labelOf_lt_iff μ ν (hφ μ hμ) hν).mpr
      ((orderLT_iff μ ν).mp (h μ hμ)).2.2
  · intro h μ hμ
    exact (orderLT_iff μ ν).mpr
      ⟨hφ μ hμ, hν, (labelOf_lt_iff μ ν (hφ μ hμ) hν).mp
        (h _ (Finset.mem_image.mpr ⟨μ, hμ, rfl⟩))⟩

theorem support_below_value_exact (φ : Syntax) (hφ : Supported φ)
    (ν : Nat) (hν : unionCheck ν = true) :
    (letI : LT Nat := Program.orderLT ordinalOrder
     ∀ μ ∈ φ.labelSupport, μ < ν) ↔
      ∀ ξ ∈ (denotation φ).labelSupport, value ξ < unionInterpretation ν := by
  rw [support_below_exact φ hφ ν hν]
  simp only [label_lt_iff, labelOf_value ν hν]

theorem stratified_exact (φ : Syntax) (hφ : Supported φ) :
    (letI : LT Nat := Program.orderLT ordinalOrder
     φ.GloballyStratified) ↔ (denotation φ).GloballyStratified := by
  classical
  letI : LT Nat := Program.orderLT ordinalOrder
  revert hφ
  induction φ with
  | falsum => intro _; rfl
  | equal t u => intro _; rfl
  | imp φ ψ ihφ ihψ =>
    intro h
    have hφ : Supported φ := fun μ hμ => h μ (Finset.mem_union_left _ hμ)
    have hψ : Supported ψ := fun μ hμ => h μ (Finset.mem_union_right _ hμ)
    exact and_congr (ihφ hφ) (ihψ hψ)
  | conj φ ψ ihφ ihψ =>
    intro h
    have hφ : Supported φ := fun μ hμ => h μ (Finset.mem_union_left _ hμ)
    have hψ : Supported ψ := fun μ hμ => h μ (Finset.mem_union_right _ hμ)
    exact and_congr (ihφ hφ) (ihψ hψ)
  | disj φ ψ ihφ ihψ =>
    intro h
    have hφ : Supported φ := fun μ hμ => h μ (Finset.mem_union_left _ hμ)
    have hψ : Supported ψ := fun μ hμ => h μ (Finset.mem_union_right _ hμ)
    exact and_congr (ihφ hφ) (ihψ hψ)
  | neg φ ih => intro h; exact ih h
  | all x φ ih => intro h; exact ih h
  | ex x φ ih => intro h; exact ih h
  | know a φ ih =>
    cases a with
    | live a => intro h; exact ih h
    | ghost a => intro h; exact ih h
    | indexed a ν =>
      intro h
      have hφ : Supported φ := fun μ hμ => h μ (Finset.mem_insert_of_mem hμ)
      have hν : unionCheck ν = true := h ν (Finset.mem_insert_self _ _)
      exact and_congr (ih hφ) (support_below_exact φ hφ ν hν)

theorem admissible_exact (AE : List Nat × List Nat) (φ : Syntax)
    (hφ : Supported φ) :
    (letI : LT Nat := Program.orderLT ordinalOrder
     φ.RecordedAdmissible AE.1.toFinset AE.2.toFinset) ↔
      (denotation φ).RecordedAdmissible AE.1.toFinset AE.2.toFinset := by
  classical
  letI : LT Nat := Program.orderLT ordinalOrder
  exact and_congr
    (Formula.headsAllowed_relabel AE.1.toFinset AE.2.toFinset φ labelOf).symm
    (stratified_exact φ hφ)

/-- The literal total union-order decision algorithm underlying `ordinalOrder`.
Both original union-domain checks are retained on every raw input. -/
def unionLess (μ ν : Nat) : Bool :=
  HereditaryThetaProgram.crossLess μ.unpair.1 μ.unpair.2 ν.unpair.1 ν.unpair.2

theorem unionLess_primrec : Primrec₂ unionLess :=
  (HereditaryThetaProgram.crossLess_primrec.comp
    ((Primrec.unpair.comp Primrec.fst).pair (Primrec.unpair.comp Primrec.snd))).to₂

theorem unionLess_exact (μ ν : Nat) : unionLess μ ν = true ↔
    unionCheck μ = true ∧ unionCheck ν = true ∧
      unionInterpretation μ < unionInterpretation ν := by
  simpa only [unionLess, unionCheck, unionInterpretation] using
    HereditaryThetaProgram.crossLess_exact μ.unpair.1 μ.unpair.2 ν.unpair.1 ν.unpair.2

theorem unionLess_orderLT (μ ν : Nat) : unionLess μ ν = true ↔
    @LT.lt Nat (Program.orderLT ordinalOrder) μ ν :=
  (unionLess_exact μ ν).trans (orderLT_iff μ ν).symm

def nestingCheckCode (n : Nat) : Bool :=
  allCheck (fun p : Nat × Nat => unionLess p.1 p.2)
    (OrderedRecordedFormula.nestingRequirementsCode n)

theorem nestingCheckCode_primrec : Primrec nestingCheckCode := by
  have ht : Primrec₂ (fun (_ : Unit) (p : Nat × Nat) => unionLess p.1 p.2) :=
    (unionLess_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (allCheck_primrec _ ht).comp (Primrec.const ())
    OrderedRecordedFormula.nestingRequirementsCode_primrec

theorem nestingCheckCode_exact (φ : Syntax) :
    nestingCheckCode (φ.code RecordedHead.code) = true ↔
      letI : LT Nat := Program.orderLT ordinalOrder
      φ.GloballyStratified := by
  letI : LT Nat := Program.orderLT ordinalOrder
  simp only [nestingCheckCode, OrderedRecordedFormula.nestingRequirementsCode_code,
    allCheck_iff, unionLess_orderLT]
  exact Formula.nestingRequirements_exact φ

def admissionCheckCode (AE : List Nat × List Nat) (n : Nat) : Bool :=
  labelCheckCode n && (headsAllowedCode AE n && nestingCheckCode n)

theorem admissionCheckCode_primrec : Primrec₂ admissionCheckCode :=
  (Primrec.and.comp (labelCheckCode_primrec.comp Primrec.snd)
    (Primrec.and.comp headsAllowedCode_primrec
      (nestingCheckCode_primrec.comp Primrec.snd))).to₂

def admissionCheck (AE : List Nat × List Nat) (φ : Syntax) : Bool :=
  admissionCheckCode AE (φ.code RecordedHead.code)

theorem admissionCheck_primrec : Primrec₂ admissionCheck :=
  (admissionCheckCode_primrec.comp Primrec.fst
    (code_primrec.comp Primrec.snd)).to₂

theorem admissionCheck_code_order (AE : List Nat × List Nat) (φ : Syntax) :
    admissionCheck AE φ = true ↔ Supported φ ∧
      (letI : LT Nat := Program.orderLT ordinalOrder
       φ.RecordedAdmissible AE.1.toFinset AE.2.toFinset) := by
  letI : LT Nat := Program.orderLT ordinalOrder
  change (labelCheck φ && (headsAllowedCode AE (φ.code RecordedHead.code) &&
    nestingCheckCode (φ.code RecordedHead.code))) = true ↔ _
  simp only [Bool.and_eq_true, labelCheck_exact, headsAllowedCode_code,
    nestingCheckCode_exact, Formula.RecordedAdmissible]

theorem admissionCheck_exact (AE : List Nat × List Nat) (φ : Syntax) :
    admissionCheck AE φ = true ↔ Supported φ ∧
      (denotation φ).RecordedAdmissible AE.1.toFinset AE.2.toFinset := by
  rw [admissionCheck_code_order]
  constructor
  · rintro ⟨hφ, h⟩
    exact ⟨hφ, (admissible_exact AE φ hφ).mp h⟩
  · rintro ⟨hφ, h⟩
    exact ⟨hφ, (admissible_exact AE φ hφ).mpr h⟩

theorem admissionCheck_ordered_condition (AE : List Nat × List Nat) (φ : Syntax) :
    admissionCheck AE φ = true ↔ Supported φ ∧
      ∃ cutoff, OrderedRecordedAdmissionProgram.condition ordinalOrder AE φ cutoff = true := by
  rw [admissionCheck_code_order, OrderedRecordedAdmissionProgram.condition_correct]

def sentenceCheck (AE : List Nat × List Nat) (φ : Syntax) : Bool :=
  Formula.isClosedCode (φ.code RecordedHead.code) && admissionCheck AE φ

theorem sentenceCheck_primrec : Primrec₂ sentenceCheck :=
  (Primrec.and.comp
    (Formula.isClosedCode_primrec.comp (code_primrec.comp Primrec.snd))
    admissionCheck_primrec).to₂

theorem sentenceCheck_exact (AE : List Nat × List Nat) (φ : Syntax) :
    sentenceCheck AE φ = true ↔ φ.Closed ∧ Supported φ ∧
      (denotation φ).RecordedAdmissible AE.1.toFinset AE.2.toFinset := by
  simp only [sentenceCheck, Bool.and_eq_true,
    RecordedPrefixProgram.recorded_closed_code, admissionCheck_exact]

abbrev Parameters := List Nat × List Nat

def defaultParameters : Parameters := ([], [])

def decodeParameters (n : Nat) : Parameters :=
  (Encodable.decode (α := Parameters) n).getD defaultParameters

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

@[simp] theorem decodeParameters_encode (p : Parameters) :
    decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

def rawCheck (key query : Nat) : Bool :=
  isCode query && admissionCheckCode (decodeParameters key) query

theorem rawCheck_primrec : Primrec₂ rawCheck :=
  (Primrec.and.comp (isCode_primrec.comp Primrec.snd)
    (admissionCheckCode_primrec.comp (decodeParameters_primrec.comp Primrec.fst)
      Primrec.snd)).to₂

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun _ => Part.some (rawCheck key query))

theorem evaluation_partrec : Partrec₂ evaluation := by
  have h : Primrec (fun p : (Nat × Nat) × Nat => rawCheck p.1.1 p.1.2) :=
    rawCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  exact (Partrec.rfind h.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ rawCheck key query = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

theorem evaluation_correct (p : Parameters) (φ : Syntax) :
    (evaluation (Encodable.encode p) (φ.code RecordedHead.code)).Dom ↔
      Supported φ ∧ (denotation φ).RecordedAdmissible p.1.toFinset p.2.toFinset := by
  rw [evaluation_domain]
  have hsyntax : isCode (φ.code RecordedHead.code) = true :=
    (isCode_iff _).mpr ⟨φ, rfl⟩
  simp only [rawCheck, decodeParameters_encode, hsyntax, Bool.true_and]
  exact admissionCheck_exact p φ

theorem evaluation_only_formulas (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ Supported φ ∧
      (denotation φ).RecordedAdmissible (decodeParameters key).1.toFinset
        (decodeParameters key).2.toFinset := by
  have hh := Bool.and_eq_true_iff.mp ((evaluation_domain key query).mp h)
  obtain ⟨φ, hφ⟩ := (isCode_iff query).mp hh.1
  have hadm : admissionCheck (decodeParameters key) φ = true := by
    simpa only [admissionCheck, hφ] using hh.2
  exact ⟨φ, hφ.symm, (admissionCheck_exact _ φ).mp hadm⟩

/-- A genuinely constructed uniform Program, with the original domain on
every label. Raw acceptance is exactly the typed semantic formation image;
open formulas are allowed, and sentence closedness is tested separately. -/
theorem compiler_exists :
    ∃ compiler : Parameters → Program, Primrec compiler ∧
      (∀ p φ, (compiler p).domain (φ.code RecordedHead.code) ↔
        Supported φ ∧ (denotation φ).RecordedAdmissible p.1.toFinset p.2.toFinset) ∧
      (∀ p query, (compiler p).domain query ↔
        ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ Supported φ ∧
          (denotation φ).RecordedAdmissible p.1.toFinset p.2.toFinset) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Parameters → Program := fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : Parameters) (query : Nat) :
      (compiler p).eval query = evaluation (Encodable.encode p) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_, ?_⟩
  · intro p φ
    change ((compiler p).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct p φ
  · intro p query
    change ((compiler p).eval query).Dom ↔ _
    rw [heval]
    constructor
    · intro h
      simpa only [decodeParameters_encode] using evaluation_only_formulas _ _ h
    · rintro ⟨φ, rfl, hφ⟩
      exact (evaluation_correct p φ).mpr hφ

end Alexander313.HereditaryOrdinalFormation
