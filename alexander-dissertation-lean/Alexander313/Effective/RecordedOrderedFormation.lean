import Alexander313.Effective.RecordedOrder
import Alexander313.Effective.RecordedGuardPrograms
import Alexander313.Effective.RecordedPrefixPrograms

/-!
# Actual positive admissibility checks for an executing label-order Program

The finite nesting list visits every indexed head and every indexed label in
its whole argument, including beneath live and ghost heads. All listed order
edges require positive bounded computations. Owner policy is the existing
literal finite owner test. Labels are never compared by their Nat code order.

The admission checker accepts open as well as closed syntax. Closedness has
its own explicit finite test below. The order Program remains ordinary data;
this does not supply Wilken's ordinal-domain or comparison implementation.
-/

noncomputable section

namespace Alexander313
namespace NestingRequirements

def Holds {Label : Type} (relation : Label → Label → Prop) (L : List (Label × Label)) : Prop :=
  ∀ p ∈ L, relation p.1 p.2

@[simp] theorem holds_nil {Label : Type} (relation : Label → Label → Prop) :
    Holds relation [] := by simp [Holds]

@[simp] theorem holds_append {Label : Type} (relation : Label → Label → Prop)
    (L M : List (Label × Label)) :
    Holds relation (L ++ M) ↔ Holds relation L ∧ Holds relation M := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
      fun p hp => h p (List.mem_append_right _ hp)⟩
  · rintro ⟨hL, hM⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hL p hp
    · exact hM p hp

theorem holds_edges {Label : Type} (relation : Label → Label → Prop)
    (ν : Label) (L : List Label) :
    Holds relation (L.map (fun μ => (μ, ν))) ↔ ∀ μ ∈ L, relation μ ν := by
  constructor
  · intro h μ hμ
    exact h (μ, ν) (List.mem_map.mpr ⟨μ, hμ, rfl⟩)
  · intro h p hp
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hp
    exact h μ hμ

end NestingRequirements
namespace Formula

/-- Whole argument support contributes one edge to the containing indexed
    label. Live and ghost heads continue traversal. Repetition is retained. -/
def nestingRequirements {Owner Label : Type} :
    Formula (RecordedHead Owner Label) → List (Label × Label)
  | .falsum => []
  | .equal _ _ => []
  | .imp φ ψ => φ.nestingRequirements ++ ψ.nestingRequirements
  | .conj φ ψ => φ.nestingRequirements ++ ψ.nestingRequirements
  | .disj φ ψ => φ.nestingRequirements ++ ψ.nestingRequirements
  | .neg φ => φ.nestingRequirements
  | .all _ φ => φ.nestingRequirements
  | .ex _ φ => φ.nestingRequirements
  | .know (.live _) φ => φ.nestingRequirements
  | .know (.ghost _) φ => φ.nestingRequirements
  | .know (.indexed _ ν) φ =>
      φ.nestingRequirements ++ φ.labelList.map (fun μ => (μ, ν))

theorem nestingRequirements_exact {Owner Label : Type} [DecidableEq Label] [LT Label]
    (φ : Formula (RecordedHead Owner Label)) :
    NestingRequirements.Holds (fun μ ν => μ < ν) φ.nestingRequirements ↔
      φ.GloballyStratified := by
  induction φ with
  | know a φ ih =>
    cases a with
    | live a => exact ih
    | ghost a => exact ih
    | indexed a ν =>
      simp only [nestingRequirements, NestingRequirements.holds_append,
        NestingRequirements.holds_edges, mem_labelList_iff, GloballyStratified]
      exact and_congr ih Iff.rfl
  | _ => simp_all [nestingRequirements, GloballyStratified]

end Formula
namespace OrderedRecordedFormula

open RecordedFormula

def nestingHead (_ : Unit) (owner body : Nat) (value : List (Nat × Nat)) : List (Nat × Nat) :=
  cond (owner.unpair.1 == 1)
    (value ++ labelEdges owner.unpair.2.unpair.2 (labelListCode body)) value

theorem nestingHead_primrec :
    Primrec (fun p : Unit × (Nat × (Nat × List (Nat × Nat))) =>
      nestingHead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ho : Primrec (fun p : Unit × (Nat × (Nat × List (Nat × Nat))) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht := Primrec.fst.comp (Primrec.unpair.comp ho)
  have hν := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ho)))
  have hb : Primrec (fun p : Unit × (Nat × (Nat × List (Nat × Nat))) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun p : Unit × (Nat × (Nat × List (Nat × Nat))) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.beq.comp ht (Primrec.const 1)).cond
    (Primrec.list_append.comp hv (labelEdges_primrec.comp hν (labelListCode_primrec.comp hb))) hv

def nestingRequirementsCode (n : Nat) : List (Nat × Nat) :=
  ValueFold.code (· ++ ·) id [] nestingHead () n

theorem nestingRequirementsCode_primrec : Primrec nestingRequirementsCode :=
  (ValueFold.code_primrec _ _ _ _ Primrec.list_append Primrec.id nestingHead_primrec).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem nestingRequirementsCode_code (φ : Syntax) :
    nestingRequirementsCode (φ.code RecordedHead.code) = φ.nestingRequirements := by
  unfold nestingRequirementsCode
  rw [ValueFold.code_formula]
  induction φ with
  | know a φ ih => cases a <;>
      simp_all [ValueFold.formula, nestingHead, Formula.nestingRequirements, labelEdges,
        RecordedHead.code, Nat.unpair_pair]
  | _ => simp_all [ValueFold.formula, Formula.nestingRequirements]

theorem nestingRequirementsCode_exact (order : Program) (φ : Syntax) :
    NestingRequirements.Holds (fun μ ν => order.domain (Nat.pair μ ν))
      (nestingRequirementsCode (φ.code RecordedHead.code)) ↔
      letI : LT Nat := Program.orderLT order
      φ.GloballyStratified := by
  letI : LT Nat := Program.orderLT order
  rw [nestingRequirementsCode_code]
  exact Formula.nestingRequirements_exact φ

end OrderedRecordedFormula
namespace OrderedRecordedAdmissionProgram

open RecordedFormula RecordedGuardProgram OrderedRecordedFormula
open RecordedBackgroundProgram (positive positive_primrec positive_iff)

def orderPairsCheck (order : Program) (cutoff : Nat) (L : List (Nat × Nat)) : Bool :=
  allCheck (fun p => positive cutoff order (Nat.pair p.1 p.2)) L

theorem orderPairsCheck_primrec :
    Primrec (fun p : (Program × Nat) × List (Nat × Nat) =>
      orderPairsCheck p.1.1 p.1.2 p.2) := by
  have ht : Primrec₂ (fun (p : Program × Nat) (q : Nat × Nat) =>
      positive p.2 p.1 (Nat.pair q.1 q.2)) :=
    (positive_primrec.comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))).to₂
  exact allCheck_primrec _ ht

theorem orderPairsCheck_correct (order : Program) (L : List (Nat × Nat)) :
    (∃ cutoff, orderPairsCheck order cutoff L = true) ↔
      NestingRequirements.Holds (fun μ ν => order.domain (Nat.pair μ ν)) L := by
  constructor
  · rintro ⟨k, h⟩ p hp
    exact (positive_iff order _).mp ⟨k, (allCheck_iff _ _).mp h p hp⟩
  · intro h
    have hencoded : ∀ n ∈ L.map (fun p => Nat.pair p.1 p.2), order.domain n := by
      intro n hn
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
      exact h p hp
    obtain ⟨k, hk⟩ := (finite_positive order (L.map (fun p => Nat.pair p.1 p.2))).mpr hencoded
    refine ⟨k, (allCheck_iff _ _).mpr ?_⟩
    intro p hp
    exact hk _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

def conditionCode (order : Program) (AE : List Nat × List Nat) (n cutoff : Nat) : Bool :=
  headsAllowedCode AE n && orderPairsCheck order cutoff (nestingRequirementsCode n)

theorem conditionCode_primrec :
    Primrec (fun p : ((Program × (List Nat × List Nat)) × Nat) × Nat =>
      conditionCode p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hp : Primrec (fun p : ((Program × (List Nat × List Nat)) × Nat) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ho := Primrec.fst.comp hp
  have hAE := Primrec.snd.comp hp
  have hn : Primrec (fun p : ((Program × (List Nat × List Nat)) × Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact Primrec.and.comp (headsAllowedCode_primrec.comp hAE hn)
    (orderPairsCheck_primrec.comp
      ((ho.pair Primrec.snd).pair (nestingRequirementsCode_primrec.comp hn)))

def condition (order : Program) (AE : List Nat × List Nat) (φ : Syntax) (cutoff : Nat) : Bool :=
  conditionCode order AE (φ.code RecordedHead.code) cutoff

theorem condition_primrec :
    Primrec (fun p : ((Program × (List Nat × List Nat)) × Syntax) × Nat =>
      condition p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  conditionCode_primrec.comp
    (((Primrec.fst.comp Primrec.fst).pair
      (code_primrec.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)

theorem condition_correct (order : Program) (AE : List Nat × List Nat) (φ : Syntax) :
    (∃ cutoff, condition order AE φ cutoff = true) ↔
      letI : LT Nat := Program.orderLT order
      φ.RecordedAdmissible AE.1.toFinset AE.2.toFinset := by
  letI : LT Nat := Program.orderLT order
  simp only [condition, conditionCode, Bool.and_eq_true, exists_and_left,
    headsAllowedCode_code, orderPairsCheck_correct, nestingRequirementsCode_code,
    Formula.RecordedAdmissible]
  exact and_congr Iff.rfl (Formula.nestingRequirements_exact φ)

/-- Closedness is a separate requirement; the unrestricted admission condition
    above computes the existing admissibility predicate for open syntax too. -/
def sentenceCondition (order : Program) (AE : List Nat × List Nat)
    (φ : Syntax) (cutoff : Nat) : Bool :=
  Formula.isClosedCode (φ.code RecordedHead.code) && condition order AE φ cutoff

theorem sentenceCondition_primrec :
    Primrec (fun p : ((Program × (List Nat × List Nat)) × Syntax) × Nat =>
      sentenceCondition p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.and.comp
    (Formula.isClosedCode_primrec.comp (code_primrec.comp (Primrec.snd.comp Primrec.fst)))
    condition_primrec

theorem sentenceCondition_correct (order : Program) (AE : List Nat × List Nat) (φ : Syntax) :
    (∃ cutoff, sentenceCondition order AE φ cutoff = true) ↔
      φ.Closed ∧
        (letI : LT Nat := Program.orderLT order
         φ.RecordedAdmissible AE.1.toFinset AE.2.toFinset) := by
  simp only [sentenceCondition, Bool.and_eq_true, exists_and_left, condition_correct,
    RecordedPrefixProgram.recorded_closed_code]

abbrev Parameters := (List Nat × List Nat) × Program

def defaultParameters : Parameters := (([], []), Nat.Partrec.Code.zero)

def decodeParameters (n : Nat) : Parameters :=
  (Encodable.decode (α := Parameters) n).getD defaultParameters

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

@[simp] theorem decodeParameters_encode (p : Parameters) :
    decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

/-- The exact recorded-code test rejects invalid raw trees independently of
    all default values used by the finite tree folds. -/
def check (key query cutoff : Nat) : Bool :=
  let p := decodeParameters key
  isCode query && conditionCode p.2 p.1 query cutoff

theorem check_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Nat × Nat) × Nat => decodeParameters p.1.1) :=
    decodeParameters_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.and.comp (isCode_primrec.comp hq)
    (conditionCode_primrec.comp
      ((((Primrec.snd.comp hp).pair (Primrec.fst.comp hp)).pair hq).pair Primrec.snd))

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun cutoff => Part.some (check key query cutoff))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ cutoff, check key query cutoff = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (p : Parameters) (φ : Syntax) :
    (evaluation (Encodable.encode p) (φ.code RecordedHead.code)).Dom ↔
      letI : LT Nat := Program.orderLT p.2
      φ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset := by
  rw [evaluation_domain]
  have hsyntax : isCode (φ.code RecordedHead.code) = true :=
    (isCode_iff _).mpr ⟨φ, rfl⟩
  simp only [check, decodeParameters_encode, hsyntax, Bool.true_and]
  exact condition_correct p.2 p.1 φ

theorem evaluation_only_formulas (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
      (letI : LT Nat := Program.orderLT (decodeParameters key).2
       φ.RecordedAdmissible (decodeParameters key).1.1.toFinset
         (decodeParameters key).1.2.toFinset) := by
  obtain ⟨k, hk⟩ := (evaluation_domain key query).mp h
  have hh := Bool.and_eq_true_iff.mp hk
  obtain ⟨φ, hφ⟩ := (isCode_iff query).mp hh.1
  have hcondition : condition (decodeParameters key).2 (decodeParameters key).1 φ k = true := by
    simpa only [condition, hφ] using hh.2
  exact ⟨φ, hφ.symm,
    (condition_correct (decodeParameters key).2 (decodeParameters key).1 φ).mp ⟨k, hcondition⟩⟩

/-- Uniform recognition of the existing admissibility predicate with the
    supplied Program's literal order relation. Raw accepted codes are exactly
    typed admissible formulas; neither statement requires closedness. -/
theorem compiler_exists :
    ∃ compiler : Parameters → Program, Primrec compiler ∧
      (∀ p (φ : Syntax), (compiler p).domain (φ.code RecordedHead.code) ↔
        letI : LT Nat := Program.orderLT p.2
        φ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset) ∧
      (∀ p query, (compiler p).domain query ↔
        ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
          (letI : LT Nat := Program.orderLT p.2
           φ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset)) := by
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
      have hf := evaluation_only_formulas _ _ h
      rw [decodeParameters_encode] at hf
      exact hf
    · rintro ⟨φ, rfl, hφ⟩
      exact (evaluation_correct p φ).mpr hφ

end OrderedRecordedAdmissionProgram
end Alexander313
