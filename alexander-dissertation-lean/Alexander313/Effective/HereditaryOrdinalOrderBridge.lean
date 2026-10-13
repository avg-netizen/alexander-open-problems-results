import Alexander313.Effective.HereditaryOrdinalFormation
import Alexander313.Effective.RecordedOrderedSeedPrograms

/-!
# Actual hereditary order in the complete recorded compiler route

The existing seed, indexed-prefix and finite-consequence compilers are
instantiated with the genuine executing hereditary union-order Program.
A constructed positive Program filter keeps exactly outputs whose whole
literal label support belongs to the original union domain. This is an
explicit domain restriction of the existing coded generator/proof predicates.
For seed and admission outputs, the formation theorem supplies genuine
ordinal admissibility of their literal relabelings.

The displayed source, hierarchy, original Valid and edge Programs remain
the existing inputs. No ordinal edge algorithm, bounded room existence,
relabeled theory conservativity, truth or full-stage soundness is concluded.
-/

noncomputable section

namespace Alexander313.HereditaryOrdinalOrderBridge

open RecordedFormula HereditaryOrdinalFormation
open RecordedBackgroundProgram (positive positive_primrec positive_iff)

/-- The existing whole compiler data, with the actual union order fixed. -/
abbrev Parameters := RecordedSeedProgram.Parameters

def orderedData (p : Parameters) : OrderedRecordedSeedProgram.Parameters :=
  (p, ordinalOrder)

theorem orderedData_primrec : Primrec orderedData :=
  Primrec.id.pair (Primrec.const ordinalOrder)

def outputLabelCheck (query : Nat) : Bool := labelCheckCode query.unpair.2

theorem outputLabelCheck_primrec : Primrec outputLabelCheck :=
  labelCheckCode_primrec.comp (Primrec.snd.comp Primrec.unpair)

@[simp] theorem outputLabelCheck_code (a : Nat) (φ : Syntax) :
    outputLabelCheck (Nat.pair a (φ.code RecordedHead.code)) = true ↔ Supported φ := by
  simpa only [outputLabelCheck, Nat.unpair_pair, labelCheck] using labelCheck_exact φ

def filterRunCheck (c : Program) (query cutoff : Nat) : Bool :=
  positive cutoff c query && outputLabelCheck query

theorem filterRunCheck_primrec :
    Primrec (fun p : (Program × Nat) × Nat => filterRunCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp
    (positive_primrec.comp
      ((Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)))
    (outputLabelCheck_primrec.comp (Primrec.snd.comp Primrec.fst))

def filterEvaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun cutoff => Part.some
    (filterRunCheck ((Encodable.decode (α := Program) key).getD Nat.Partrec.Code.zero) query cutoff))

theorem filterEvaluation_partrec : Partrec₂ filterEvaluation := by
  have hd : Primrec (fun p : (Nat × Nat) × Nat =>
      (Encodable.decode (α := Program) p.1.1).getD Nat.Partrec.Code.zero) :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const Nat.Partrec.Code.zero)
  have h : Primrec (fun p : (Nat × Nat) × Nat =>
      filterRunCheck ((Encodable.decode (α := Program) p.1.1).getD Nat.Partrec.Code.zero)
        p.1.2 p.2) :=
    filterRunCheck_primrec.comp ((hd.pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact (Partrec.rfind h.to_comp.partrec.to₂).to₂

theorem filterEvaluation_exact (c : Program) (query : Nat) :
    (filterEvaluation (Encodable.encode c) query).Dom ↔
      c.domain query ∧ outputLabelCheck query = true := by
  calc
    (filterEvaluation (Encodable.encode c) query).Dom ↔
        ∃ cutoff, positive cutoff c query = true ∧ outputLabelCheck query = true := by
      simp only [filterEvaluation, Encodable.encodek, Option.getD_some,
        Nat.rfind_dom, Part.mem_some_iff, Part.some_dom, implies_true, and_true,
        Bool.true_eq, filterRunCheck, Bool.and_eq_true]
    _ ↔ (∃ cutoff, positive cutoff c query = true) ∧ outputLabelCheck query = true :=
      exists_and_right
    _ ↔ c.domain query ∧ outputLabelCheck query = true :=
      and_congr (positive_iff c query) Iff.rfl

/-- Executing intersection with the literal whole-label test. Its domain
equation holds on all raw queries, independently of their shape or source. -/
theorem filterCompiler_exists :
    ∃ filter : Program → Program, Primrec filter ∧ ∀ c query,
      (filter c).domain query ↔ c.domain query ∧ outputLabelCheck query = true := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr filterEvaluation_partrec)
  let filter : Program → Program := fun c => Nat.Partrec.Code.curry kernel (Encodable.encode c)
  have heval (c : Program) (query : Nat) :
      (filter c).eval query = filterEvaluation (Encodable.encode c) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨filter, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_⟩
  intro c query
  change ((filter c).eval query).Dom ↔ _
  rw [heval]
  exact filterEvaluation_exact c query

def seed (p : Parameters) (a : Nat) (φ : Syntax) : Prop :=
  OrderedRecordedSeedProgram.seed (orderedData p) a φ ∧ Supported φ

def admissions (p : Parameters) (a : Nat) (φ : Syntax) : Prop :=
  OrderedRecordedSeedProgram.admissions (orderedData p) a φ ∧ Supported φ

theorem seed_ordinal_admissible {p : Parameters} {a : Nat} {φ : Syntax}
    (h : seed p a φ) :
    (denotation φ).RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset :=
  (admissible_exact p.1.1 φ h.2).mp (OrderedRecordedSeedProgram.seed_admissible h.1)

theorem seed_compiler_exists :
    ∃ compiler : Parameters → Program, Primrec compiler ∧
      (∀ p a φ, (compiler p).domain (Nat.pair a (φ.code RecordedHead.code)) ↔ seed p a φ) ∧
      (∀ p query, (compiler p).domain query → ∃ a, ∃ φ : Syntax,
        query = Nat.pair a (φ.code RecordedHead.code) ∧ φ.Closed ∧ Supported φ ∧
          (denotation φ).RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset) := by
  obtain ⟨seeds, hs, exactSeed, rawSeed⟩ := OrderedRecordedSeedProgram.seed_compiler_exists
  obtain ⟨filter, hf, exactFilter⟩ := filterCompiler_exists
  refine ⟨fun p => filter (seeds (orderedData p)), hf.comp (hs.comp orderedData_primrec), ?_, ?_⟩
  · intro p a φ
    exact (exactFilter _ _).trans
      (and_congr (exactSeed (orderedData p) a φ) (outputLabelCheck_code a φ))
  · intro p query h
    obtain ⟨hseed, hlabels⟩ := (exactFilter _ query).mp h
    obtain ⟨a, φ, heq, hclosed, hadm⟩ := rawSeed (orderedData p) query hseed
    have hφ : Supported φ := by simpa only [heq, outputLabelCheck_code] using hlabels
    exact ⟨a, φ, heq, hclosed, hφ, (admissible_exact p.1.1 φ hφ).mp hadm⟩

theorem admission_compiler_exists :
    ∃ compiler : Parameters → Program, Primrec compiler ∧
      (∀ p a φ, (compiler p).domain (Nat.pair a (φ.code RecordedHead.code)) ↔ admissions p a φ) ∧
      (∀ p query, (compiler p).domain query → ∃ a, ∃ φ : Syntax,
        query = Nat.pair a (φ.code RecordedHead.code) ∧ φ.Closed ∧ Supported φ ∧
          (denotation φ).RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset) := by
  obtain ⟨generators, hg, exactGen, rawGen⟩ := OrderedRecordedSeedProgram.admission_compiler_exists
  obtain ⟨filter, hf, exactFilter⟩ := filterCompiler_exists
  refine ⟨fun p => filter (generators (orderedData p)),
    hf.comp (hg.comp orderedData_primrec), ?_, ?_⟩
  · intro p a φ
    exact (exactFilter _ _).trans
      (and_congr (exactGen (orderedData p) a φ) (outputLabelCheck_code a φ))
  · intro p query h
    obtain ⟨hgen, hlabels⟩ := (exactFilter _ query).mp h
    obtain ⟨a, φ, heq, hclosed, hadm⟩ := rawGen (orderedData p) query hgen
    have hφ : Supported φ := by simpa only [heq, outputLabelCheck_code] using hlabels
    exact ⟨a, φ, heq, hclosed, hφ, (admissible_exact p.1.1 φ hφ).mp hadm⟩

theorem admissions_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (p : Parameters) (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (φ : Syntax) :
    admissions p a φ ↔
      (letI : LT Nat := Program.orderLT ordinalOrder
       FullRecordedAdmissions C p.1.1.1.toFinset p.1.1.2.toFinset a
         (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) φ) ∧ Supported φ :=
  and_congr (OrderedRecordedSeedProgram.admissions_exact C (orderedData p)
    hArithmetic hsource hhierarchy hvalid a φ) Iff.rfl

/-- The consequence compiler is filtered only on the final query support.
Its target is the original coded consequence relation under the true Program
order, not a newly asserted relabeling equivalence for ordinal theories. -/
theorem theory_compiler_exists :
    ∃ compiler : Parameters → Program, Primrec compiler ∧
      (∀ {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters),
        C.arithmetic = canonicalArithmeticCoding Nat →
        C.family.effective.recognizes = p.1.2.1.1 →
        (∀ j i, p.1.2.1.2.domain (Nat.pair j i) ↔ R j i) →
        (∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ) → ∀ a φ,
          (compiler p).domain (Nat.pair a (φ.code RecordedHead.code)) ↔
            (letI : LT Nat := Program.orderLT ordinalOrder
             φ.Closed ∧ Provable
               (FullRecordedAdmissions C p.1.1.1.toFinset p.1.1.2.toFinset a
                 (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
                 (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν))) φ) ∧ Supported φ) ∧
      (∀ p query, (compiler p).domain query → ∃ a, ∃ φ : Syntax,
        query = Nat.pair a (φ.code RecordedHead.code) ∧ φ.Closed ∧ Supported φ) := by
  obtain ⟨theories, ht, exactTheory, rawTheory⟩ := OrderedRecordedSeedProgram.theory_compiler_exists
  obtain ⟨filter, hf, exactFilter⟩ := filterCompiler_exists
  refine ⟨fun p => filter (theories (orderedData p)),
    hf.comp (ht.comp orderedData_primrec), ?_, ?_⟩
  · intro R C p hArithmetic hsource hhierarchy hvalid a φ
    rw [exactFilter, outputLabelCheck_code]
    exact and_congr (exactTheory C (orderedData p)
      hArithmetic hsource hhierarchy hvalid a φ) Iff.rfl
  · intro p query h
    obtain ⟨hproof, hlabels⟩ := (exactFilter _ query).mp h
    obtain ⟨a, φ, heq, hclosed⟩ := rawTheory (orderedData p) query hproof
    exact ⟨a, φ, heq, hclosed, by simpa only [heq, outputLabelCheck_code] using hlabels⟩

end Alexander313.HereditaryOrdinalOrderBridge
