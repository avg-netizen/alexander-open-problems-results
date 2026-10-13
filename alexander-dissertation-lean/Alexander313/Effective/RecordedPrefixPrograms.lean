import Alexander313.Effective.RecordedBackgroundPrograms
import Alexander313.RecordedPrefixClosure

/-!
# Actual positive indexed own-prefix compiler

An executing base generator Program is transformed uniformly into its literal
admissible indexed-prefix closure. Certificates carry an actual base formula,
a finite prefix-label list and a positive base computation. Whole output
admissibility tests every prefix bound. Raw accepted queries are closed,
admissible recorded syntax even for arbitrary supplied base Programs.

Exact semantic identification is proved for both existing recorded tables.
The background instance is fully composed here; the complete-table instance
still requires an actual guarded-main/base Program. Nat labels use ordinary
order, not an assumed Wilken coding or pure-relation decision procedure.
-/

noncomputable section

namespace Alexander313
namespace RecordedPrefixProgram

open RecordedFormula

abbrev Parameters := (List Nat × List Nat) × Program
abbrev Witness := List Nat × Syntax

def formula (a : Nat) (w : Witness) : Syntax := «prefix» a w.1 w.2

theorem formula_primrec : Primrec₂ formula :=
  (prefix_primrec.comp ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd))).to₂

theorem recorded_closed_code (φ : Syntax) :
    Formula.isClosedCode (φ.code RecordedHead.code) = true ↔ φ.Closed := by
  rw [← encode_code, Formula.isClosedCode_code]
  simp only [encode, Formula.Closed, Formula.freeVars_mapOwner]

def side (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  w.2.Closed ∧ (formula a w).RecordedAdmissible p.1.1.toFinset p.1.2.toFinset ∧
    p.2.domain (Nat.pair a (w.2.code RecordedHead.code))

def admits (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w : Witness, side p a w ∧ σ = formula a w

theorem admits_closed {p : Parameters} {a : Nat} {σ : Syntax}
    (h : admits p a σ) : σ.Closed := by
  obtain ⟨w, hs, rfl⟩ := h
  exact prefix_closed a w.1 w.2 hs.1

theorem admits_admissible {p : Parameters} {a : Nat} {σ : Syntax}
    (h : admits p a σ) : σ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset := by
  obtain ⟨w, hs, rfl⟩ := h
  exact hs.2.1

/-- The computed image is exactly the actual rule-generated closure. The
    displayed semantic base-domain premise identifies ordinary Program data;
    it is not supplied as a checker-effectivity or closure assumption. -/
theorem closure_exact (p : Parameters) (base : Nat → Syntax → Prop)
    (exactBase : ∀ a φ, p.2.domain (Nat.pair a (φ.code RecordedHead.code)) ↔ base a φ)
    (closedBase : ∀ a φ, base a φ → φ.Closed)
    (admissibleBase : ∀ a φ, base a φ → φ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset)
    (a : Nat) (σ : Syntax) :
    admits p a σ ↔ RecordedPrefixClosure p.1.1.toFinset a (base a) σ := by
  constructor
  · rintro ⟨w, hs, rfl⟩
    exact RecordedPrefixClosure.of_list p.1.2.toFinset w.1 w.2
      ((exactBase a w.2).mp hs.2.2) hs.2.1
  · intro h
    obtain ⟨θ, L, ht, rfl, hadm⟩ := h.exists_list p.1.2.toFinset (admissibleBase a)
    exact ⟨(L, θ), ⟨closedBase a θ ht, hadm, (exactBase a θ).mpr ht⟩, rfl⟩

def condition (p : Parameters) (a : Nat) (w : Witness) (cutoff : Nat) : Bool :=
  Formula.isClosedCode (w.2.code RecordedHead.code) &&
    (admissibleCode p.1 ((formula a w).code RecordedHead.code) &&
      RecordedBackgroundProgram.positive cutoff p.2 (Nat.pair a (w.2.code RecordedHead.code)))

theorem condition_primrec : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) =>
    condition p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hb := code_primrec.comp (Primrec.snd.comp hw)
  have ho := code_primrec.comp (formula_primrec.comp ha hw)
  exact Primrec.and.comp (Formula.isClosedCode_primrec.comp hb)
    (Primrec.and.comp (admissibleCode_primrec.comp (Primrec.fst.comp hp) ho)
      (RecordedBackgroundProgram.positive_primrec.comp
        ((hk.pair (Primrec.snd.comp hp)).pair (Primrec₂.natPair.comp ha hb))))

theorem condition_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ cutoff, condition p a w cutoff = true) ↔ side p a w := by
  simp only [condition, Bool.and_eq_true, recorded_closed_code, admissibleCode_code,
    exists_and_left, RecordedBackgroundProgram.positive_iff, side]

def defaultWitness : Witness := ([], .falsum)
def defaultParameters : Parameters := (([], []), Nat.Partrec.Code.zero)
def decodeWitness (n : Nat) : Witness := (Encodable.decode (α := Witness) n).getD defaultWitness
def decodeParameters (n : Nat) : Parameters := (Encodable.decode (α := Parameters) n).getD defaultParameters

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultWitness)

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]

@[simp] theorem decodeParameters_encode (p : Parameters) : decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

def check (key query certificate : Nat) : Bool :=
  let p := decodeParameters key
  let w := decodeWitness certificate.unpair.1
  condition p query.unpair.1 w certificate.unpair.2 &&
    (query.unpair.2 == (formula query.unpair.1 w).code RecordedHead.code)

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Nat × Nat) × Nat => decodeParameters p.1.1) := decodeParameters_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) := Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have ha := Primrec.fst.comp hq
  have hσ := Primrec.snd.comp hq
  have hc : Primrec (fun p : (Nat × Nat) × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hw := decodeWitness_primrec.comp (Primrec.fst.comp hc)
  have hk := Primrec.snd.comp hc
  exact Primrec.and.comp (condition_primrec.comp ((hp.pair ha).pair (hw.pair hk)))
    (Primrec.beq.comp hσ (code_primrec.comp (formula_primrec.comp ha hw)))

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ certificate, check key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (p : Parameters) (a : Nat) (σ : Syntax) :
    (evaluation (Encodable.encode p) (Nat.pair a (σ.code RecordedHead.code))).Dom ↔ admits p a σ := by
  rw [evaluation_domain]
  constructor
  · rintro ⟨t, ht⟩
    let w := decodeWitness t.unpair.1
    have hc : condition p a w t.unpair.2 = true ∧
        σ.code RecordedHead.code = (formula a w).code RecordedHead.code := by
      simpa only [check, Nat.unpair_pair, decodeParameters_encode, Bool.and_eq_true, beq_iff_eq] using ht
    exact ⟨w, (condition_correct p a w).mp ⟨_, hc.1⟩,
      Formula.code_injective RecordedHead.code RecordedHead.code_injective hc.2⟩
  · rintro ⟨w, hs, rfl⟩
    obtain ⟨cutoff, hc⟩ := (condition_correct p a w).mpr hs
    exact ⟨Nat.pair (Encodable.encode w) cutoff, by simp [check, hc]⟩

theorem evaluation_only_sentences (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ a, ∃ σ : Syntax, query = Nat.pair a (σ.code RecordedHead.code) ∧
      σ.Closed ∧ σ.RecordedAdmissible (decodeParameters key).1.1.toFinset (decodeParameters key).1.2.toFinset := by
  obtain ⟨t, ht⟩ := (evaluation_domain key query).mp h
  let w := decodeWitness t.unpair.1
  let σ := formula query.unpair.1 w
  have hc : query.unpair.2 = σ.code RecordedHead.code := beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
  have hs : side (decodeParameters key) query.unpair.1 w :=
    (condition_correct _ _ _).mp ⟨_, (Bool.and_eq_true_iff.mp ht).1⟩
  refine ⟨query.unpair.1, σ, ?_, prefix_closed _ _ _ hs.1, hs.2.1⟩
  rw [← hc]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admits p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        σ.RecordedAdmissible p.1.1.toFinset p.1.2.toFinset) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Parameters → Program := fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : Parameters) (query : Nat) : (compiler p).eval query =
      evaluation (Encodable.encode p) query := by
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

/-- Compose the two actual compilers. The only remaining semantic input here
    is exactness of the executing validity/contextual-edge programs. -/
theorem background_compiler_exists :
    ∃ compiler : RecordedBackgroundProgram.Parameters → Program, Primrec compiler ∧
      (∀ p R, (∀ μ ν, p.1.2.domain (Nat.pair μ ν) ↔ R μ ν) →
        (∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ) → ∀ a σ,
        (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
          RecordedAdmissions p.1.1.1.toFinset p.1.1.2.toFinset a R σ) ∧
      (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
        query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
          σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset) := by
  obtain ⟨background, hbg, exactBg, _⟩ := RecordedBackgroundProgram.compiler_exists
  obtain ⟨prefixes, hpr, exactPr, rawPr⟩ := compiler_exists
  let parameters := fun p : RecordedBackgroundProgram.Parameters => (p.1.1, background p)
  let compiler := fun p : RecordedBackgroundProgram.Parameters => prefixes (parameters p)
  have hp : Primrec parameters := (Primrec.fst.comp Primrec.fst).pair hbg
  refine ⟨compiler, hpr.comp hp, ?_, ?_⟩
  · intro p R hedge hvalid a σ
    rw [show (compiler p).domain _ ↔ admits (parameters p) a σ from exactPr _ _ _]
    exact (closure_exact (parameters p)
      (fun b θ => RecordedBackground p.1.1.1.toFinset p.1.1.2.toFinset b R θ)
      (fun b θ => (exactBg p b θ).trans (RecordedBackgroundProgram.background_exact p R hedge hvalid b θ))
      (fun _ _ h => h.closed) (fun _ _ h => h.admissible) a σ).trans
        (RecordedAdmissions.iff_prefixClosure _ _ a R σ).symm
  · intro p query h
    exact rawPr (parameters p) query h

/-- The same actual compiler closes a complete background/main seed Program
    under precisely the full table's indexed-prefix rule. Construction of that
    seed Program, especially its guarded main rows, is still required. -/
theorem full_compiler_exists {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : List Nat) (R₁ R₂ : Nat → Nat → Prop) (seed : Program)
    (exactSeed : ∀ a φ, seed.domain (Nat.pair a (φ.code RecordedHead.code)) ↔
      RecordedBackground A.toFinset E.toFinset a R₁ φ ∨
        RecordedMain C A.toFinset E.toFinset a R₁ R₂ φ) :
    ∃ program : Program,
      (∀ a σ, program.domain (Nat.pair a (σ.code RecordedHead.code)) ↔
        FullRecordedAdmissions C A.toFinset E.toFinset a R₁ R₂ σ) ∧
      (∀ query, program.domain query → ∃ a, ∃ σ : Syntax,
        query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
          σ.RecordedAdmissible A.toFinset E.toFinset) := by
  obtain ⟨compiler, _, exactCompiler, rawCompiler⟩ := compiler_exists
  let p : Parameters := ((A, E), seed)
  refine ⟨compiler p, ?_, rawCompiler p⟩
  intro a σ
  exact (exactCompiler p a σ).trans
    ((closure_exact p
      (fun b θ => RecordedBackground A.toFinset E.toFinset b R₁ θ ∨
        RecordedMain C A.toFinset E.toFinset b R₁ R₂ θ)
      exactSeed (fun _ _ h => h.elim (fun h => h.closed) (fun h => h.closed))
      (fun _ _ h => h.elim (fun h => h.admissible) (fun h => h.admissible)) a σ).trans
        (FullRecordedAdmissions.iff_prefixClosure C A.toFinset E.toFinset a R₁ R₂ σ).symm)

end RecordedPrefixProgram
end Alexander313
