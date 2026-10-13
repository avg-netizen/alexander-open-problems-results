import Alexander313.Effective.CanonicalFormation
import Alexander313.Alexander.SourceLabelFormation
import Alexander313.SourceColumns

/-!
# Actual uniform programs for the subordinate particular-code generators

The relation is supplied by an ordinary edge program. Acceptance checks
one finite edge-computation witness, the exact unary-syntax predicate and
literal equality with the compiled particular-code sentence. There is no
negative relation test, semantic validity test or consequence oracle.

The candidate joint source program is effective data passed to the already
constructed unary-column compiler. A fixed-point source theory still needs
the remaining background and finite consequence enumeration programs.
-/

namespace Alexander313

noncomputable def compiledUnaryColumnCode (c : Program) (j body input : Nat) : Nat :=
  Encodable.encode (unaryColumnCompiler (((c, j), body), input))

theorem compiledUnaryColumnCode_primrec : Primrec (fun p : InstanceParameters =>
    compiledUnaryColumnCode p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.encode.comp unaryColumnCompiler_primrec

@[simp] theorem compiledUnaryColumnCode_family (F : MachineFamily) (j : Nat)
    (φ : UnaryFormula Nat) :
    compiledUnaryColumnCode F.effective.recognizes j (φ.body.code id) φ.input =
      F.unaryColumnIndex j φ := rfl

def SubordinateCodeGenerator (c edge : Program) (i : Nat) (σ : Formula Nat) : Prop :=
  ∃ j, ∃ φ : UnaryFormula Nat, edge.domain (Nat.pair j i) ∧
    σ = codeSentence (canonicalArithmeticCoding Nat) j φ
      (compiledUnaryColumnCode c j (φ.body.code id) φ.input)

noncomputable def subordinateCheck (key query witness : Nat) : Bool :=
  let c := Nat.Partrec.Code.ofNatCode key.unpair.1
  let edge := Nat.Partrec.Code.ofNatCode key.unpair.2
  let j := witness.unpair.1
  let body := witness.unpair.2.unpair.1
  let input := witness.unpair.2.unpair.2.unpair.1
  let cutoff := witness.unpair.2.unpair.2.unpair.2
  Formula.isUnaryCode input body &&
    ((Nat.Partrec.Code.evaln cutoff edge (Nat.pair j query.unpair.1)).isSome &&
      (query.unpair.2 == particularCodeSentenceCode j body input
        (compiledUnaryColumnCode c j body input)))

theorem subordinateCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    subordinateCheck p.1.1 p.1.2 p.2) := by
  have hkey : Primrec (fun p : (Nat × Nat) × Nat => p.1.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)
  have hc := (Primrec.ofNat Program).comp (Primrec.fst.comp hkey)
  have hedge := (Primrec.ofNat Program).comp (Primrec.snd.comp hkey)
  have hquery : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hi := Primrec.fst.comp hquery
  have hσ := Primrec.snd.comp hquery
  have hw : Primrec (fun p : (Nat × Nat) × Nat => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hj := Primrec.fst.comp hw
  have hrest := Primrec.unpair.comp (Primrec.snd.comp hw)
  have hbody := Primrec.fst.comp hrest
  have htail := Primrec.unpair.comp (Primrec.snd.comp hrest)
  have hx := Primrec.fst.comp htail
  have hk := Primrec.snd.comp htail
  have hcolumn := compiledUnaryColumnCode_primrec.comp (((hc.pair hj).pair hbody).pair hx)
  have hsentence := particularCodeSentenceCode_primrec.comp
    (((hj.pair hbody).pair hx).pair hcolumn)
  have heval := Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hedge).pair
    (Primrec₂.natPair.comp hj hi))
  exact Primrec.and.comp (Formula.isUnaryCode_primrec.comp hx hbody)
    (Primrec.and.comp (Primrec.option_isSome.comp heval) (Primrec.beq.comp hσ hsentence))

noncomputable def subordinateEvaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (subordinateCheck key query witness))

theorem subordinateEvaluation_partrec : Partrec₂ subordinateEvaluation :=
  (Partrec.rfind subordinateCheck_primrec.to_comp.partrec.to₂).to₂

theorem subordinateEvaluation_domain (key query : Nat) :
    (subordinateEvaluation key query).Dom ↔ ∃ witness, subordinateCheck key query witness = true := by
  simp only [subordinateEvaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem subordinateEvaluation_correct (c edge : Program) (i : Nat) (σ : Formula Nat) :
    (subordinateEvaluation (Nat.pair (Encodable.encode c) (Encodable.encode edge))
      (Nat.pair i (σ.code id))).Dom ↔ SubordinateCodeGenerator c edge i σ := by
  rw [subordinateEvaluation_domain]
  have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c := Denumerable.ofNat_encode c
  have he : Nat.Partrec.Code.ofNatCode (Encodable.encode edge) = edge := Denumerable.ofNat_encode edge
  constructor
  · rintro ⟨w, hw⟩
    let j := w.unpair.1
    let body := w.unpair.2.unpair.1
    let input := w.unpair.2.unpair.2.unpair.1
    let cutoff := w.unpair.2.unpair.2.unpair.2
    have hcheck : Formula.isUnaryCode input body = true ∧
        (Nat.Partrec.Code.evaln cutoff edge (Nat.pair j i)).isSome = true ∧
        σ.code id = particularCodeSentenceCode j body input (compiledUnaryColumnCode c j body input) := by
      simpa only [subordinateCheck, Nat.unpair_pair, hc, he, Bool.and_eq_true, beq_iff_eq] using hw
    obtain ⟨φ, hφ, hfree⟩ := (Formula.isUnaryCode_iff input body).mp hcheck.1
    let unary : UnaryFormula Nat := ⟨φ, input, hfree⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcheck.2.1
    have hdomain : edge.domain (Nat.pair j i) :=
      (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1
    refine ⟨j, unary, hdomain, ?_⟩
    apply Formula.code_injective id Function.injective_id
    have hs := hcheck.2.2
    rw [← hφ, particularCodeSentenceCode_eq j unary] at hs
    exact hs
  · rintro ⟨j, φ, hdomain, rfl⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdomain
    obtain ⟨cutoff, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    have hsyntax := (Formula.isUnaryCode_code φ.input φ.body).mpr φ.freeVars_exact
    refine ⟨Nat.pair j (Nat.pair (φ.body.code id) (Nat.pair φ.input cutoff)), ?_⟩
    simp only [subordinateCheck, Nat.unpair_pair, hc, he, hsyntax, Bool.true_and,
      Option.mem_def.mp hk, Option.isSome_some, particularCodeSentenceCode_eq, beq_self_eq_true]

theorem subordinateEvaluation_only_sentences (key query : Nat)
    (h : (subordinateEvaluation key query).Dom) :
    ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed := by
  obtain ⟨w, hw⟩ := (subordinateEvaluation_domain key query).mp h
  let c := Nat.Partrec.Code.ofNatCode key.unpair.1
  let j := w.unpair.1
  let body := w.unpair.2.unpair.1
  let input := w.unpair.2.unpair.2.unpair.1
  have hsyntax : Formula.isUnaryCode input body = true := (Bool.and_eq_true_iff.mp hw).1
  have hsentence : query.unpair.2 = particularCodeSentenceCode j body input
      (compiledUnaryColumnCode c j body input) := by
    exact (beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).2).2)
  obtain ⟨φ, hφ, hfree⟩ := (Formula.isUnaryCode_iff input body).mp hsyntax
  let unary : UnaryFormula Nat := ⟨φ, input, hfree⟩
  let σ := codeSentence (canonicalArithmeticCoding Nat) j unary
    (compiledUnaryColumnCode c j (φ.code id) input)
  have hcode : query.unpair.2 = σ.code id := by
    rw [← hφ, particularCodeSentenceCode_eq j unary] at hsentence
    exact hsentence
  refine ⟨query.unpair.1, σ, ?_, codeSentence_closed _ _ _ _⟩
  rw [← hcode]
  exact (Nat.pair_unpair query).symm

theorem subordinateCompiler_exists :
    ∃ compiler : Program × Program → Program, Primrec compiler ∧
      ∀ p query, (compiler p).eval query = subordinateEvaluation
        (Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)) query := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr subordinateEvaluation_partrec)
  have hkey : Primrec (fun p : Program × Program =>
      Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)) :=
    Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
  refine ⟨fun p => Nat.Partrec.Code.curry kernel
      (Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)),
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) hkey, ?_⟩
  intro p query
  rw [Nat.Partrec.Code.eval_curry, hkernel]
  simp only [Nat.unpaired, Nat.unpair_pair]

theorem subordinate_generator_programs :
    ∃ compiler : Program × Program → Program, Primrec compiler ∧
      ∀ c edge i σ, (compiler (c, edge)).domain (Nat.pair i (σ.code id)) ↔
        SubordinateCodeGenerator c edge i σ := by
  obtain ⟨compiler, hp, heval⟩ := subordinateCompiler_exists
  refine ⟨compiler, hp, ?_⟩
  intro c edge i σ
  change ((compiler (c, edge)).eval _).Dom ↔ _
  rw [heval]
  exact subordinateEvaluation_correct c edge i σ

theorem subordinate_generators_exact {R : Nat → Nat → Prop}
    (F : MachineFamily) (edge : Program)
    (hedge : ∀ j i, edge.domain (Nat.pair j i) ↔ R j i) (i : Nat) (σ : Formula Nat) :
    SubordinateCodeGenerator F.effective.recognizes edge i σ ↔
      ∃ j, ∃ φ : UnaryFormula Nat, R j i ∧
        σ = codeSentence (canonicalArithmeticCoding Nat) j φ (F.unaryColumnIndex j φ) := by
  simp only [SubordinateCodeGenerator, hedge, compiledUnaryColumnCode_family]

theorem SubordinateCodeGenerator.closed {c edge : Program} {i : Nat} {σ : Formula Nat}
    (h : SubordinateCodeGenerator c edge i σ) : σ.Closed := by
  obtain ⟨j, φ, hedge, rfl⟩ := h
  exact codeSentence_closed _ _ _ _

end Alexander313
