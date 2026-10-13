import Alexander313.Effective.ValidityImages
import Alexander313.CommonCoreAssembly

/-!
# Actual common-core generator programs

The extra branches check literal freshness and unary syntax, use the one
already chosen `unaryColumnCompiler`, and check positive finite computations
of the supplied edge program. The full generator compiler combines these
branches with the constructed syntactic background and validity-program
images. Semantic identification with the source presentation uses explicit
exactness of the edge and validity programs; neither is decided semantically.
-/

namespace Alexander313

namespace Formula

theorem ex_primrec : Primrec₂ (Formula.ex : Nat → Formula Nat → Formula Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code, EncodedSyntax.binary, EncodedSyntax.node] using
    (EncodedSyntax.binary_primrec 7).comp Primrec.fst (code_primrec.comp Primrec.snd)

theorem iff_primrec : Primrec₂ (Formula.iff : Formula Nat → Formula Nat → Formula Nat) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, EncodedSyntax.equivalence_code] using
    EncodedSyntax.equivalence_primrec.comp (code_primrec.comp Primrec.fst)
      (code_primrec.comp Primrec.snd)

end Formula

namespace CommonCoreProgram

abbrev Witness := ((Nat × Nat) × Nat) × Formula Nat

def particularSentence (j x e : Nat) (φ : Formula Nat) : Formula Nat :=
  .all x (.iff (.know j φ) ((canonicalArithmeticCoding Nat).member (.numeral e) (.var x)))

@[simp] theorem particularSentence_unary (j e : Nat) (φ : UnaryFormula Nat) :
    particularSentence j φ.input e φ.body = codeSentence (canonicalArithmeticCoding Nat) j φ e := rfl

theorem particularSentence_primrec : Primrec (fun p : ((Nat × Nat) × Nat) × Formula Nat =>
    particularSentence p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hj : Primrec (fun p : Witness => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : Witness => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec (fun p : Witness => p.1.2) := Primrec.snd.comp Primrec.fst
  have hbody : Primrec (fun p : Witness => p.2) := Primrec.snd
  have hmember := canonicalArithmeticCoding_member_primrec.comp
    (Term.numeral_primrec.comp he) (Term.var_primrec.comp hx)
  exact Formula.all_primrec.comp hx
    (Formula.iff_primrec.comp (Formula.know_primrec.comp hj hbody) hmember)

theorem parameterMechanicalSentence_primrec :
    Primrec (fun p : Witness => parameterMechanicalSentence (canonicalArithmeticCoding Nat)
      p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hj : Primrec (fun p : Witness => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : Witness => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec (fun p : Witness => p.1.2) := Primrec.snd.comp Primrec.fst
  have hφ : Primrec (fun p : Witness => p.2) := Primrec.snd
  have hmember := canonicalArithmeticCoding_member_primrec.comp
    (Term.var_primrec.comp he) (Term.var_primrec.comp hx)
  have hbody := Formula.iff_primrec.comp (Formula.know_primrec.comp hj hφ) hmember
  exact Formula.universalClosure_primrec.comp
    (Formula.ex_primrec.comp he (Formula.all_primrec.comp hx hbody))

/-- Tags zero and one select parameter mechanicalness and the fixed core
column code; every other tag selects a shifted subordinate code. -/
noncomputable def formula (source : Program) (tag : Nat) (w : Witness) : Formula Nat :=
  if tag = 0 then
    parameterMechanicalSentence (canonicalArithmeticCoding Nat) (w.1.1.1 + 1) w.1.1.2 w.1.2 w.2
  else if tag = 1 then
    particularSentence 0 w.1.1.2 (compiledUnaryColumnCode source 0 (w.2.code id) w.1.1.2) w.2
  else
    particularSentence (w.1.1.1 + 1) w.1.1.2
      (compiledUnaryColumnCode source (w.1.1.1 + 1) (w.2.code id) w.1.1.2) w.2

theorem formula_primrec : Primrec (fun p : (Program × Nat) × Witness =>
    formula p.1.1 p.1.2 p.2) := by
  have hc : Primrec (fun p : (Program × Nat) × Witness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have htag : Primrec (fun p : (Program × Nat) × Witness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Program × Nat) × Witness => p.2) := Primrec.snd
  have hj := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp hw))
  have hx := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp hw))
  have he := Primrec.snd.comp (Primrec.fst.comp hw)
  have hφ := Primrec.snd.comp hw
  have hnext := Primrec.succ.comp hj
  have hcode := Formula.code_primrec.comp hφ
  have hmechanical := parameterMechanicalSentence_primrec.comp
    (((hnext.pair hx).pair he).pair hφ)
  have hcoreIndex := compiledUnaryColumnCode_primrec.comp
    (((hc.pair (Primrec.const 0)).pair hcode).pair hx)
  have hsubIndex := compiledUnaryColumnCode_primrec.comp (((hc.pair hnext).pair hcode).pair hx)
  have hcore := particularSentence_primrec.comp
    ((((Primrec.const 0).pair hx).pair hcoreIndex).pair hφ)
  have hsub := particularSentence_primrec.comp (((hnext.pair hx).pair hsubIndex).pair hφ)
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hmechanical
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hcore hsub)

def sideCondition (edge : Program) (tag owner : Nat) (w : Witness) : Prop :=
  if tag = 0 then owner = 0 ∧ w.1.2 ∉ w.2.freeVars ∧ w.1.2 ≠ w.1.1.2
  else if tag = 1 then owner ≠ 0 ∧ w.2.freeVars = {w.1.1.2}
  else owner ≠ 0 ∧ w.2.freeVars = {w.1.1.2} ∧
    edge.domain (Nat.pair w.1.1.1 (owner - 1))

def condition (edge : Program) (tag owner : Nat) (w : Witness) (cutoff : Nat) : Bool :=
  if tag = 0 then decide (owner = 0 ∧ w.1.2 ∉ w.2.freeVars ∧ w.1.2 ≠ w.1.1.2)
  else if tag = 1 then decide (owner ≠ 0 ∧ w.2.freeVars = {w.1.1.2})
  else decide (owner ≠ 0 ∧ w.2.freeVars = {w.1.1.2}) &&
    (Nat.Partrec.Code.evaln cutoff edge (Nat.pair w.1.1.1 (owner - 1))).isSome

theorem condition_primrec : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) =>
    condition p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htag : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ho : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hj := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp hw))
  have hx := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp hw))
  have he := Primrec.snd.comp (Primrec.fst.comp hw)
  have hφ := Primrec.snd.comp hw
  have hzero := Primrec.eq.comp ho (Primrec.const 0)
  have hmem : PrimrecPred (fun p : ((Program × Nat) × Nat) × (Witness × Nat) =>
      p.2.1.1.2 ∈ p.2.1.2.freeVars) :=
    (Primrec.eq.comp (Formula.freeMemCode_primrec.comp he (Formula.code_primrec.comp hφ))
      (Primrec.const true)).of_eq (fun p => by simp only [Formula.freeMemCode_code, decide_eq_true_eq])
  have hdistinct := (Primrec.eq.comp he hx).not
  have hunary := Formula.unary_primrec.comp hφ hx
  have hmechanical := (hzero.and (hmem.not.and hdistinct)).decide
  have hcode := (hzero.not.and hunary).decide
  have hinput := Primrec₂.natPair.comp hj (Primrec.nat_sub.comp ho (Primrec.const 1))
  have heval := Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hc).pair hinput)
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hmechanical
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hcode
      (Primrec.and.comp hcode (Primrec.option_isSome.comp heval)))

theorem condition_correct (edge : Program) (tag owner : Nat) (w : Witness) :
    (∃ cutoff, condition edge tag owner w cutoff = true) ↔ sideCondition edge tag owner w := by
  by_cases hzero : tag = 0
  · simp [condition, sideCondition, hzero]
  · by_cases hone : tag = 1
    · simp [condition, sideCondition, hzero, hone]
    · have heval : (∃ cutoff,
          (Nat.Partrec.Code.evaln cutoff edge (Nat.pair w.1.1.1 (owner - 1))).isSome = true) ↔
          edge.domain (Nat.pair w.1.1.1 (owner - 1)) := by
        constructor
        · rintro ⟨cutoff, h⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
          exact (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1
        · intro h
          obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
          obtain ⟨cutoff, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
          exact ⟨cutoff, Option.isSome_iff_exists.mpr ⟨v, Option.mem_def.mp hk⟩⟩
      simp only [condition, sideCondition, if_neg hzero, if_neg hone,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨cutoff, h, hk⟩
        exact ⟨h.1, h.2, heval.mp ⟨cutoff, hk⟩⟩
      · rintro ⟨ho, hf, hd⟩
        obtain ⟨cutoff, hk⟩ := heval.mpr hd
        exact ⟨cutoff, ⟨ho, hf⟩, hk⟩

def admits (source edge : Program) (owner : Nat) (σ : Formula Nat) : Prop :=
  ∃ tag, ∃ w : Witness, sideCondition edge tag owner w ∧ σ = formula source tag w

theorem admits_closed {source edge : Program} {owner : Nat} {σ : Formula Nat}
    (h : admits source edge owner σ) : σ.Closed := by
  obtain ⟨tag, w, hs, rfl⟩ := h
  by_cases hzero : tag = 0
  · rw [formula, if_pos hzero]
    exact Formula.universalClosure_closed _
  · by_cases hone : tag = 1
    · have hf : w.2.freeVars = {w.1.1.2} := by
        have h := hs
        simp only [sideCondition, if_neg hzero, if_pos hone] at h
        exact h.2
      let φ : UnaryFormula Nat := ⟨w.2, w.1.1.2, hf⟩
      rw [formula, if_neg hzero, if_pos hone]
      exact codeSentence_closed (canonicalArithmeticCoding Nat) 0 φ _
    · have hf : w.2.freeVars = {w.1.1.2} := by
        have h := hs
        simp only [sideCondition, if_neg hzero, if_neg hone] at h
        exact h.2.1
      let φ : UnaryFormula Nat := ⟨w.2, w.1.1.2, hf⟩
      rw [formula, if_neg hzero, if_neg hone]
      exact codeSentence_closed (canonicalArithmeticCoding Nat) (w.1.1.1 + 1) φ _

noncomputable def decodeWitness (n : Nat) : Witness :=
  (Encodable.decode (α := Witness) n).getD (((0, 0), 0), .falsum)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ((((0, 0), 0), .falsum) : Witness))

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]

noncomputable def check (key query certificate : Nat) : Bool :=
  let source := Nat.Partrec.Code.ofNatCode key.unpair.1
  let edge := Nat.Partrec.Code.ofNatCode key.unpair.2
  let tag := certificate.unpair.1
  let w := decodeWitness certificate.unpair.2.unpair.1
  let cutoff := certificate.unpair.2.unpair.2
  condition edge tag query.unpair.1 w cutoff &&
    (query.unpair.2 == (formula source tag w).code id)

set_option maxHeartbeats 1000000 in
private theorem check_primrec_of_formation
    (form : Program → Nat → Witness → Formula Nat)
    (hform : Primrec (fun p : (Program × Nat) × Witness => form p.1.1 p.1.2 p.2))
    (cond : Program → Nat → Nat → Witness → Nat → Bool)
    (hcond : Primrec (fun p : ((Program × Nat) × Nat) × (Witness × Nat) =>
      cond p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)) :
    Primrec (fun p : (Nat × Nat) × Nat =>
      cond (Nat.Partrec.Code.ofNatCode p.1.1.unpair.2) p.2.unpair.1 p.1.2.unpair.1
        (decodeWitness p.2.unpair.2.unpair.1) p.2.unpair.2.unpair.2 &&
      (p.1.2.unpair.2 == (form (Nat.Partrec.Code.ofNatCode p.1.1.unpair.1) p.2.unpair.1
        (decodeWitness p.2.unpair.2.unpair.1)).code id)) := by
  have hkey : Primrec (fun p : (Nat × Nat) × Nat => p.1.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)
  have hsource := (Primrec.ofNat Program).comp (Primrec.fst.comp hkey)
  have hedge := (Primrec.ofNat Program).comp (Primrec.snd.comp hkey)
  have hquery : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have howner := Primrec.fst.comp hquery
  have hσ := Primrec.snd.comp hquery
  have ht : Primrec (fun p : (Nat × Nat) × Nat => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have htag := Primrec.fst.comp ht
  have hrest := Primrec.unpair.comp (Primrec.snd.comp ht)
  have hw := decodeWitness_primrec.comp (Primrec.fst.comp hrest)
  have hk := Primrec.snd.comp hrest
  have hcondition := hcond.comp (((hedge.pair htag).pair howner).pair (hw.pair hk))
  have hformula := Formula.code_primrec.comp (hform.comp ((hsource.pair htag).pair hw))
  have result := Primrec.and.comp hcondition (Primrec.beq.comp hσ hformula)
  exact result.of_eq (fun _ => by simp only [Nat.Partrec.Code.ofNatCode_eq])

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) :=
  check_primrec_of_formation formula formula_primrec condition condition_primrec

noncomputable def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ certificate, check key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (source edge : Program) (owner : Nat) (σ : Formula Nat) :
    (evaluation (Nat.pair (Encodable.encode source) (Encodable.encode edge))
      (Nat.pair owner (σ.code id))).Dom ↔ admits source edge owner σ := by
  rw [evaluation_domain]
  have hs : Nat.Partrec.Code.ofNatCode (Encodable.encode source) = source := Denumerable.ofNat_encode source
  have he : Nat.Partrec.Code.ofNatCode (Encodable.encode edge) = edge := Denumerable.ofNat_encode edge
  constructor
  · rintro ⟨t, ht⟩
    let tag := t.unpair.1
    let w := decodeWitness t.unpair.2.unpair.1
    have hcheck : condition edge tag owner w t.unpair.2.unpair.2 = true ∧
        σ.code id = (formula source tag w).code id := by
      simpa only [check, Nat.unpair_pair, hs, he, Bool.and_eq_true, beq_iff_eq] using ht
    exact ⟨tag, w, (condition_correct edge tag owner w).mp ⟨_, hcheck.1⟩,
      Formula.code_injective id Function.injective_id hcheck.2⟩
  · rintro ⟨tag, w, hside, rfl⟩
    obtain ⟨cutoff, hk⟩ := (condition_correct edge tag owner w).mpr hside
    refine ⟨Nat.pair tag (Nat.pair (Encodable.encode w) cutoff), ?_⟩
    simp only [check, Nat.unpair_pair, hs, he, decodeWitness_encode, hk,
      Bool.true_and, beq_self_eq_true]

theorem evaluation_only_sentences (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ owner, ∃ σ : Formula Nat, query = Nat.pair owner (σ.code id) ∧ σ.Closed := by
  obtain ⟨t, ht⟩ := (evaluation_domain key query).mp h
  let source := Nat.Partrec.Code.ofNatCode key.unpair.1
  let edge := Nat.Partrec.Code.ofNatCode key.unpair.2
  let tag := t.unpair.1
  let w := decodeWitness t.unpair.2.unpair.1
  let σ := formula source tag w
  have hside : sideCondition edge tag query.unpair.1 w :=
    (condition_correct edge tag query.unpair.1 w).mp ⟨_, (Bool.and_eq_true_iff.mp ht).1⟩
  have hcode : query.unpair.2 = σ.code id := beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
  refine ⟨query.unpair.1, σ, ?_, admits_closed ⟨tag, w, hside, rfl⟩⟩
  rw [← hcode]
  exact (Nat.pair_unpair query).symm

theorem extraCompiler_exists :
    ∃ compiler : Program × Program → Program, Primrec compiler ∧
      (∀ source edge owner σ, (compiler (source, edge)).domain (Nat.pair owner (σ.code id)) ↔
        admits source edge owner σ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ owner, ∃ σ : Formula Nat, query = Nat.pair owner (σ.code id) ∧ σ.Closed) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Program × Program → Program := fun p => Nat.Partrec.Code.curry kernel
    (Nat.pair (Encodable.encode p.1) (Encodable.encode p.2))
  have heval (p : Program × Program) (query : Nat) : (compiler p).eval query =
      evaluation (Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  have hkey : Primrec (fun p : Program × Program =>
      Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)) :=
    Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) hkey, ?_, ?_⟩
  · intro source edge owner σ
    change ((compiler (source, edge)).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct source edge owner σ
  · intro p query h
    change ((compiler p).eval query).Dom at h
    rw [heval] at h
    exact evaluation_only_sentences _ _ h

end CommonCoreProgram

def CommonCoreProgramGenerator (source edge validity : Program) (i : Nat) (σ : Formula Nat) : Prop :=
  SyntacticBackground.admits i σ ∨ ValidityImage.image validity i σ ∨
    CommonCoreProgram.admits source edge i σ

theorem CommonCoreProgramGenerator.closed {source edge validity : Program} {i : Nat} {σ : Formula Nat}
    (h : CommonCoreProgramGenerator source edge validity i σ) : σ.Closed := by
  rcases h with h | h | h
  · exact SyntacticBackground.admits_closed h
  · exact ValidityImage.image_closed h
  · exact CommonCoreProgram.admits_closed h

/-- Identification with the literal source table uses no family soundness
or closure property. The program identities and semantic validity exactness
are displayed separately from the actual numerical compiler. -/
theorem commonCoreProgramGenerator_exact {R : Nat → Nat → Prop}
    (F : MachineFamily) (source edge validity : Program)
    (hsource : F.effective.recognizes = source)
    (hedge : ∀ j i, edge.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ)
    (owner : Nat) (σ : Formula Nat) :
    CommonCoreProgramGenerator source edge validity owner σ ↔
      CommonCoreGenerator R (canonicalArithmeticCoding Nat) F owner σ := by
  have hcolumn (j : Nat) (φ : UnaryFormula Nat) :
      compiledUnaryColumnCode source j (φ.body.code id) φ.input = F.unaryColumnIndex j φ := by
    rw [← hsource]
    exact compiledUnaryColumnCode_family F j φ
  constructor
  · rintro (h | h | ⟨tag, w, hs, rfl⟩)
    · exact .background owner (SyntacticBackground.admits_background h)
    · exact .background owner ((ValidityImage.background_exact validity hvalid owner σ).mp (Or.inr h))
    · by_cases hzero : tag = 0
      · have h := hs
        simp only [CommonCoreProgram.sideCondition, if_pos hzero] at h
        rw [CommonCoreProgram.formula, if_pos hzero, h.1]
        exact .core_mechanical w.1.1.1 w.1.1.2 w.1.2 w.2 h.2.1 h.2.2
      · by_cases hone : tag = 1
        · have h := hs
          simp only [CommonCoreProgram.sideCondition, if_neg hzero, if_pos hone] at h
          have howner : owner = (owner - 1) + 1 := by omega
          let φ : UnaryFormula Nat := ⟨w.2, w.1.1.2, h.2⟩
          rw [CommonCoreProgram.formula, if_neg hzero, if_pos hone]
          change CommonCoreGenerator R (canonicalArithmeticCoding Nat) F owner
            (codeSentence (canonicalArithmeticCoding Nat) 0 φ
              (compiledUnaryColumnCode source 0 (φ.body.code id) φ.input))
          rw [hcolumn, howner]
          exact .core_code (owner - 1) φ
        · have h := hs
          simp only [CommonCoreProgram.sideCondition, if_neg hzero, if_neg hone] at h
          have howner : owner = (owner - 1) + 1 := by omega
          let φ : UnaryFormula Nat := ⟨w.2, w.1.1.2, h.2.1⟩
          rw [CommonCoreProgram.formula, if_neg hzero, if_neg hone]
          change CommonCoreGenerator R (canonicalArithmeticCoding Nat) F owner
            (codeSentence (canonicalArithmeticCoding Nat) (w.1.1.1 + 1) φ
              (compiledUnaryColumnCode source (w.1.1.1 + 1) (φ.body.code id) φ.input))
          rw [hcolumn, howner]
          exact .subordinate_code (owner - 1) w.1.1.1 ((hedge _ _).mp h.2.2) φ
  · intro h
    cases h with
    | background _ h =>
      rcases (ValidityImage.background_exact validity hvalid owner σ).mpr h with hs | hv
      · exact Or.inl hs
      · exact Or.inr (Or.inl hv)
    | core_mechanical j x e φ fresh distinct =>
      refine Or.inr (Or.inr ⟨0, (((j, x), e), φ), ?_, rfl⟩)
      simp only [CommonCoreProgram.sideCondition, if_pos rfl]
      exact ⟨trivial, fresh, distinct⟩
    | core_code i φ =>
      refine Or.inr (Or.inr ⟨1, (((0, φ.input), 0), φ.body), ?_, ?_⟩)
      · simp only [CommonCoreProgram.sideCondition, show (1 : Nat) ≠ 0 by decide,
          if_false, if_true]
        exact ⟨by omega, φ.freeVars_exact⟩
      · change codeSentence (canonicalArithmeticCoding Nat) 0 φ (F.unaryColumnIndex 0 φ) =
          CommonCoreProgram.particularSentence 0 φ.input
            (compiledUnaryColumnCode source 0 (φ.body.code id) φ.input) φ.body
        rw [CommonCoreProgram.particularSentence_unary, hcolumn]
    | subordinate_code i j below φ =>
      refine Or.inr (Or.inr ⟨2, (((j, φ.input), 0), φ.body), ?_, ?_⟩)
      · simp only [CommonCoreProgram.sideCondition, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide, if_false, Nat.add_sub_cancel]
        exact ⟨by omega, φ.freeVars_exact, (hedge j i).mpr below⟩
      · change codeSentence (canonicalArithmeticCoding Nat) (j + 1) φ (F.unaryColumnIndex (j + 1) φ) =
          CommonCoreProgram.particularSentence (j + 1) φ.input
            (compiledUnaryColumnCode source (j + 1) (φ.body.code id) φ.input) φ.body
        rw [CommonCoreProgram.particularSentence_unary, hcolumn]

theorem commonCoreGeneratorCompiler_exists :
    ∃ compiler : (Program × Program) × Program → Program, Primrec compiler ∧
      (∀ source edge validity i σ,
        (compiler ((source, edge), validity)).domain (Nat.pair i (σ.code id)) ↔
          CommonCoreProgramGenerator source edge validity i σ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed) := by
  obtain ⟨schemas, hschemas, hschemasClosed⟩ := SyntacticBackground.program_exists
  obtain ⟨images, himagePR, himages, himagesClosed⟩ := ValidityImage.compiler_exists
  obtain ⟨extras, hextraPR, hextras, hextrasClosed⟩ := CommonCoreProgram.extraCompiler_exists
  obtain ⟨union, hunionPR, hunion⟩ := Program.finiteUnionCompiler_exists
  let table : (Program × Program) × Program → List Program :=
    fun p => [schemas, images p.2, extras p.1]
  have htable : Primrec table :=
    Primrec.list_cons.comp (Primrec.const schemas)
      (Primrec.list_cons.comp (himagePR.comp Primrec.snd)
        (Primrec.list_cons.comp (hextraPR.comp Primrec.fst) (Primrec.const [])))
  refine ⟨fun p => union (table p), hunionPR.comp htable, ?_, ?_⟩
  · intro source edge validity i σ
    rw [hunion]
    change (∃ d ∈ [schemas, images validity, extras (source, edge)],
      d.domain (Nat.pair i (σ.code id))) ↔ _
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨d, rfl | rfl | rfl, hd⟩
      · exact Or.inl ((hschemas i σ).mp hd)
      · exact Or.inr (Or.inl ((himages validity i σ).mp hd))
      · exact Or.inr (Or.inr ((hextras source edge i σ).mp hd))
    · rintro (hs | hi | he)
      · exact ⟨schemas, Or.inl rfl, (hschemas i σ).mpr hs⟩
      · exact ⟨images validity, Or.inr (Or.inl rfl), (himages validity i σ).mpr hi⟩
      · exact ⟨extras (source, edge), Or.inr (Or.inr rfl), (hextras source edge i σ).mpr he⟩
  · intro p query h
    obtain ⟨d, hd, ht⟩ := (hunion (table p) query).mp h
    change d ∈ [schemas, images p.2, extras p.1] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact hschemasClosed query ht
    · exact himagesClosed p.2 query ht
    · exact hextrasClosed p.1 query ht

theorem commonCorePrefixCompiler_exists :
    ∃ compiler : (Program × Program) × Program → Program, Primrec compiler ∧
      (∀ source edge validity i σ,
        (compiler ((source, edge), validity)).domain (Nat.pair i (σ.code id)) ↔
          PrefixedAxioms i (CommonCoreProgramGenerator source edge validity i) σ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed) ∧
      (∀ source edge validity i σ,
        (compiler ((source, edge), validity)).domain (Nat.pair i (σ.code id)) →
        (compiler ((source, edge), validity)).domain (Nat.pair i ((Formula.know i σ).code id))) := by
  obtain ⟨base, hbasePR, hbase, _⟩ := commonCoreGeneratorCompiler_exists
  obtain ⟨prefixes, hprefixPR, hprefix, hsentences⟩ := PrefixAdmission.compiler_exists
  refine ⟨fun p => prefixes (base p), hprefixPR.comp hbasePR, ?_, ?_, ?_⟩
  · intro source edge validity i σ
    exact (hprefix _ i σ).trans (PrefixAdmission.generated_iff_prefixed
      (hbase source edge validity) (fun _ _ h => h.closed) i σ)
  · intro p query h
    exact hsentences (base p) query h
  · intro source edge validity i σ h
    exact (hprefix _ i _).mpr (PrefixAdmission.generated_known ((hprefix _ i σ).mp h))

end Alexander313
