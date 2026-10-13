import Alexander313.Effective.GeneratorPrograms
import Alexander313.Effective.FiniteAssignments

/-!
# Actual program images for known and assigned validity branches

The input is an ordinary partial program on literal formula codes. A finite
positive computation of that program is transformed into either a universally
closed knowledge formula or an arbitrary numeral instance. This constructs
the executable image compiler without deciding semantic validity.

Only `background_exact` identifies the input program's domain with `Valid`,
and that theorem displays this as a hypothesis. No such complete validity
program or effective Alexander consequence enumerator is constructed here.
-/

namespace Alexander313
namespace ValidityImage

abbrev Witness := (Bool × Formula Nat) × List Nat

def formula (i : Nat) (w : Witness) : Formula Nat :=
  cond w.1.1 (Formula.universalClosure (.know i w.1.2)) (FiniteAssignment.close w.1.2 w.2)

theorem formula_primrec : Primrec₂ formula := by
  have hw : Primrec (fun p : Nat × Witness => p.2) := Primrec.snd
  have hkind := Primrec.fst.comp (Primrec.fst.comp hw)
  have hφ := Primrec.snd.comp (Primrec.fst.comp hw)
  have hL := Primrec.snd.comp hw
  have hknown := Formula.universalClosure_primrec.comp
    (Formula.know_primrec.comp Primrec.fst hφ)
  exact (hkind.cond hknown (FiniteAssignment.close_primrec.comp hφ hL)).to₂

theorem formula_closed (i : Nat) (w : Witness) : (formula i w).Closed := by
  cases h : w.1.1 <;> simp only [formula, h, Bool.cond_false, Bool.cond_true]
  · exact FiniteAssignment.close_closed _ _
  · exact Formula.universalClosure_closed _

def image (c : Program) (i : Nat) (σ : Formula Nat) : Prop :=
  ∃ φ : Formula Nat, c.domain (φ.code id) ∧
    (σ = Formula.universalClosure (.know i φ) ∨ ∃ s : Assignment, σ = φ.close s)

theorem image_iff_witness (c : Program) (i : Nat) (σ : Formula Nat) :
    image c i σ ↔ ∃ w : Witness, c.domain (w.1.2.code id) ∧ σ = formula i w := by
  constructor
  · rintro ⟨φ, hd, heq | ⟨s, heq⟩⟩
    · exact ⟨((true, φ), []), hd, heq⟩
    · obtain ⟨L, hL⟩ := FiniteAssignment.represents φ s
      exact ⟨((false, φ), L), hd, heq.trans hL⟩
  · rintro ⟨w, hd, rfl⟩
    refine ⟨w.1.2, hd, ?_⟩
    cases h : w.1.1
    · exact Or.inr ⟨FiniteAssignment.assignment w.2,
        by simp only [formula, h, Bool.cond_false, FiniteAssignment.close_eq]⟩
    · exact Or.inl (by simp only [formula, h, Bool.cond_true])

theorem image_closed {c : Program} {i : Nat} {σ : Formula Nat} (h : image c i σ) : σ.Closed := by
  obtain ⟨w, _, rfl⟩ := (image_iff_witness c i σ).mp h
  exact formula_closed _ _

noncomputable def decodeWitness (n : Nat) : Witness :=
  (Encodable.decode (α := Witness) n).getD ((false, .falsum), [])

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (((false, .falsum), []) : Witness))

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]

noncomputable def check (e query certificate : Nat) : Bool :=
  let w := decodeWitness certificate.unpair.1
  (Nat.Partrec.Code.evaln certificate.unpair.2 (Nat.Partrec.Code.ofNatCode e) (w.1.2.code id)).isSome &&
    (query.unpair.2 == (formula query.unpair.1 w).code id)

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    check p.1.1 p.1.2 p.2) := by
  have hc : Primrec (fun p : (Nat × Nat) × Nat => Nat.Partrec.Code.ofNatCode p.1.1) :=
    (Primrec.ofNat Program).comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hi := Primrec.fst.comp hq
  have hσ := Primrec.snd.comp hq
  have ht : Primrec (fun p : (Nat × Nat) × Nat => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hw := decodeWitness_primrec.comp (Primrec.fst.comp ht)
  have hk := Primrec.snd.comp ht
  have hbody := Formula.code_primrec.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have heval := Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hc).pair hbody)
  have hformula := Formula.code_primrec.comp (formula_primrec.comp hi hw)
  exact Primrec.and.comp (Primrec.option_isSome.comp heval) (Primrec.beq.comp hσ hformula)

noncomputable def evaluation (e query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check e query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (e query : Nat) :
    (evaluation e query).Dom ↔ ∃ certificate, check e query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (c : Program) (i : Nat) (σ : Formula Nat) :
    (evaluation (Encodable.encode c) (Nat.pair i (σ.code id))).Dom ↔ image c i σ := by
  rw [evaluation_domain, image_iff_witness]
  have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c := Denumerable.ofNat_encode c
  constructor
  · rintro ⟨t, ht⟩
    let w := decodeWitness t.unpair.1
    have hcheck : (Nat.Partrec.Code.evaln t.unpair.2 c (w.1.2.code id)).isSome = true ∧
        σ.code id = (formula i w).code id := by
      simpa only [check, Nat.unpair_pair, hc, Bool.and_eq_true, beq_iff_eq] using ht
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcheck.1
    refine ⟨w, (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1,
      Formula.code_injective id Function.injective_id hcheck.2⟩
  · rintro ⟨w, hd, rfl⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨cutoff, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨Nat.pair (Encodable.encode w) cutoff, ?_⟩
    simp only [check, Nat.unpair_pair, hc, decodeWitness_encode,
      Option.mem_def.mp hk, Option.isSome_some, Bool.true_and, beq_self_eq_true]

theorem evaluation_only_sentences (e query : Nat) (h : (evaluation e query).Dom) :
    ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed := by
  obtain ⟨t, ht⟩ := (evaluation_domain e query).mp h
  let w := decodeWitness t.unpair.1
  let σ := formula query.unpair.1 w
  have hcode : query.unpair.2 = σ.code id := beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
  refine ⟨query.unpair.1, σ, ?_, formula_closed _ _⟩
  rw [← hcode]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists :
    ∃ compiler : Program → Program, Primrec compiler ∧
      (∀ c i σ, (compiler c).domain (Nat.pair i (σ.code id)) ↔ image c i σ) ∧
      (∀ c query, (compiler c).domain query →
        ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Program → Program := fun c => Nat.Partrec.Code.curry kernel (Encodable.encode c)
  have heval (c : Program) (query : Nat) :
      (compiler c).eval query = evaluation (Encodable.encode c) query := by
    change (Nat.Partrec.Code.curry kernel (Encodable.encode c)).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler,
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_, ?_⟩
  · intro c i σ
    change ((compiler c).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct c i σ
  · intro c query h
    change ((compiler c).eval query).Dom at h
    rw [heval] at h
    exact evaluation_only_sentences _ _ h

/-- The hypothesis here is precisely the unresolved complete validity
program. The executable image construction above does not assume it. -/
theorem background_exact (validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ)
    (i : Nat) (σ : Formula Nat) :
    (SyntacticBackground.admits i σ ∨ image validity i σ) ↔ BackgroundGenerator i σ := by
  constructor
  · rintro (h | ⟨φ, hv, hknown | ⟨s, hclose⟩⟩)
    · exact SyntacticBackground.admits_background h
    · rw [hknown]
      exact .structural (.validity φ ((hvalid φ).mp hv))
    · rw [hclose]
      exact .assigned φ s ((hvalid φ).mp hv)
  · intro h
    cases h with
    | arithmetic h => exact Or.inl (Or.inl h)
    | assigned φ s hv => exact Or.inr ⟨φ, (hvalid φ).mpr hv, Or.inr ⟨s, rfl⟩⟩
    | structural h =>
      cases h with
      | validity φ hv => exact Or.inr ⟨φ, (hvalid φ).mpr hv, Or.inl rfl⟩
      | reasoning φ ψ => exact Or.inl (Or.inr (Or.inl ⟨φ, ψ, rfl⟩))
      | introspection φ => exact Or.inl (Or.inr (Or.inr (Or.inl ⟨φ, rfl⟩)))
    | reflection j φ => exact Or.inl (Or.inr (Or.inr (Or.inr ⟨j, φ, rfl⟩)))

end ValidityImage

def ProgramSourceGenerator (source edge validity : Program) (i : Nat) (σ : Formula Nat) : Prop :=
  SyntacticSourceGenerator source edge i σ ∨ ValidityImage.image validity i σ

theorem ProgramSourceGenerator.closed {source edge validity : Program} {i : Nat} {σ : Formula Nat}
    (h : ProgramSourceGenerator source edge validity i σ) : σ.Closed := by
  rcases h with h | h
  · exact h.closed
  · exact ValidityImage.image_closed h

theorem programSourceGenerator_exact (source edge validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ) (i : Nat) (σ : Formula Nat) :
    ProgramSourceGenerator source edge validity i σ ↔
      BackgroundGenerator i σ ∨ SubordinateCodeGenerator source edge i σ := by
  have hb := ValidityImage.background_exact validity hvalid i σ
  unfold ProgramSourceGenerator SyntacticSourceGenerator
  tauto

/-- A real uniform program-data transform for every positive source branch
and every own prefix. Identifying `validity` with all semantic validity still
requires constructing the exact program displayed in `background_exact`. -/
theorem positiveSourceCompiler_exists :
    ∃ compiler : (Program × Program) × Program → Program, Primrec compiler ∧
      (∀ source edge validity i σ,
        (compiler ((source, edge), validity)).domain (Nat.pair i (σ.code id)) ↔
          PrefixedAxioms i (ProgramSourceGenerator source edge validity i) σ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed) ∧
      (∀ source edge validity i σ,
        (compiler ((source, edge), validity)).domain (Nat.pair i (σ.code id)) →
        (compiler ((source, edge), validity)).domain (Nat.pair i ((Formula.know i σ).code id))) := by
  obtain ⟨schemas, hschemas, _⟩ := SyntacticBackground.program_exists
  obtain ⟨subordinate, hsubPR, hsub⟩ := subordinate_generator_programs
  obtain ⟨images, himagePR, himages, _⟩ := ValidityImage.compiler_exists
  obtain ⟨union, hunionPR, hunion⟩ := Program.finiteUnionCompiler_exists
  obtain ⟨prefixes, hprefixPR, hprefix, hsentences⟩ := PrefixAdmission.compiler_exists
  let base : (Program × Program) × Program → Program :=
    fun p => union [schemas, subordinate p.1, images p.2]
  have hlist : Primrec (fun p : (Program × Program) × Program =>
      [schemas, subordinate p.1, images p.2]) :=
    Primrec.list_cons.comp (Primrec.const schemas)
      (Primrec.list_cons.comp (hsubPR.comp Primrec.fst)
        (Primrec.list_cons.comp (himagePR.comp Primrec.snd) (Primrec.const [])))
  have hbasePR : Primrec base := hunionPR.comp hlist
  have hbase (source edge validity : Program) (i : Nat) (σ : Formula Nat) :
      (base ((source, edge), validity)).domain (Nat.pair i (σ.code id)) ↔
        ProgramSourceGenerator source edge validity i σ := by
    change (union [schemas, subordinate (source, edge), images validity]).domain
      (Nat.pair i (σ.code id)) ↔ _
    rw [hunion]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨d, rfl | rfl | rfl, hd⟩
      · exact Or.inl (Or.inl ((hschemas i σ).mp hd))
      · exact Or.inl (Or.inr ((hsub source edge i σ).mp hd))
      · exact Or.inr ((himages validity i σ).mp hd)
    · rintro ((hs | hs) | hi)
      · exact ⟨schemas, Or.inl rfl, (hschemas i σ).mpr hs⟩
      · exact ⟨subordinate (source, edge), Or.inr (Or.inl rfl),
          (hsub source edge i σ).mpr hs⟩
      · exact ⟨images validity, Or.inr (Or.inr rfl), (himages validity i σ).mpr hi⟩
  refine ⟨fun p => prefixes (base p), hprefixPR.comp hbasePR, ?_, ?_, ?_⟩
  · intro source edge validity i σ
    exact (hprefix _ i σ).trans (PrefixAdmission.generated_iff_prefixed
      (hbase source edge validity) (fun _ _ h => h.closed) i σ)
  · intro p query h
    exact hsentences (base p) query h
  · intro source edge validity i σ h
    exact (hprefix _ i _).mpr (PrefixAdmission.generated_known ((hprefix _ i σ).mp h))

end Alexander313
