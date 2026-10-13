import Alexander313.Effective.RecordedPrefixPrograms
import Alexander313.ConsequencePrograms

/-!
# Actual finite-certificate consequence enumeration in recorded syntax

Every numerical certificate names literal recorded formulas and independent
positive computations for their actual generator admissions. The exact recorded
implication chain is queried through the injective owner encoding, which has
proved validity equivalence; no validity converse for source erasure is used.
The compiler itself is uniform in executing generator/validity Programs.
Semantic consequence identification still requires the unconstructed exact
Valid Program. Raw accepted queries are closed recorded formulas; logical
consequences need not themselves be globally stratified generator instances.
-/

namespace Alexander313
namespace RecordedFormula

theorem chain_primrec : Primrec₂ (Formula.chain (Owner := Head)) := by
  have step : Primrec₂ (fun (_ : List Syntax × Syntax)
      (p : Syntax × Syntax) => Formula.imp p.1 p.2) :=
    (imp_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have hf := Primrec.list_foldr Primrec.fst Primrec.snd step
  have heq (Γ : List Syntax) (φ : Syntax) :
      Γ.foldr Formula.imp φ = Formula.chain Γ φ := by
    induction Γ with
    | nil => rfl
    | cons θ Γ ih => simp only [List.foldr_cons, Formula.chain, ih]
  exact hf.to₂.of_eq heq

end RecordedFormula

namespace RecordedConsequenceProgram

open RecordedFormula

def axioms (source : Program) (i : Nat) (φ : Syntax) : Prop :=
  φ.Closed ∧ source.domain (Nat.pair i (φ.code RecordedHead.code))

def generated (source validity : Program) (i : Nat) (φ : Syntax) : Prop :=
  φ.Closed ∧ ∃ Γ : List (Syntax),
    (∀ θ ∈ Γ, axioms source i θ) ∧ validity.domain ((Formula.chain Γ φ).code RecordedHead.code)

def premiseAt (source : Program) (i : Nat) (p : Syntax × Nat) : Bool :=
  Formula.isClosedCode (p.1.code RecordedHead.code) &&
    (Nat.Partrec.Code.evaln p.2 source (Nat.pair i (p.1.code RecordedHead.code))).isSome

theorem premiseAt_primrec :
    Primrec (fun p : (Program × Nat) × (Syntax × Nat) =>
      premiseAt p.1.1 p.1.2 p.2) := by
  have hsource : Primrec (fun p : (Program × Nat) × (Syntax × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : (Program × Nat) × (Syntax × Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hφ : Primrec (fun p : (Program × Nat) × (Syntax × Nat) => p.2.1.code RecordedHead.code) := RecordedFormula.code_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hk : Primrec (fun p : (Program × Nat) × (Syntax × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have heval := Nat.Partrec.Code.primrec_evaln.comp
    ((hk.pair hsource).pair (Primrec₂.natPair.comp hi hφ))
  exact Primrec.and.comp (Formula.isClosedCode_primrec.comp hφ)
    (Primrec.option_isSome.comp heval)

def premisesAt (source : Program) (i : Nat) (L : List (Syntax × Nat)) : Bool :=
  L.foldr (fun p previous => premiseAt source i p && previous) true

theorem premisesAt_primrec :
    Primrec (fun p : (Program × Nat) × List (Syntax × Nat) =>
      premisesAt p.1.1 p.1.2 p.2) := by
  have step : Primrec₂ (fun (p : (Program × Nat) × List (Syntax × Nat))
      (s : (Syntax × Nat) × Bool) => premiseAt p.1.1 p.1.2 s.1 && s.2) :=
    (Primrec.and.comp
      (premiseAt_primrec.comp
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) step

theorem premisesAt_iff (source : Program) (i : Nat) (L : List (Syntax × Nat)) :
    premisesAt source i L = true ↔ ∀ p ∈ L, premiseAt source i p = true := by
  induction L with
  | nil => simp [premisesAt]
  | cons p L ih =>
    simp only [premisesAt, List.foldr_cons, Bool.and_eq_true, List.forall_mem_cons]
    exact and_congr Iff.rfl ih

theorem premiseAt_sound (source : Program) (i : Nat) (p : Syntax × Nat)
    (h : premiseAt source i p = true) : axioms source i p.1 := by
  have hs := Bool.and_eq_true_iff.mp h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs.2
  exact ⟨(RecordedPrefixProgram.recorded_closed_code p.1).mp hs.1,
    (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1⟩

theorem premiseAt_complete (source : Program) (i : Nat) (φ : Syntax)
    (h : axioms source i φ) : ∃ k, premiseAt source i (φ, k) = true := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h.2
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  refine ⟨k, ?_⟩
  simp only [premiseAt, (RecordedPrefixProgram.recorded_closed_code φ).mpr h.1, Bool.true_and,
    Option.mem_def.mp hk, Option.isSome_some]

/-- Decorate each actual premise independently. This avoids assuming a common
    proof-depth or computation bound for different numerical source proofs. -/
theorem decorate (source : Program) (i : Nat) (Γ : List (Syntax))
    (admitted : ∀ θ ∈ Γ, axioms source i θ) :
    ∃ L : List (Syntax × Nat), L.map Prod.fst = Γ ∧ premisesAt source i L = true := by
  revert admitted
  induction Γ with
  | nil => intro _; exact ⟨[], rfl, rfl⟩
  | cons θ Γ ih =>
    intro admitted
    obtain ⟨k, hk⟩ := premiseAt_complete source i θ (admitted θ List.mem_cons_self)
    obtain ⟨L, hL, hcheck⟩ := ih (fun η hη => admitted η (List.mem_cons_of_mem _ hη))
    refine ⟨(θ, k) :: L, ?_, ?_⟩
    · simp only [List.map_cons, hL]
    · simp only [premisesAt, List.foldr_cons, hk, Bool.true_and] at hcheck ⊢
      exact hcheck

abbrev Witness := (Syntax × List (Syntax × Nat)) × Nat

noncomputable def decodeWitness (n : Nat) : Witness :=
  (Encodable.decode (α := Witness) n).getD ((.falsum, []), 0)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (((Formula.falsum : Syntax), []), 0))

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]

noncomputable def check (e query certificate : Nat) : Bool :=
  let w := decodeWitness certificate
  let source := Nat.Partrec.Code.ofNatCode e.unpair.1
  let validity := Nat.Partrec.Code.ofNatCode e.unpair.2
  Formula.isClosedCode (w.1.1.code RecordedHead.code) &&
    ((query.unpair.2 == w.1.1.code RecordedHead.code) &&
      (premisesAt source query.unpair.1 w.1.2 &&
        (Nat.Partrec.Code.evaln w.2 validity
          ((Formula.chain (w.1.2.map Prod.fst) w.1.1).code RecordedHead.code)).isSome))

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    check p.1.1 p.1.2 p.2) := by
  have he : Primrec (fun p : (Nat × Nat) × Nat => p.1.1.unpair) := Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)
  have hsource := (Primrec.ofNat Program).comp (Primrec.fst.comp he)
  have hvalidity := (Primrec.ofNat Program).comp (Primrec.snd.comp he)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) := Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hi := Primrec.fst.comp hq
  have hquery := Primrec.snd.comp hq
  have hw : Primrec (fun p : (Nat × Nat) × Nat => decodeWitness p.2) := decodeWitness_primrec.comp Primrec.snd
  have hφ := Primrec.fst.comp (Primrec.fst.comp hw)
  have hcode := RecordedFormula.code_primrec.comp hφ
  have hL := Primrec.snd.comp (Primrec.fst.comp hw)
  have hΓ := Primrec.list_map hL ((Primrec.fst.comp Primrec.snd).to₂)
  have hk := Primrec.snd.comp hw
  have hchain := RecordedFormula.code_primrec.comp (RecordedFormula.chain_primrec.comp hΓ hφ)
  have hgen := premisesAt_primrec.comp ((hsource.pair hi).pair hL)
  have hv := Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hvalidity).pair hchain)
  exact Primrec.and.comp (Formula.isClosedCode_primrec.comp hcode)
    (Primrec.and.comp (Primrec.beq.comp hquery hcode)
      (Primrec.and.comp hgen (Primrec.option_isSome.comp hv)))

noncomputable def evaluation (e query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check e query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (e query : Nat) :
    (evaluation e query).Dom ↔ ∃ certificate, check e query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (source validity : Program) (i : Nat) (φ : Syntax) :
    (evaluation (Nat.pair (Encodable.encode source) (Encodable.encode validity))
      (Nat.pair i (φ.code RecordedHead.code))).Dom ↔ generated source validity i φ := by
  rw [evaluation_domain]
  have hs : Nat.Partrec.Code.ofNatCode (Encodable.encode source) = source :=
    Denumerable.ofNat_encode source
  have hv : Nat.Partrec.Code.ofNatCode (Encodable.encode validity) = validity :=
    Denumerable.ofNat_encode validity
  constructor
  · rintro ⟨n, hn⟩
    let w := decodeWitness n
    have hcheck : w.1.1.Closed ∧ φ.code RecordedHead.code = w.1.1.code RecordedHead.code ∧
        premisesAt source i w.1.2 = true ∧
        (Nat.Partrec.Code.evaln w.2 validity
          ((Formula.chain (w.1.2.map Prod.fst) w.1.1).code RecordedHead.code)).isSome = true := by
      simpa only [check, Nat.unpair_pair, hs, hv, Bool.and_eq_true,
        beq_iff_eq, RecordedPrefixProgram.recorded_closed_code] using hn
    have heq : φ = w.1.1 := Formula.code_injective RecordedHead.code RecordedHead.code_injective hcheck.2.1
    refine ⟨heq.symm ▸ hcheck.1, w.1.2.map Prod.fst, ?_, ?_⟩
    · intro θ hθ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hθ
      exact premiseAt_sound source i p ((premisesAt_iff source i _).mp hcheck.2.2.1 p hp)
    · obtain ⟨v, hh⟩ := Option.isSome_iff_exists.mp hcheck.2.2.2
      simpa only [heq, Program.domain] using (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hh)).1
  · rintro ⟨hφ, Γ, admitted, hvalid⟩
    obtain ⟨L, hL, hcheck⟩ := decorate source i Γ admitted
    obtain ⟨v, hh⟩ := Part.dom_iff_mem.mp hvalid
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    refine ⟨Encodable.encode ((φ, L), k), ?_⟩
    simp only [check, decodeWitness_encode, Nat.unpair_pair, hs, hv,
      (RecordedPrefixProgram.recorded_closed_code φ).mpr hφ, Bool.true_and, beq_self_eq_true,
      hcheck, hL, Option.mem_def.mp hk, Option.isSome_some]

theorem evaluation_only_sentences (e query : Nat) (h : (evaluation e query).Dom) :
    ∃ i, ∃ φ : Syntax, query = Nat.pair i (φ.code RecordedHead.code) ∧ φ.Closed := by
  obtain ⟨n, hn⟩ := (evaluation_domain e query).mp h
  let w := decodeWitness n
  have hclosed : w.1.1.Closed := (RecordedPrefixProgram.recorded_closed_code _).mp
    (Bool.and_eq_true_iff.mp hn).1
  have hcode : query.unpair.2 = w.1.1.code RecordedHead.code :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hn).2).1
  refine ⟨query.unpair.1, w.1.1, ?_, hclosed⟩
  rw [← hcode]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists :
    ∃ compiler : Program × Program → Program, Primrec compiler ∧
      (∀ source validity i φ,
        (compiler (source, validity)).domain (Nat.pair i (φ.code RecordedHead.code)) ↔
          generated source validity i φ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ i, ∃ φ : Syntax, query = Nat.pair i (φ.code RecordedHead.code) ∧ φ.Closed) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let parameter (p : Program × Program) := Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)
  let compiler (p : Program × Program) := Nat.Partrec.Code.curry kernel (parameter p)
  have hparameter : Primrec parameter := Primrec₂.natPair.comp
    (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
  have heval (p : Program × Program) (n : Nat) :
      (compiler p).eval n = evaluation (parameter p) n := by
    change (Nat.Partrec.Code.curry kernel _).eval n = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) hparameter,
    ?_, ?_⟩
  · intro source validity i φ
    change ((compiler _).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct source validity i φ
  · intro p query h
    change ((compiler p).eval query).Dom at h
    rw [heval] at h
    exact evaluation_only_sentences _ _ h

theorem generated_iff_provable (source validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ)
    (i : Nat) (φ : Syntax) :
    generated source validity i φ ↔ φ.Closed ∧ Provable (axioms source i) φ := by
  have recordedValidity (θ : Syntax) : validity.domain (θ.code RecordedHead.code) ↔ Valid θ := by
    rw [← encode_code, hvalid, valid_encode]
  constructor
  · rintro ⟨hφ, Γ, admitted, hv⟩
    exact ⟨hφ, ⟨{
      premises := Γ
      admitted := admitted
      validity := (recordedValidity _).mp hv }⟩⟩
  · rintro ⟨hφ, c⟩
    obtain ⟨c⟩ := c
    exact ⟨hφ, c.premises, c.admitted, (recordedValidity _).mpr c.validity⟩

theorem theory_closed (source validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ)
    (i : Nat) (φ : Syntax) (hφ : φ.Closed) :
    Provable (generated source validity i) φ ↔ generated source validity i φ := by
  constructor
  · rintro ⟨c⟩
    apply (generated_iff_provable source validity hvalid i φ).mpr
    refine ⟨hφ, c.consequences ?_⟩
    intro θ hθ
    exact ((generated_iff_provable source validity hvalid i θ).mp hθ).2
  · exact Provable.of_axiom

theorem axioms_exact (source : Program) (base : Nat → Syntax → Prop)
    (exactSource : ∀ i φ, source.domain (Nat.pair i (φ.code RecordedHead.code)) ↔ base i φ)
    (closedSource : ∀ i φ, base i φ → φ.Closed) (i : Nat) (φ : Syntax) :
    axioms source i φ ↔ base i φ :=
  ⟨fun h => (exactSource i φ).mp h.2,
    fun h => ⟨closedSource i φ h, (exactSource i φ).mpr h⟩⟩

theorem generated_exact (source validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ)
    (base : Nat → Syntax → Prop)
    (exactSource : ∀ i φ, source.domain (Nat.pair i (φ.code RecordedHead.code)) ↔ base i φ)
    (closedSource : ∀ i φ, base i φ → φ.Closed) (i : Nat) (φ : Syntax) :
    generated source validity i φ ↔ φ.Closed ∧ Provable (base i) φ := by
  rw [generated_iff_provable source validity hvalid i φ]
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨hc, hp.mono (fun θ h => (axioms_exact source base exactSource closedSource i θ).mp h)⟩
  · rintro ⟨hc, hp⟩
    exact ⟨hc, hp.mono (fun θ h => (axioms_exact source base exactSource closedSource i θ).mpr h)⟩

/-- A concrete composition of the recorded background, indexed-prefix and
    finite-consequence compilers. Exact validity and contextual edge programs
    remain semantic inputs, while all compiler/effectivity proofs are constructed. -/
theorem background_theory_compiler_exists :
    ∃ compiler : RecordedBackgroundProgram.Parameters → Program, Primrec compiler ∧
      (∀ p R, (∀ μ ν, p.1.2.domain (Nat.pair μ ν) ↔ R μ ν) →
        (∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ) → ∀ a σ,
        (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
          σ.Closed ∧ Provable (RecordedAdmissions p.1.1.1.toFinset p.1.1.2.toFinset a R) σ) ∧
      (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
        query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed) := by
  obtain ⟨generators, hgen, exactGen, _⟩ := RecordedPrefixProgram.background_compiler_exists
  obtain ⟨consequences, hcon, exactCon, rawCon⟩ := compiler_exists
  let parameters := fun p : RecordedBackgroundProgram.Parameters => (generators p, p.2)
  let compiler := fun p : RecordedBackgroundProgram.Parameters => consequences (parameters p)
  have hp : Primrec parameters := hgen.pair Primrec.snd
  refine ⟨compiler, hcon.comp hp, ?_, ?_⟩
  · intro p R hedge hvalid a σ
    exact (exactCon (generators p) p.2 a σ).trans
      (generated_exact (generators p) p.2 hvalid
        (fun b θ => RecordedAdmissions p.1.1.1.toFinset p.1.1.2.toFinset b R θ)
        (exactGen p R hedge hvalid) (fun _ _ h => h.closed) a σ)
  · intro p query h
    exact rawCon (parameters p) query h

end RecordedConsequenceProgram

end Alexander313
