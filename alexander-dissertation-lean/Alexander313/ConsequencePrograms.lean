import Alexander313.Effective.ValidityImages
import Alexander313.RecordedLogic

/-!
# A real finite-certificate consequence program

Inputs are ordinary generator and validity program values. Every premise has
its own positive finite halting witness, so no uniform running-time bound or
negative test is needed. The target and premises are literal closed formulas;
the implication chain is tested by an actual positive validity computation.
The compiler is constructed without a validity oracle. Identification with
semantic consequence still needs an exact validity program, which is not
constructed in this file.
-/

namespace Alexander313

namespace Formula

theorem chain_primrec : Primrec₂ (chain (Owner := Nat)) := by
  have step : Primrec₂ (fun (_ : List (Formula Nat) × Formula Nat)
      (p : Formula Nat × Formula Nat) => Formula.imp p.1 p.2) :=
    (imp_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have hf := Primrec.list_foldr Primrec.fst Primrec.snd step
  have heq (Γ : List (Formula Nat)) (φ : Formula Nat) :
      Γ.foldr Formula.imp φ = chain Γ φ := by
    induction Γ with
    | nil => rfl
    | cons θ Γ ih => simp only [List.foldr_cons, chain, ih]
  exact hf.to₂.of_eq heq

end Formula

namespace ConsequenceProgram

def axioms (source : Program) (i : Nat) (φ : Formula Nat) : Prop :=
  φ.Closed ∧ source.domain (Nat.pair i (φ.code id))

def generated (source validity : Program) (i : Nat) (φ : Formula Nat) : Prop :=
  φ.Closed ∧ ∃ Γ : List (Formula Nat),
    (∀ θ ∈ Γ, axioms source i θ) ∧ validity.domain ((Formula.chain Γ φ).code id)

def premiseAt (source : Program) (i : Nat) (p : Formula Nat × Nat) : Bool :=
  Formula.isClosedCode (p.1.code id) &&
    (Nat.Partrec.Code.evaln p.2 source (Nat.pair i (p.1.code id))).isSome

theorem premiseAt_primrec :
    Primrec (fun p : (Program × Nat) × (Formula Nat × Nat) =>
      premiseAt p.1.1 p.1.2 p.2) := by
  have hsource : Primrec (fun p : (Program × Nat) × (Formula Nat × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : (Program × Nat) × (Formula Nat × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hφ : Primrec (fun p : (Program × Nat) × (Formula Nat × Nat) => p.2.1.code id) :=
    Formula.code_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hk : Primrec (fun p : (Program × Nat) × (Formula Nat × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have heval := Nat.Partrec.Code.primrec_evaln.comp
    ((hk.pair hsource).pair (Primrec₂.natPair.comp hi hφ))
  exact Primrec.and.comp (Formula.isClosedCode_primrec.comp hφ)
    (Primrec.option_isSome.comp heval)

def premisesAt (source : Program) (i : Nat) (L : List (Formula Nat × Nat)) : Bool :=
  L.foldr (fun p previous => premiseAt source i p && previous) true

theorem premisesAt_primrec :
    Primrec (fun p : (Program × Nat) × List (Formula Nat × Nat) =>
      premisesAt p.1.1 p.1.2 p.2) := by
  have step : Primrec₂ (fun (p : (Program × Nat) × List (Formula Nat × Nat))
      (s : (Formula Nat × Nat) × Bool) => premiseAt p.1.1 p.1.2 s.1 && s.2) :=
    (Primrec.and.comp
      (premiseAt_primrec.comp
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) step

theorem premisesAt_iff (source : Program) (i : Nat) (L : List (Formula Nat × Nat)) :
    premisesAt source i L = true ↔ ∀ p ∈ L, premiseAt source i p = true := by
  induction L with
  | nil => simp [premisesAt]
  | cons p L ih =>
    simp only [premisesAt, List.foldr_cons, Bool.and_eq_true, List.forall_mem_cons]
    exact and_congr Iff.rfl ih

theorem premiseAt_sound (source : Program) (i : Nat) (p : Formula Nat × Nat)
    (h : premiseAt source i p = true) : axioms source i p.1 := by
  have hs := Bool.and_eq_true_iff.mp h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs.2
  exact ⟨(Formula.isClosedCode_code p.1).mp hs.1,
    (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1⟩

theorem premiseAt_complete (source : Program) (i : Nat) (φ : Formula Nat)
    (h : axioms source i φ) : ∃ k, premiseAt source i (φ, k) = true := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h.2
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  refine ⟨k, ?_⟩
  simp only [premiseAt, (Formula.isClosedCode_code φ).mpr h.1, Bool.true_and,
    Option.mem_def.mp hk, Option.isSome_some]

/-- Decorate each actual premise independently. This avoids assuming a common
    proof-depth or computation bound for different numerical source proofs. -/
theorem decorate (source : Program) (i : Nat) (Γ : List (Formula Nat))
    (admitted : ∀ θ ∈ Γ, axioms source i θ) :
    ∃ L : List (Formula Nat × Nat), L.map Prod.fst = Γ ∧ premisesAt source i L = true := by
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

abbrev Witness := (Formula Nat × List (Formula Nat × Nat)) × Nat

noncomputable def decodeWitness (n : Nat) : Witness :=
  (Encodable.decode (α := Witness) n).getD ((.falsum, []), 0)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (((Formula.falsum : Formula Nat), []), 0))

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]

noncomputable def check (e query certificate : Nat) : Bool :=
  let w := decodeWitness certificate
  let source := Nat.Partrec.Code.ofNatCode e.unpair.1
  let validity := Nat.Partrec.Code.ofNatCode e.unpair.2
  Formula.isClosedCode (w.1.1.code id) &&
    ((query.unpair.2 == w.1.1.code id) &&
      (premisesAt source query.unpair.1 w.1.2 &&
        (Nat.Partrec.Code.evaln w.2 validity
          ((Formula.chain (w.1.2.map Prod.fst) w.1.1).code id)).isSome))

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    check p.1.1 p.1.2 p.2) := by
  have he : Primrec (fun p : (Nat × Nat) × Nat => p.1.1.unpair) :=
    Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)
  have hsource := (Primrec.ofNat Program).comp (Primrec.fst.comp he)
  have hvalidity := (Primrec.ofNat Program).comp (Primrec.snd.comp he)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hi := Primrec.fst.comp hq
  have hquery := Primrec.snd.comp hq
  have hw : Primrec (fun p : (Nat × Nat) × Nat => decodeWitness p.2) :=
    decodeWitness_primrec.comp Primrec.snd
  have hφ := Primrec.fst.comp (Primrec.fst.comp hw)
  have hcode := Formula.code_primrec.comp hφ
  have hL := Primrec.snd.comp (Primrec.fst.comp hw)
  have hΓ := Primrec.list_map hL ((Primrec.fst.comp Primrec.snd).to₂)
  have hk := Primrec.snd.comp hw
  have hchain := Formula.code_primrec.comp (Formula.chain_primrec.comp hΓ hφ)
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

theorem evaluation_correct (source validity : Program) (i : Nat) (φ : Formula Nat) :
    (evaluation (Nat.pair (Encodable.encode source) (Encodable.encode validity))
      (Nat.pair i (φ.code id))).Dom ↔ generated source validity i φ := by
  rw [evaluation_domain]
  have hs : Nat.Partrec.Code.ofNatCode (Encodable.encode source) = source :=
    Denumerable.ofNat_encode source
  have hv : Nat.Partrec.Code.ofNatCode (Encodable.encode validity) = validity :=
    Denumerable.ofNat_encode validity
  constructor
  · rintro ⟨n, hn⟩
    let w := decodeWitness n
    have hcheck : w.1.1.Closed ∧ φ.code id = w.1.1.code id ∧
        premisesAt source i w.1.2 = true ∧
        (Nat.Partrec.Code.evaln w.2 validity
          ((Formula.chain (w.1.2.map Prod.fst) w.1.1).code id)).isSome = true := by
      simpa only [check, Nat.unpair_pair, hs, hv, Bool.and_eq_true,
        beq_iff_eq, Formula.isClosedCode_code] using hn
    have heq : φ = w.1.1 := Formula.code_injective id Function.injective_id hcheck.2.1
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
      (Formula.isClosedCode_code φ).mpr hφ, Bool.true_and, beq_self_eq_true,
      hcheck, hL, Option.mem_def.mp hk, Option.isSome_some]

theorem evaluation_only_sentences (e query : Nat) (h : (evaluation e query).Dom) :
    ∃ i, ∃ φ : Formula Nat, query = Nat.pair i (φ.code id) ∧ φ.Closed := by
  obtain ⟨n, hn⟩ := (evaluation_domain e query).mp h
  let w := decodeWitness n
  have hclosed : w.1.1.Closed := (Formula.isClosedCode_code _).mp
    (Bool.and_eq_true_iff.mp hn).1
  have hcode : query.unpair.2 = w.1.1.code id :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hn).2).1
  refine ⟨query.unpair.1, w.1.1, ?_, hclosed⟩
  rw [← hcode]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists :
    ∃ compiler : Program × Program → Program, Primrec compiler ∧
      (∀ source validity i φ,
        (compiler (source, validity)).domain (Nat.pair i (φ.code id)) ↔
          generated source validity i φ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ i, ∃ φ : Formula Nat, query = Nat.pair i (φ.code id) ∧ φ.Closed) := by
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
    (i : Nat) (φ : Formula Nat) :
    generated source validity i φ ↔ φ.Closed ∧ Provable (axioms source i) φ := by
  constructor
  · rintro ⟨hφ, Γ, admitted, hv⟩
    exact ⟨hφ, ⟨{
      premises := Γ
      admitted := admitted
      validity := (hvalid _).mp hv }⟩⟩
  · rintro ⟨hφ, c⟩
    obtain ⟨c⟩ := c
    exact ⟨hφ, c.premises, c.admitted, (hvalid _).mpr c.validity⟩

theorem theory_closed (source validity : Program)
    (hvalid : ∀ φ : Formula Nat, validity.domain (φ.code id) ↔ Valid φ)
    (i : Nat) (φ : Formula Nat) (hφ : φ.Closed) :
    Provable (generated source validity i) φ ↔ generated source validity i φ := by
  constructor
  · rintro ⟨c⟩
    apply (generated_iff_provable source validity hvalid i φ).mpr
    refine ⟨hφ, c.consequences ?_⟩
    intro θ hθ
    exact ((generated_iff_provable source validity hvalid i θ).mp hθ).2
  · exact Provable.of_axiom

end ConsequenceProgram

end Alexander313
