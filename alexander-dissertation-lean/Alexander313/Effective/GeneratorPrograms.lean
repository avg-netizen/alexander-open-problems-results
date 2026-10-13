import Alexander313.Effective.SchemaGenerators
import Alexander313.Effective.SubordinateGenerators

/-!
# Positive finite unions and literal own-prefix admission programs

Finite unions dovetail bounded positive computations. Prefix admission
checks a positive computation of the base generator on a closed sentence,
and compares literal prefix syntax. Both compilers are primitive recursive
in their actual program data. Their composition below is the syntactic and
subordinate part of the source generator, not a consequence enumerator.
-/

namespace Alexander313
namespace Program

def unionAt (L : List Program) (n cutoff : Nat) : Bool :=
  L.foldr (fun c previous => (Nat.Partrec.Code.evaln cutoff c n).isSome || previous) false

theorem unionAt_primrec : Primrec (fun p : (List Program × Nat) × Nat =>
    unionAt p.1.1 p.1.2 p.2) := by
  have hstep : Primrec₂ (fun (p : (List Program × Nat) × Nat) (s : Program × Bool) =>
      (Nat.Partrec.Code.evaln p.2 s.1 p.1.2).isSome || s.2) := by
    have hk : Primrec (fun p : ((List Program × Nat) × Nat) × (Program × Bool) => p.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hc : Primrec (fun p : ((List Program × Nat) × Nat) × (Program × Bool) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hn : Primrec (fun p : ((List Program × Nat) × Nat) × (Program × Bool) => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have he := Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hc).pair hn)
    exact (Primrec.or.comp (Primrec.option_isSome.comp he) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.fst.comp Primrec.fst) (Primrec.const false) hstep

theorem unionAt_iff (L : List Program) (n cutoff : Nat) :
    unionAt L n cutoff = true ↔
      ∃ c ∈ L, (Nat.Partrec.Code.evaln cutoff c n).isSome = true := by
  induction L with
  | nil => simp [unionAt]
  | cons c L ih =>
    change ((Nat.Partrec.Code.evaln cutoff c n).isSome || unionAt L n cutoff) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨d, hd, ht⟩)
      · exact ⟨c, List.mem_cons_self, h⟩
      · exact ⟨d, List.mem_cons_of_mem c hd, ht⟩
    · rintro ⟨d, hd, ht⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Or.inl ht
      · exact Or.inr ⟨d, hd, ht⟩

theorem unionAt_domain (L : List Program) (n : Nat) :
    (∃ cutoff, unionAt L n cutoff = true) ↔ ∃ c ∈ L, c.domain n := by
  constructor
  · rintro ⟨cutoff, h⟩
    obtain ⟨c, hc, ht⟩ := (unionAt_iff L n cutoff).mp h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ht
    exact ⟨c, hc, (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1⟩
  · rintro ⟨c, hc, h⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨cutoff, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨cutoff, (unionAt_iff L n cutoff).mpr ⟨c, hc, ?_⟩⟩
    exact Option.isSome_iff_exists.mpr ⟨v, Option.mem_def.mp hk⟩

def decodePrograms (e : Nat) : List Program := (Encodable.decode (α := List Program) e).getD []

theorem decodePrograms_primrec : Primrec decodePrograms :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([] : List Program))

@[simp] theorem decodePrograms_encode (L : List Program) :
    decodePrograms (Encodable.encode L) = L := by simp [decodePrograms]

def unionEvaluation (e n : Nat) : Part Nat :=
  Nat.rfind (fun cutoff => Part.some (unionAt (decodePrograms e) n cutoff))

theorem unionEvaluation_partrec : Partrec₂ unionEvaluation := by
  have hL : Primrec (fun p : (Nat × Nat) × Nat => decodePrograms p.1.1) :=
    decodePrograms_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht := unionAt_primrec.comp ((hL.pair hn).pair Primrec.snd)
  exact (Partrec.rfind ht.to_comp.partrec.to₂).to₂

theorem unionEvaluation_domain (e n : Nat) :
    (unionEvaluation e n).Dom ↔ ∃ c ∈ decodePrograms e, c.domain n := by
  have h : (unionEvaluation e n).Dom ↔ ∃ cutoff, unionAt (decodePrograms e) n cutoff = true := by
    simp only [unionEvaluation, Nat.rfind_dom, Part.mem_some_iff,
      Part.some_dom, implies_true, and_true, Bool.true_eq]
  exact h.trans (unionAt_domain (decodePrograms e) n)

theorem finiteUnionCompiler_exists :
    ∃ compiler : List Program → Program, Primrec compiler ∧
      ∀ L n, (compiler L).domain n ↔ ∃ c ∈ L, c.domain n := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr unionEvaluation_partrec)
  refine ⟨fun L => Nat.Partrec.Code.curry kernel (Encodable.encode L),
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_⟩
  intro L n
  change ((Nat.Partrec.Code.curry kernel _).eval n).Dom ↔ _
  rw [Nat.Partrec.Code.eval_curry, hkernel]
  simpa only [Nat.unpaired, Nat.unpair_pair, decodePrograms_encode] using
    unionEvaluation_domain (Encodable.encode L) n

end Program

namespace PrefixAdmission

def generated (c : Program) (i : Nat) (σ : Formula Nat) : Prop :=
  ∃ ρ n, ρ.Closed ∧ c.domain (Nat.pair i (ρ.code id)) ∧ σ = Formula.«prefix» i n ρ

theorem generated_closed {c : Program} {i : Nat} {σ : Formula Nat}
    (h : generated c i σ) : σ.Closed := by
  obtain ⟨ρ, n, hc, _, rfl⟩ := h
  simpa only [Formula.Closed, Formula.freeVars_prefix] using hc

theorem generated_known {c : Program} {i : Nat} {σ : Formula Nat}
    (h : generated c i σ) : generated c i (.know i σ) := by
  obtain ⟨ρ, n, hc, hd, rfl⟩ := h
  exact ⟨ρ, n + 1, hc, hd, rfl⟩

def check (e query witness : Nat) : Bool :=
  let body := witness.unpair.1
  let depth := witness.unpair.2.unpair.1
  let cutoff := witness.unpair.2.unpair.2
  Formula.isClosedCode body &&
    ((Nat.Partrec.Code.evaln cutoff (Nat.Partrec.Code.ofNatCode e)
      (Nat.pair query.unpair.1 body)).isSome &&
      (query.unpair.2 == prefixCode query.unpair.1 depth body))

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    check p.1.1 p.1.2 p.2) := by
  have he : Primrec (fun p : (Nat × Nat) × Nat => Nat.Partrec.Code.ofNatCode p.1.1) :=
    (Primrec.ofNat Program).comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hi := Primrec.fst.comp hq
  have hσ := Primrec.snd.comp hq
  have hw : Primrec (fun p : (Nat × Nat) × Nat => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hbody := Primrec.fst.comp hw
  have htail := Primrec.unpair.comp (Primrec.snd.comp hw)
  have hn := Primrec.fst.comp htail
  have hk := Primrec.snd.comp htail
  have ht := Nat.Partrec.Code.primrec_evaln.comp
    ((hk.pair he).pair (Primrec₂.natPair.comp hi hbody))
  have hp := prefixCode_primrec.comp ((hi.pair hbody).pair hn)
  exact Primrec.and.comp (Formula.isClosedCode_primrec.comp hbody)
    (Primrec.and.comp (Primrec.option_isSome.comp ht) (Primrec.beq.comp hσ hp))

def evaluation (e query : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (check e query witness))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (e query : Nat) :
    (evaluation e query).Dom ↔ ∃ witness, check e query witness = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (c : Program) (i : Nat) (σ : Formula Nat) :
    (evaluation (Encodable.encode c) (Nat.pair i (σ.code id))).Dom ↔ generated c i σ := by
  rw [evaluation_domain]
  have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c := Denumerable.ofNat_encode c
  constructor
  · rintro ⟨w, hw⟩
    have hcheck : Formula.isClosedCode w.unpair.1 = true ∧
        (Nat.Partrec.Code.evaln w.unpair.2.unpair.2 c (Nat.pair i w.unpair.1)).isSome = true ∧
        σ.code id = prefixCode i w.unpair.2.unpair.1 w.unpair.1 := by
      simpa only [check, Nat.unpair_pair, hc, Bool.and_eq_true, beq_iff_eq] using hw
    obtain ⟨ρ, hρ, hclosed⟩ := (Formula.isClosedCode_iff w.unpair.1).mp hcheck.1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcheck.2.1
    have hdomain : c.domain (Nat.pair i (ρ.code id)) := by
      rw [hρ]
      exact (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1
    refine ⟨ρ, w.unpair.2.unpair.1, hclosed, hdomain,
      Formula.code_injective id Function.injective_id ?_⟩
    simpa only [← hρ, prefixCode_eq] using hcheck.2.2
  · rintro ⟨ρ, n, hclosed, hdomain, rfl⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdomain
    obtain ⟨cutoff, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    have hsyntax := (Formula.isClosedCode_code ρ).mpr hclosed
    refine ⟨Nat.pair (ρ.code id) (Nat.pair n cutoff), ?_⟩
    simp only [check, Nat.unpair_pair, hc, hsyntax, Bool.true_and,
      Option.mem_def.mp hk, Option.isSome_some, prefixCode_eq, beq_self_eq_true]

theorem evaluation_only_sentences (e query : Nat) (h : (evaluation e query).Dom) :
    ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed := by
  obtain ⟨w, hw⟩ := (evaluation_domain e query).mp h
  have hsyntax : Formula.isClosedCode w.unpair.1 = true := (Bool.and_eq_true_iff.mp hw).1
  have heq : query.unpair.2 = prefixCode query.unpair.1 w.unpair.2.unpair.1 w.unpair.1 :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).2).2
  obtain ⟨ρ, hρ, hclosed⟩ := (Formula.isClosedCode_iff w.unpair.1).mp hsyntax
  let σ := Formula.«prefix» query.unpair.1 w.unpair.2.unpair.1 ρ
  have hcode : query.unpair.2 = σ.code id := by
    simpa only [← hρ, prefixCode_eq] using heq
  have hσ : σ.Closed := by
    simpa only [σ, Formula.Closed, Formula.freeVars_prefix] using hclosed
  refine ⟨query.unpair.1, σ, ?_, hσ⟩
  rw [← hcode]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists :
    ∃ compiler : Program → Program, Primrec compiler ∧
      (∀ c i σ, (compiler c).domain (Nat.pair i (σ.code id)) ↔ generated c i σ) ∧
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

theorem generated_iff_prefixed {c : Program} {G : Nat → Formula Nat → Prop}
    (hexact : ∀ i σ, c.domain (Nat.pair i (σ.code id)) ↔ G i σ)
    (hclosed : ∀ i σ, G i σ → σ.Closed) (i : Nat) (σ : Formula Nat) :
    generated c i σ ↔ PrefixedAxioms i (G i) σ := by
  constructor
  · rintro ⟨ρ, n, _, hd, heq⟩
    exact ⟨ρ, n, (hexact i ρ).mp hd, heq⟩
  · rintro ⟨ρ, n, hg, heq⟩
    exact ⟨ρ, n, hclosed i ρ hg, (hexact i ρ).mpr hg, heq⟩

end PrefixAdmission

def SyntacticSourceGenerator (c edge : Program) (i : Nat) (σ : Formula Nat) : Prop :=
  SyntacticBackground.admits i σ ∨ SubordinateCodeGenerator c edge i σ

theorem SyntacticSourceGenerator.closed {c edge : Program} {i : Nat} {σ : Formula Nat}
    (h : SyntacticSourceGenerator c edge i σ) : σ.Closed := by
  rcases h with h | h
  · exact SyntacticBackground.admits_closed h
  · exact h.closed

/-- This is an actual compiler for all syntactic source branches and their
own prefixes. The still-missing validity/assigned-validity branches and
consequence enumeration are not parameters or conclusions of this theorem. -/
theorem syntacticSourceCompiler_exists :
    ∃ compiler : Program × Program → Program, Primrec compiler ∧
      (∀ c edge i σ, (compiler (c, edge)).domain (Nat.pair i (σ.code id)) ↔
        PrefixedAxioms i (SyntacticSourceGenerator c edge i) σ) ∧
      (∀ p query, (compiler p).domain query →
        ∃ i, ∃ σ : Formula Nat, query = Nat.pair i (σ.code id) ∧ σ.Closed) ∧
      (∀ c edge i σ, (compiler (c, edge)).domain (Nat.pair i (σ.code id)) →
        (compiler (c, edge)).domain (Nat.pair i ((Formula.know i σ).code id))) := by
  obtain ⟨schemas, hschemas, _⟩ := SyntacticBackground.program_exists
  obtain ⟨subordinate, hsubPR, hsub⟩ := subordinate_generator_programs
  obtain ⟨union, hunionPR, hunion⟩ := Program.finiteUnionCompiler_exists
  obtain ⟨prefixes, hprefixPR, hprefix, hsentences⟩ := PrefixAdmission.compiler_exists
  let base : Program × Program → Program := fun p => union [schemas, subordinate p]
  have hlist : Primrec (fun p : Program × Program => [schemas, subordinate p]) :=
    Primrec.list_cons.comp (Primrec.const schemas)
      (Primrec.list_cons.comp hsubPR (Primrec.const []))
  have hbasePR : Primrec base := hunionPR.comp hlist
  have hbase (c edge : Program) (i : Nat) (σ : Formula Nat) :
      (base (c, edge)).domain (Nat.pair i (σ.code id)) ↔ SyntacticSourceGenerator c edge i σ := by
    change (union [schemas, subordinate (c, edge)]).domain (Nat.pair i (σ.code id)) ↔ _
    rw [hunion]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨d, rfl | rfl, hd⟩
      · exact Or.inl ((hschemas i σ).mp hd)
      · exact Or.inr ((hsub c edge i σ).mp hd)
    · rintro (hs | hs)
      · exact ⟨schemas, Or.inl rfl, (hschemas i σ).mpr hs⟩
      · exact ⟨subordinate (c, edge), Or.inr rfl, (hsub c edge i σ).mpr hs⟩
  refine ⟨fun p => prefixes (base p), hprefixPR.comp hbasePR, ?_, ?_, ?_⟩
  · intro c edge i σ
    exact (hprefix _ i σ).trans (PrefixAdmission.generated_iff_prefixed (hbase c edge)
      (fun _ _ h => h.closed) i σ)
  · intro p query h
    exact hsentences (base p) query h
  · intro c edge i σ h
    exact (hprefix _ i _).mpr (PrefixAdmission.generated_known ((hprefix _ i σ).mp h))

end Alexander313
