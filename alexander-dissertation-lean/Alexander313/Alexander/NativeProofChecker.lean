import Alexander313.Alexander.NativeFreeVariables
import Alexander313.Alexander.ProofTreeCoding

/-!
# An effective complete native Hilbert proof kernel

All eleven rules, native labels and quantifier side conditions are checked.
The acceptance predicate for sentence premises remains explicit. The actual
finite-premise checker below has no effectivity hypothesis. Neither theorem
asserts effective BL-premise recognition or semantic Hilbert completeness.
-/

noncomputable section

namespace Alexander313.Delta.NativeProofChecker

open FirstOrderCalculus

abbrev Formula := NativeFormula.Syntax 0
abbrev Term := NativeTerm.FreeSyntax
abbrev Sentence := (language Nat).Sentence

local instance formulaDecidableEq : DecidableEq Formula := Encodable.decidableEqOfEncodable _
local instance sentenceDecidableEq : DecidableEq Sentence := Encodable.decidableEqOfEncodable _

attribute [local simp] cond_eq_ite

@[local simp] private theorem decode_formula_code (φ : Formula) :
    Encodable.decode (α := Formula) (NativeFormula.code φ) = some φ := by
  simpa only [NativeFormula.encode_eq_code] using Encodable.encodek φ

@[local simp] private theorem decode_sentence_code (σ : Sentence) :
    Encodable.decode (α := Sentence) (NativeClosedLabels.code σ) = some σ := by
  simpa only [NativeClosedLabels.encode_eq_code] using Encodable.encodek σ

@[local simp] private theorem decode_term_code (t : Term) :
    Encodable.decode (α := Term) (NativeTerm.freeCode t) = some t := by
  simpa only [NativeTerm.free_encode_eq_code] using Encodable.encodek t

private theorem termEmbedding_primrec : Primrec (fun t : Term =>
    (t.relabel Sum.inl : NativeTerm.Syntax 0)) := by
  apply Primrec.encode_iff.1
  simpa only [NativeTerm.encode_eq_code, NativeTerm.freeCode_relabel] using
    NativeTerm.freeCode_primrec

private theorem equality_primrec : Primrec₂
    (FirstOrder.Language.Term.equal : Term → Term → Formula) :=
  (NativeFormula.equal_primrec 0).comp
    (termEmbedding_primrec.comp Primrec.fst) (termEmbedding_primrec.comp Primrec.snd)

private theorem negation_primrec : Primrec (fun φ : Formula => φ.not) :=
  (NativeFormula.imp_primrec 0).comp Primrec.id (Primrec.const (FirstOrder.Language.BoundedFormula.falsum : Formula))

def kRule (p : Formula × Formula) : Formula := p.1.imp (p.2.imp p.1)
def sRule (p : Formula × (Formula × Formula)) : Formula :=
  (p.1.imp (p.2.1.imp p.2.2)).imp ((p.1.imp p.2.1).imp (p.1.imp p.2.2))
def classicalRule (p : Formula × Formula) : Formula :=
  (p.1.not.imp p.2.not).imp (p.2.imp p.1)
def allElimRule (p : Nat × (Term × Formula)) : Formula :=
  (allVariable p.1 p.2.2).imp (substituteVariable p.1 p.2.1 p.2.2)
def allDistRule (p : Nat × (Formula × Formula)) : Formula :=
  (allVariable p.1 (p.2.1.imp p.2.2)).imp
    ((allVariable p.1 p.2.1).imp (allVariable p.1 p.2.2))
def vacuousRule (p : Nat × Formula) : Option Formula :=
  if p.1 ∉ p.2.freeVarFinset then some (p.2.imp (allVariable p.1 p.2)) else none
def eqSubstRule (p : Nat × (Term × (Term × Formula))) : Formula :=
  (p.2.1.equal p.2.2.1).imp
    ((substituteVariable p.1 p.2.1 p.2.2.2).imp
      (substituteVariable p.1 p.2.2.1 p.2.2.2))

theorem kRule_primrec : Primrec kRule :=
  (NativeFormula.imp_primrec 0).comp Primrec.fst
    ((NativeFormula.imp_primrec 0).comp Primrec.snd Primrec.fst)

theorem sRule_primrec : Primrec sRule := by
  have hφ := (Primrec.fst : Primrec (Prod.fst : Formula × (Formula × Formula) → _))
  have hψ : Primrec (fun p : Formula × (Formula × Formula) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hχ : Primrec (fun p : Formula × (Formula × Formula) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have imp := NativeFormula.imp_primrec 0
  exact imp.comp (imp.comp hφ (imp.comp hψ hχ))
    (imp.comp (imp.comp hφ hψ) (imp.comp hφ hχ))

theorem classicalRule_primrec : Primrec classicalRule := by
  have imp := NativeFormula.imp_primrec 0
  exact imp.comp (imp.comp (negation_primrec.comp Primrec.fst)
    (negation_primrec.comp Primrec.snd)) (imp.comp Primrec.snd Primrec.fst)

theorem allElimRule_primrec : Primrec allElimRule := by
  have hx := (Primrec.fst : Primrec (Prod.fst : Nat × (Term × Formula) → _))
  have ht : Primrec (fun p : Nat × (Term × Formula) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hφ : Primrec (fun p : Nat × (Term × Formula) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (NativeFormula.imp_primrec 0).comp
    (NativeFormula.allVariable_primrec.comp hx hφ)
    (NativeFormula.substituteVariable_primrec.comp ((hx.pair ht).pair hφ))

theorem allDistRule_primrec : Primrec allDistRule := by
  have hx := (Primrec.fst : Primrec (Prod.fst : Nat × (Formula × Formula) → _))
  have hφ : Primrec (fun p : Nat × (Formula × Formula) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hψ : Primrec (fun p : Nat × (Formula × Formula) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have imp := NativeFormula.imp_primrec 0
  have all := NativeFormula.allVariable_primrec
  exact imp.comp (all.comp hx (imp.comp hφ hψ))
    (imp.comp (all.comp hx hφ) (all.comp hx hψ))

theorem vacuousRule_primrec : Primrec vacuousRule :=
  Primrec.ite (NativeFormula.freeVariableMembership_primrec 0).not
    (Primrec.option_some.comp ((NativeFormula.imp_primrec 0).comp Primrec.snd
      (NativeFormula.allVariable_primrec.comp Primrec.fst Primrec.snd))) (Primrec.const none)

theorem eqSubstRule_primrec : Primrec eqSubstRule := by
  have hx := (Primrec.fst : Primrec (Prod.fst : Nat × (Term × (Term × Formula)) → _))
  have ht : Primrec (fun p : Nat × (Term × (Term × Formula)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : Nat × (Term × (Term × Formula)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hφ : Primrec (fun p : Nat × (Term × (Term × Formula)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have sub := NativeFormula.substituteVariable_primrec
  have imp := NativeFormula.imp_primrec 0
  exact imp.comp (equality_primrec.comp ht hu)
    (imp.comp (sub.comp ((hx.pair ht).pair hφ)) (sub.comp ((hx.pair hu).pair hφ)))

def leafCheck (accept : Sentence → Bool) (tag payload : Nat) : Option Formula :=
  cond (tag == 0) ((Encodable.decode (α := Sentence) payload).bind fun σ =>
    if accept σ then some (sentenceFormula σ) else none)
    (cond (tag == 1) ((Encodable.decode (α := Formula × Formula) payload).map kRule)
      (cond (tag == 2) ((Encodable.decode (α := Formula × (Formula × Formula)) payload).map sRule)
        (cond (tag == 3) ((Encodable.decode (α := Formula × Formula) payload).map classicalRule)
          (cond (tag == 4) ((Encodable.decode (α := Nat × (Term × Formula)) payload).map allElimRule)
            (cond (tag == 5) ((Encodable.decode (α := Nat × (Formula × Formula)) payload).map allDistRule)
              (cond (tag == 6) ((Encodable.decode (α := Nat × Formula) payload).bind vacuousRule)
                (cond (tag == 7) ((Encodable.decode (α := Term) payload).map fun t => t.equal t)
                  (cond (tag == 8)
                    ((Encodable.decode (α := Nat × (Term × (Term × Formula))) payload).map eqSubstRule)
                    none))))))))

theorem leafCheck_primrec {accept : Sentence → Bool} (ha : Primrec accept) :
    Primrec₂ (leafCheck accept) := by
  have test (t : Nat) := Primrec.beq.comp (Primrec.fst : Primrec (Prod.fst : Nat × Nat → _))
    (Primrec.const t)
  have mapped {B : Type} [Primcodable B] (f : B → Formula) (hf : Primrec f) :
      Primrec (fun p : Nat × Nat => (Encodable.decode (α := B) p.2).map f) :=
    (Primrec.decode.comp Primrec.snd).option_map (hf.comp Primrec.snd).to₂
  have assumption : Primrec (fun p : Nat × Nat =>
      (Encodable.decode (α := Sentence) p.2).bind fun σ =>
        if accept σ then some (sentenceFormula σ) else none) :=
    (Primrec.decode.comp Primrec.snd).option_bind
      (Primrec.ite (Primrec.eq.comp (ha.comp Primrec.snd) (Primrec.const true))
        (Primrec.option_some.comp (NativeClosedLabels.sentenceFormula_primrec.comp Primrec.snd))
        (Primrec.const none)).to₂
  have vacuous : Primrec (fun p : Nat × Nat =>
      (Encodable.decode (α := Nat × Formula) p.2).bind vacuousRule) :=
    (Primrec.decode.comp Primrec.snd).option_bind (vacuousRule_primrec.comp Primrec.snd).to₂
  exact ((test 0).cond assumption
    ((test 1).cond (mapped _ kRule_primrec)
      ((test 2).cond (mapped _ sRule_primrec)
        ((test 3).cond (mapped _ classicalRule_primrec)
          ((test 4).cond (mapped _ allElimRule_primrec)
            ((test 5).cond (mapped _ allDistRule_primrec)
              ((test 6).cond vacuous
                ((test 7).cond (mapped _ (equality_primrec.comp Primrec.id Primrec.id))
                  ((test 8).cond (mapped _ eqSubstRule_primrec) (Primrec.const none)))))))))).to₂

def mpResult (payload : Nat) (p q : Option Formula) : Option Formula := do
  let labels ← Encodable.decode (α := Formula × Formula) payload
  if p = some (labels.1.imp labels.2) ∧ q = some labels.1 then some labels.2 else none

def generalizeResult (payload : Nat) (p : Option Formula) : Option Formula := do
  let labels ← Encodable.decode (α := Nat × Formula) payload
  if p = some labels.2 then some (allVariable labels.1 labels.2) else none

theorem mpResult_primrec : Primrec (fun p : Nat × (Option Formula × Option Formula) =>
    mpResult p.1 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : (Nat × (Option Formula × Option Formula)) × (Formula × Formula) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × (Option Formula × Option Formula)) × (Formula × Formula) => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hφ : Primrec (fun p : (Nat × (Option Formula × Option Formula)) × (Formula × Formula) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hψ : Primrec (fun p : (Nat × (Option Formula × Option Formula)) × (Formula × Formula) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hc := PrimrecPred.and
    (Primrec.eq.comp hp (Primrec.option_some.comp ((NativeFormula.imp_primrec 0).comp hφ hψ)))
    (Primrec.eq.comp hq (Primrec.option_some.comp hφ))
  exact (Primrec.decode.comp Primrec.fst).option_bind
    (Primrec.ite hc (Primrec.option_some.comp hψ) (Primrec.const none)).to₂

theorem generalizeResult_primrec : Primrec₂ generalizeResult := by
  have hp : Primrec (fun p : (Nat × Option Formula) × (Nat × Formula) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun p : (Nat × Option Formula) × (Nat × Formula) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hφ : Primrec (fun p : (Nat × Option Formula) × (Nat × Formula) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact ((Primrec.decode.comp Primrec.fst).option_bind
    (Primrec.ite (Primrec.eq.comp hp (Primrec.option_some.comp hφ))
      (Primrec.option_some.comp (NativeFormula.allVariable_primrec.comp hx hφ))
      (Primrec.const none)).to₂).to₂

def numericCheck (accept : Sentence → Bool) : Nat → Option Formula
  | 0 => none
  | k + 1 =>
    let tag := k.unpair.1
    let payload := k.unpair.2
    cond (tag == 9)
      (mpResult payload.unpair.1
        (numericCheck accept payload.unpair.2.unpair.1)
        (numericCheck accept payload.unpair.2.unpair.2))
      (cond (tag == 10)
        (generalizeResult payload.unpair.1 (numericCheck accept payload.unpair.2))
        (leafCheck accept tag payload))
termination_by c => c
decreasing_by
  all_goals
    have h₁ := Nat.unpair_right_le k
    have h₂ := Nat.unpair_right_le k.unpair.2
    have h₃ := Nat.unpair_left_le k.unpair.2.unpair.2
    have h₄ := Nat.unpair_right_le k.unpair.2.unpair.2
    omega

private def checkingStep (accept : Sentence → Bool) (h : List (Option Formula)) : Option Formula :=
  let k := h.length - 1
  let tag := k.unpair.1
  let payload := k.unpair.2
  cond (h.length == 0) none
    (cond (tag == 9)
      (mpResult payload.unpair.1 (h[payload.unpair.2.unpair.1]?.getD none)
        (h[payload.unpair.2.unpair.2]?.getD none))
      (cond (tag == 10)
        (generalizeResult payload.unpair.1 (h[payload.unpair.2]?.getD none))
        (leafCheck accept tag payload)))

set_option maxHeartbeats 800000 in
private theorem checkingStep_primrec {accept : Sentence → Bool} (ha : Primrec accept) :
    Primrec (checkingStep accept) := by
  have hn := (Primrec.list_length : Primrec (List.length (α := Option Formula)))
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hc := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hcp := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hcq := Primrec.snd.comp (Primrec.unpair.comp hc)
  have get (f : List (Option Formula) → Nat) (hf : Primrec f) :
      Primrec (fun h : List (Option Formula) => h[f h]?.getD none) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const none)
  have result := (Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const none)
    ((Primrec.beq.comp ht (Primrec.const 9)).cond
      (mpResult_primrec.comp (hl.pair ((get _ hcp).pair (get _ hcq))))
      ((Primrec.beq.comp ht (Primrec.const 10)).cond
        (generalizeResult_primrec.comp hl (get _ hc)) ((leafCheck_primrec ha).comp ht hp)))
  exact result.of_eq (fun _ => rfl)

theorem numericCheck_primrec {accept : Sentence → Bool} (ha : Primrec accept) :
    Primrec (numericCheck accept) := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List (Option Formula)) =>
      some (checkingStep accept h)) :=
    ((Primrec.option_some.comp (checkingStep_primrec ha)).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => numericCheck accept c) hg (by
    intro a c
    cases c with
    | zero => simp [checkingStep, numericCheck]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hc := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2) hp
      have hl := lt_of_le_of_lt (Nat.unpair_left_le k.unpair.2.unpair.2) hc
      have hr := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2.unpair.2) hc
      simp [checkingStep, numericCheck, hp, hc, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem numericCheck_proofTree (accept : Sentence → Bool)
    (p : ProofTree (language Nat)) : numericCheck accept p.numericTree.code = check accept p := by
  induction p <;> simp_all [ProofTree.numericTree, NumericTree.code, numericCheck, leafCheck,
    kRule, sRule, classicalRule, allElimRule, allDistRule, vacuousRule, eqSubstRule,
    mpResult, generalizeResult, check, Nat.unpair_pair, Encodable.encodek]

theorem leafCheck_derivation (accept : Sentence → Bool) (tag payload : Nat)
    {φ : Formula} (h : leafCheck accept tag payload = some φ) :
    Derivation {σ | accept σ = true} φ := by
  by_cases h0 : tag = 0
  · have hb : (Encodable.decode (α := Sentence) payload).bind (fun σ =>
        if accept σ then some (sentenceFormula σ) else none) = some φ := by
      simpa [leafCheck, h0] using h
    obtain ⟨σ, _, hs⟩ := Option.bind_eq_some_iff.mp hb
    split at hs
    next ha =>
      cases Option.some.inj hs
      exact .theory σ ha
    next => cases hs
  by_cases h1 : tag = 1
  · have hb : (Encodable.decode (α := Formula × Formula) payload).map kRule = some φ := by
      simpa [leafCheck, h0, h1] using h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hb
    cases hp
    exact .logical (.k p.1 p.2)
  by_cases h2 : tag = 2
  · have hb : (Encodable.decode (α := Formula × (Formula × Formula)) payload).map sRule = some φ := by
      simpa [leafCheck, h0, h1, h2] using h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hb
    cases hp
    exact .logical (.s p.1 p.2.1 p.2.2)
  by_cases h3 : tag = 3
  · have hb : (Encodable.decode (α := Formula × Formula) payload).map classicalRule = some φ := by
      simpa [leafCheck, h0, h1, h2, h3] using h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hb
    cases hp
    exact .logical (.classical p.1 p.2)
  by_cases h4 : tag = 4
  · have hb : (Encodable.decode (α := Nat × (Term × Formula)) payload).map allElimRule = some φ := by
      simpa [leafCheck, h0, h1, h2, h3, h4] using h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hb
    cases hp
    exact .logical (.allElim p.1 p.2.1 p.2.2)
  by_cases h5 : tag = 5
  · have hb : (Encodable.decode (α := Nat × (Formula × Formula)) payload).map allDistRule = some φ := by
      simpa [leafCheck, h0, h1, h2, h3, h4, h5] using h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hb
    cases hp
    exact .logical (.allDist p.1 p.2.1 p.2.2)
  by_cases h6 : tag = 6
  · have hb : (Encodable.decode (α := Nat × Formula) payload).bind vacuousRule = some φ := by
      simpa [leafCheck, h0, h1, h2, h3, h4, h5, h6] using h
    obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp hb
    unfold vacuousRule at hp
    split at hp
    next hx =>
      cases Option.some.inj hp
      exact .logical (.vacuous p.1 p.2 hx)
    next => cases hp
  by_cases h7 : tag = 7
  · have hb : (Encodable.decode (α := Term) payload).map (fun t => t.equal t) = some φ := by
      simpa [leafCheck, h0, h1, h2, h3, h4, h5, h6, h7] using h
    obtain ⟨t, _, ht⟩ := Option.map_eq_some_iff.mp hb
    cases ht
    exact .logical (.eqRefl t)
  by_cases h8 : tag = 8
  · have hb : (Encodable.decode (α := Nat × (Term × (Term × Formula))) payload).map eqSubstRule =
        some φ := by
      simpa [leafCheck, h0, h1, h2, h3, h4, h5, h6, h7, h8] using h
    obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hb
    cases hp
    exact .logical (.eqSubst p.1 p.2.1 p.2.2.1 p.2.2.2)
  simp [leafCheck, h0, h1, h2, h3, h4, h5, h6, h7, h8] at h

private theorem mpResult_derivation (accept : Sentence → Bool) (payload : Nat)
    (p q : Option Formula)
    (hp : ∀ φ, p = some φ → Derivation {σ | accept σ = true} φ)
    (hq : ∀ φ, q = some φ → Derivation {σ | accept σ = true} φ)
    {φ : Formula} (h : mpResult payload p q = some φ) :
    Derivation {σ | accept σ = true} φ := by
  obtain ⟨labels, _, hl⟩ := Option.bind_eq_some_iff.mp h
  split at hl
  next hc =>
    cases Option.some.inj hl
    exact .mp (hp _ hc.1) (hq _ hc.2)
  next => cases hl

private theorem generalizeResult_derivation (accept : Sentence → Bool) (payload : Nat)
    (p : Option Formula)
    (hp : ∀ φ, p = some φ → Derivation {σ | accept σ = true} φ)
    {φ : Formula} (h : generalizeResult payload p = some φ) :
    Derivation {σ | accept σ = true} φ := by
  obtain ⟨labels, _, hl⟩ := Option.bind_eq_some_iff.mp h
  split at hl
  next hc =>
    cases Option.some.inj hl
    exact .generalize labels.1 (hp _ hc)
  next => cases hl

theorem numericCheck_derivation (accept : Sentence → Bool) (c : Nat) :
    ∀ φ, numericCheck accept c = some φ → Derivation {σ | accept σ = true} φ := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    cases c with
    | zero => simp [numericCheck]
    | succ k =>
      intro φ hφ
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hc := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2) hp
      have hl := lt_of_le_of_lt (Nat.unpair_left_le k.unpair.2.unpair.2) hc
      have hr := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2.unpair.2) hc
      by_cases h9 : k.unpair.1 = 9
      · apply mpResult_derivation accept k.unpair.2.unpair.1
          (numericCheck accept k.unpair.2.unpair.2.unpair.1)
          (numericCheck accept k.unpair.2.unpair.2.unpair.2) (ih _ hl) (ih _ hr)
        simpa [numericCheck, h9] using hφ
      by_cases h10 : k.unpair.1 = 10
      · apply generalizeResult_derivation accept k.unpair.2.unpair.1
          (numericCheck accept k.unpair.2.unpair.2) (ih _ hc)
        simpa [numericCheck, h9, h10] using hφ
      apply leafCheck_derivation accept k.unpair.1 k.unpair.2
      simpa [numericCheck, h9, h10] using hφ

theorem exists_numericCheck_iff_derivation (accept : Sentence → Bool) (φ : Formula) :
    (∃ c, numericCheck accept c = some φ) ↔ Derivation {σ | accept σ = true} φ := by
  constructor
  · rintro ⟨c, hc⟩
    exact numericCheck_derivation accept c φ hc
  · intro h
    obtain ⟨p, hp⟩ := h.checked
    exact ⟨p.numericTree.code, by simpa only [numericCheck_proofTree] using hp⟩

theorem exists_numericCheck_iff_checkCode (accept : Sentence → Bool) (φ : Formula) :
    (∃ c, numericCheck accept c = some φ) ↔ (∃ c, checkCode accept c = some φ) := by
  rw [exists_numericCheck_iff_derivation, exists_checkCode_iff, checked_iff_derivation]

def finiteAccept (premises : List Sentence) (σ : Sentence) : Bool := decide (σ ∈ premises)

theorem finiteAccept_primrec (premises : List Sentence) : Primrec (finiteAccept premises) := by
  have he : PrimrecRel (fun σ τ : Sentence => σ = τ) := Primrec.eq
  have hp := he.exists_mem_list.comp (Primrec.const premises) Primrec.id
  exact hp.decide.of_eq (fun σ => by simp [finiteAccept])

def checkFinite (premises : List Sentence) : Nat → Option Formula := numericCheck (finiteAccept premises)

theorem checkFinite_primrec (premises : List Sentence) : Primrec (checkFinite premises) :=
  numericCheck_primrec (finiteAccept_primrec premises)

theorem exists_checkFinite_iff_derivation (premises : List Sentence) (φ : Formula) :
    (∃ c, checkFinite premises c = some φ) ↔ Derivation {σ | σ ∈ premises} φ := by
  simpa [checkFinite, finiteAccept] using
    exists_numericCheck_iff_derivation (finiteAccept premises) φ

theorem checkFinite_acceptance_primrec (premises : List Sentence) :
    PrimrecRel (fun (c : Nat) (φ : Formula) => checkFinite premises c = some φ) :=
  Primrec.eq.comp ((checkFinite_primrec premises).comp Primrec.fst)
    (Primrec.option_some.comp Primrec.snd)

def acceptsFinite (premises : List Sentence) (target proof : Nat) : Bool :=
  ((checkFinite premises proof).map (fun φ => NativeFormula.code φ == target)).getD false

theorem acceptsFinite_primrec (premises : List Sentence) : Primrec₂ (acceptsFinite premises) := by
  have hd := (checkFinite_primrec premises).comp (Primrec.snd : Primrec (Prod.snd : Nat × Nat → _))
  have hc : Primrec (fun p : (Nat × Nat) × Formula => NativeFormula.code p.2 == p.1.1) :=
    Primrec.beq.comp ((NativeFormula.code_primrec 0).comp Primrec.snd)
    (Primrec.fst.comp Primrec.fst)
  exact (Primrec.option_getD.comp (hd.option_map hc.to₂) (Primrec.const false)).to₂

theorem acceptsFinite_code_iff (premises : List Sentence) (φ : Formula) (proof : Nat) :
    acceptsFinite premises (NativeFormula.code φ) proof = true ↔ checkFinite premises proof = some φ := by
  cases h : checkFinite premises proof with
  | none => simp [acceptsFinite, h]
  | some ψ =>
    simp only [acceptsFinite, h, Option.map_some, Option.getD_some, Nat.beq_eq_true_eq]
    constructor
    · intro hc
      exact congrArg some (NativeFormula.code_injective hc)
    · intro hφ
      exact congrArg NativeFormula.code (Option.some.inj hφ)

theorem exists_acceptsFinite_iff_derivation (premises : List Sentence) (φ : Formula) :
    (∃ proof, acceptsFinite premises (NativeFormula.code φ) proof = true) ↔ Derivation {σ | σ ∈ premises} φ := by
  simp only [acceptsFinite_code_iff]
  exact exists_checkFinite_iff_derivation premises φ

variable {A : Type} [Primcodable A]

theorem leafCheck_joint_primrec {accept : A → Sentence → Bool} (ha : Primrec₂ accept) :
    Primrec (fun p : (A × Nat) × Nat => leafCheck (accept p.1.1) p.1.2 p.2) := by
  have ht := (Primrec.snd.comp Primrec.fst : Primrec (fun p : (A × Nat) × Nat => p.1.2))
  have hp := (Primrec.snd : Primrec (Prod.snd : (A × Nat) × Nat → _))
  have hs : Primrec (fun p : (A × Nat) × Nat => (Encodable.decode (α := Sentence) p.2).bind
      (fun σ => if accept p.1.1 σ then some (sentenceFormula σ) else none)) :=
    (Primrec.decode.comp hp).option_bind
      (Primrec.ite (Primrec.eq.comp
        (ha.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd) (Primrec.const true))
        (Primrec.option_some.comp (NativeClosedLabels.sentenceFormula_primrec.comp Primrec.snd))
        (Primrec.const none)).to₂
  have hf := (leafCheck_primrec (Primrec.const false)).comp ht hp
  have h := (Primrec.beq.comp ht (Primrec.const 0)).cond hs hf
  exact h.of_eq (by
    rintro ⟨⟨a, tag⟩, payload⟩
    by_cases ht : tag = 0 <;> simp [leafCheck, ht])

private theorem checkingStep_joint_primrec {accept : A → Sentence → Bool}
    (ha : Primrec₂ accept) :
    Primrec₂ (fun a h => checkingStep (accept a) h) := by
  have hn := Primrec.list_length.comp
    (Primrec.snd : Primrec (Prod.snd : A × List (Option Formula) → _))
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hc := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hcp := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hcq := Primrec.snd.comp (Primrec.unpair.comp hc)
  have get (f : A × List (Option Formula) → Nat) (hf : Primrec f) :
      Primrec (fun p : A × List (Option Formula) => p.2[f p]?.getD none) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const none)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const none)
    ((Primrec.beq.comp ht (Primrec.const 9)).cond
      (mpResult_primrec.comp (hl.pair ((get _ hcp).pair (get _ hcq))))
      ((Primrec.beq.comp ht (Primrec.const 10)).cond
        (generalizeResult_primrec.comp hl (get _ hc))
        ((leafCheck_joint_primrec ha).comp ((Primrec.fst.pair ht).pair hp))))).to₂

theorem numericCheck_joint_primrec {accept : A → Sentence → Bool} (ha : Primrec₂ accept) :
    Primrec₂ (fun a c => numericCheck (accept a) c) := by
  have hg := Primrec.option_some.comp₂ (checkingStep_joint_primrec ha)
  exact Primrec.nat_strong_rec (fun a c => numericCheck (accept a) c) hg (by
    intro a c
    cases c with
    | zero => simp [checkingStep, numericCheck]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hc := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2) hp
      have hl := lt_of_le_of_lt (Nat.unpair_left_le k.unpair.2.unpair.2) hc
      have hr := lt_of_le_of_lt (Nat.unpair_right_le k.unpair.2.unpair.2) hc
      simp [checkingStep, numericCheck, hp, hc, hl, hr])

theorem finiteAccept_joint_primrec : Primrec₂ finiteAccept := by
  have he : PrimrecRel (fun σ τ : Sentence => σ = τ) := Primrec.eq
  have h := he.exists_mem_list
  exact h.decide.of_eq (fun premises σ => by simp [finiteAccept])

theorem checkFinite_joint_primrec : Primrec₂ checkFinite :=
  numericCheck_joint_primrec finiteAccept_joint_primrec

theorem acceptsFinite_joint_primrec :
    Primrec (fun p : (List Sentence × Nat) × Nat => acceptsFinite p.1.1 p.1.2 p.2) := by
  have hd : Primrec (fun p : (List Sentence × Nat) × Nat => checkFinite p.1.1 p.2) :=
    checkFinite_joint_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hc : Primrec (fun p : ((List Sentence × Nat) × Nat) × Formula =>
      NativeFormula.code p.2 == p.1.1.2) :=
    Primrec.beq.comp ((NativeFormula.code_primrec 0).comp Primrec.snd)
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.option_getD.comp (hd.option_map hc.to₂) (Primrec.const false)

end Alexander313.Delta.NativeProofChecker
