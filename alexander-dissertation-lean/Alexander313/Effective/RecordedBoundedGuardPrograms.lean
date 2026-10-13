import Alexander313.Effective.HereditaryOrdinalFormation
import Alexander313.Effective.RecordedOrderedGuardPrograms
import Alexander313.RecordedGuardRoom

/-!
# Executing finite guard room below an actual ordinal-code cut

Every written chain point, including its base, positively runs the actual
union-order Program against the admitted cut. Forward chain pairs use the
existing ordered guard checker and the supplied R₂ Program; support edges use
the same actual order and the supplied R₁ Program. Literal formula labels and
the cut pass the unchanged original union checker. No ordinary-order procedure,
finite guard set or bounded-chain existence is supplied as an oracle.

The edge Programs remain explicit. Their identification with genuine ordinal
relations is a separate displayed contract, not an identification with natural
code order or a claim that Wilken's edge algorithms have been constructed.
Uncompiled.
-/

noncomputable section

namespace Alexander313.RecordedBoundedGuardProgram

open RecordedFormula
open Wilken.RelativeTerm.Hereditary
open HereditaryOrdinalFormation (ordinalOrder ordinalOrder_domain orderLT_iff
  Supported labelCheck labelCheck_primrec labelCheck_exact)
open RecordedBackgroundProgram (positive positive_primrec positive_iff)
open RecordedGuardProgram (allCheck allCheck_iff allCheck_primrec anyCheck anyCheck_iff
  anyCheck_primrec forwardPairs forwardPairs_primrec forwardPairs_exact positive_mono
  finite_positive finite_cover)
open OrderedRecordedGuardProgram (edgeRunCheck edgeRunCheck_primrec edgeRunCheck_sound
  finite_edgeRunCheck)

def roomRunCheck (δ cutoff : Nat) (points : List Nat) : Bool :=
  allCheck (fun μ => positive cutoff ordinalOrder (Nat.pair μ δ)) points

theorem roomRunCheck_primrec : Primrec
    (fun p : (Nat × Nat) × List Nat => roomRunCheck p.1.1 p.1.2 p.2) := by
  have ht : Primrec₂ (fun p : Nat × Nat => fun μ : Nat =>
      positive p.2 ordinalOrder (Nat.pair μ p.1)) :=
    (positive_primrec.comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.const ordinalOrder)).pair
        (Primrec₂.natPair.comp Primrec.snd (Primrec.fst.comp Primrec.fst)))).to₂
  exact allCheck_primrec _ ht

@[simp] theorem roomRunCheck_iff (δ cutoff : Nat) (points : List Nat) :
    roomRunCheck δ cutoff points = true ↔
      ∀ μ ∈ points, positive cutoff ordinalOrder (Nat.pair μ δ) = true :=
  allCheck_iff _ _

def chainCheck (edge : Program) (cutoff δ k ν : Nat) (tail : List Nat) : Bool :=
  OrderedRecordedGuardProgram.chainCheck ordinalOrder edge cutoff (ν :: tail) k ν tail &&
    roomRunCheck δ cutoff (ν :: tail)

theorem chainCheck_primrec : Primrec
    (fun p : ((Program × Nat) × Nat) × ((Nat × Nat) × List Nat) =>
      chainCheck p.1.1.1 p.1.1.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2) := by
  have he : Primrec (fun p : ((Program × Nat) × Nat) × ((Nat × Nat) × List Nat) =>
      p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun p : ((Program × Nat) × Nat) × ((Nat × Nat) × List Nat) =>
      p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hδ : Primrec (fun p : ((Program × Nat) × Nat) × ((Nat × Nat) × List Nat) =>
      p.1.2) := Primrec.snd.comp Primrec.fst
  have hq : Primrec (fun p : ((Program × Nat) × Nat) × ((Nat × Nat) × List Nat) =>
      p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : ((Program × Nat) × Nat) × ((Nat × Nat) × List Nat) =>
      p.2.2) := Primrec.snd.comp Primrec.snd
  have hL := Primrec.list_cons.comp (Primrec.snd.comp hq) ht
  exact Primrec.and.comp
    (OrderedRecordedGuardProgram.chainCheck_primrec.comp
      (((((Primrec.const ordinalOrder).pair he).pair hk).pair hL).pair (hq.pair ht)))
    (roomRunCheck_primrec.comp ((hδ.pair hk).pair hL))

theorem chainCheck_sound {edge : Program} {cutoff δ k ν : Nat} {tail : List Nat}
    (h : chainCheck edge cutoff δ k ν tail = true) :
    letI : LT Nat := Program.orderLT ordinalOrder
    BoundedGuardChain (fun μ η => edge.domain (Nat.pair μ η)) δ k ν := by
  letI : LT Nat := Program.orderLT ordinalOrder
  obtain ⟨hc, hb⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hl, _, hp⟩ := (OrderedRecordedGuardProgram.chainCheck_iff _ _ _ _ _ _ _).mp hc
  refine ⟨tail, hl, ?_, ?_, ?_⟩
  · change (ν :: tail).Pairwise (fun μ η => ordinalOrder.domain (Nat.pair μ η))
    apply (forwardPairs_exact _ _).mp
    intro q hq
    exact (edgeRunCheck_sound (hp q hq)).1
  · apply (forwardPairs_exact _ _).mp
    intro q hq
    exact (edgeRunCheck_sound (hp q hq)).2
  · intro μ hμ
    exact (positive_iff _ _).mp ⟨cutoff, (roomRunCheck_iff _ _ _).mp hb μ hμ⟩

theorem chainCheck_complete {edge : Program} {δ k ν : Nat}
    (h : letI : LT Nat := Program.orderLT ordinalOrder
      BoundedGuardChain (fun μ η => edge.domain (Nat.pair μ η)) δ k ν) :
    ∃ tail cutoff, chainCheck edge cutoff δ k ν tail = true := by
  letI : LT Nat := Program.orderLT ordinalOrder
  obtain ⟨tail, hl, ho, he, hb⟩ := h
  change (ν :: tail).Pairwise (fun μ η => ordinalOrder.domain (Nat.pair μ η)) at ho
  have hp : ∀ q ∈ forwardPairs (ν :: tail),
      ordinalOrder.domain (Nat.pair q.1 q.2) ∧ edge.domain (Nat.pair q.1 q.2) := by
    intro q hq
    exact ⟨(forwardPairs_exact _ _).mpr ho q hq, (forwardPairs_exact _ _).mpr he q hq⟩
  obtain ⟨s, hs⟩ := (finite_edgeRunCheck ordinalOrder edge _).mpr hp
  have hroom : ∀ query ∈ (ν :: tail).map (fun μ => Nat.pair μ δ), ordinalOrder.domain query := by
    intro query hquery
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hquery
    exact hb μ hμ
  obtain ⟨t, ht⟩ := (finite_positive ordinalOrder _).mpr hroom
  refine ⟨tail, max s t, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · apply (OrderedRecordedGuardProgram.chainCheck_iff _ _ _ _ _ _ _).mpr
    refine ⟨hl, fun μ hμ => hμ, ?_⟩
    intro q hq
    obtain ⟨horder, hedge⟩ := (OrderedRecordedGuardProgram.edgeRunCheck_iff _ _ _ _).mp (hs q hq)
    exact (OrderedRecordedGuardProgram.edgeRunCheck_iff _ _ _ _).mpr
      ⟨positive_mono (Nat.le_max_left _ _) horder, positive_mono (Nat.le_max_left _ _) hedge⟩
  · apply (roomRunCheck_iff _ _ _).mpr
    intro μ hμ
    exact positive_mono (Nat.le_max_right _ _) (ht _ (List.mem_map.mpr ⟨μ, hμ, rfl⟩))

abbrev ChainWitness := OrderedRecordedGuardProgram.ChainWitness
abbrev EdgeWitness := OrderedRecordedGuardProgram.EdgeWitness
abbrev Witness := OrderedRecordedGuardProgram.Witness
abbrev Parameters := (List Nat × Nat) × (Program × Program)

def chainWitnessCheck (p : Nat × Program) (q : Nat × Nat) (w : ChainWitness) : Bool :=
  decide (w.1 = q) && chainCheck p.2 w.2.2 p.1 q.1 q.2 w.2.1

theorem chainWitnessCheck_primrec : Primrec
    (fun p : ((Nat × Program) × (Nat × Nat)) × ChainWitness =>
      chainWitnessCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : ((Nat × Program) × (Nat × Nat)) × ChainWitness =>
      p.1.1) := Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : ((Nat × Program) × (Nat × Nat)) × ChainWitness =>
      p.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : ((Nat × Program) × (Nat × Nat)) × ChainWitness =>
      p.2) := Primrec.snd
  have ht := Primrec.fst.comp (Primrec.snd.comp hw)
  have hk := Primrec.snd.comp (Primrec.snd.comp hw)
  exact Primrec.and.comp (Primrec.eq.comp (Primrec.fst.comp hw) hq).decide
    (chainCheck_primrec.comp
      ((((Primrec.snd.comp hp).pair hk).pair (Primrec.fst.comp hp)).pair (hq.pair ht)))

def condition (p : Parameters) (r : GuardRequirements Nat) (w : Witness) : Bool :=
  unionCheck p.1.2 &&
    (allCheck (fun q => anyCheck (chainWitnessCheck (p.1.2, p.2.2) q) w.1) r.1 &&
      allCheck (fun q => anyCheck
        (OrderedRecordedGuardProgram.edgeWitnessCheck (ordinalOrder, p.2.1) q) w.2) r.2)

theorem condition_primrec : Primrec
    (fun p : (Parameters × GuardRequirements Nat) × Witness => condition p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness =>
      p.1.1) := Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness =>
      p.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness =>
      p.2) := Primrec.snd
  have hδ := Primrec.snd.comp (Primrec.fst.comp hp)
  have hc₁ := Primrec.fst.comp (Primrec.snd.comp hp)
  have hc₂ := Primrec.snd.comp (Primrec.snd.comp hp)
  have hchain := anyCheck_primrec _ chainWitnessCheck_primrec.to₂
  have hedge := anyCheck_primrec _ OrderedRecordedGuardProgram.edgeWitnessCheck_primrec.to₂
  have hct : Primrec₂ (fun s : (Nat × Program) × List ChainWitness => fun q : Nat × Nat =>
      anyCheck (chainWitnessCheck s.1 q) s.2) :=
    (hchain.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have het : Primrec₂ (fun s : (Program × Program) × List EdgeWitness => fun q : Nat × Nat =>
      anyCheck (OrderedRecordedGuardProgram.edgeWitnessCheck s.1 q) s.2) :=
    (hedge.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have result := Primrec.and.comp (Uniform.unionCheck_primrec.comp hδ)
    (Primrec.and.comp
      ((allCheck_primrec _ hct).comp ((hδ.pair hc₂).pair (Primrec.fst.comp hw)) (Primrec.fst.comp hr))
      ((allCheck_primrec _ het).comp (((Primrec.const ordinalOrder).pair hc₁).pair
        (Primrec.snd.comp hw)) (Primrec.snd.comp hr)))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : Parameters) (r : GuardRequirements Nat) :
    (∃ w, condition p r w = true) ↔ unionCheck p.1.2 = true ∧
      (letI : LT Nat := Program.orderLT ordinalOrder
       GuardRequirements.Bounded (fun μ ν => p.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.2.2.domain (Nat.pair μ ν)) p.1.2 r) := by
  letI : LT Nat := Program.orderLT ordinalOrder
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hδ, hc, he⟩ := by simpa only [condition, Bool.and_eq_true] using hw
    refine ⟨hδ, ?_, ?_⟩
    · intro q hq
      obtain ⟨v, _, hv⟩ := (anyCheck_iff _ _).mp ((allCheck_iff _ _).mp hc q hq)
      exact chainCheck_sound (Bool.and_eq_true_iff.mp hv).2
    · intro q hq
      obtain ⟨v, _, hv⟩ := (anyCheck_iff _ _).mp ((allCheck_iff _ _).mp he q hq)
      exact edgeRunCheck_sound (Bool.and_eq_true_iff.mp hv).2
  · rintro ⟨hδ, h⟩
    have hc : ∀ q ∈ r.1, ∃ v, chainWitnessCheck (p.1.2, p.2.2) q v = true := by
      intro q hq
      obtain ⟨tail, cutoff, ht⟩ := chainCheck_complete (h.1 q hq)
      exact ⟨(q, (tail, cutoff)), by simp [chainWitnessCheck, ht]⟩
    have he : ∀ q ∈ r.2, ∃ v,
        OrderedRecordedGuardProgram.edgeWitnessCheck (ordinalOrder, p.2.1) q v = true := by
      intro q hq
      obtain ⟨cutoff, ht⟩ := OrderedRecordedGuardProgram.edgeRunCheck_complete
        (order := ordinalOrder) (edge := p.2.1) (h.2 q hq)
      exact ⟨(q, cutoff), by simp [OrderedRecordedGuardProgram.edgeWitnessCheck, ht]⟩
    obtain ⟨C, hC⟩ := finite_cover r.1 _ hc
    obtain ⟨D, hD⟩ := finite_cover r.2 _ he
    refine ⟨(C, D), ?_⟩
    simpa only [condition, Bool.and_eq_true, hδ, true_and, allCheck_iff, anyCheck_iff] using And.intro hC hD

def defaultParameters : Parameters := (([], 0), (Nat.Partrec.Code.zero, Nat.Partrec.Code.zero))
def decodeParameters (n : Nat) : Parameters := (Encodable.decode (α := Parameters) n).getD defaultParameters
def decodeWitness (n : Nat) : Witness := (Encodable.decode (α := Witness) n).getD ([], [])
def decodeFormula (n : Nat) : Syntax := (Encodable.decode (α := Syntax) n).getD .falsum

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([], []))

theorem decodeFormula_primrec : Primrec decodeFormula :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (.falsum : Syntax))

@[simp] theorem decodeParameters_encode (p : Parameters) : decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp only [decodeWitness, Encodable.encodek, Option.getD_some]

@[simp] theorem decodeFormula_code (φ : Syntax) : decodeFormula (φ.code RecordedHead.code) = φ := by
  rw [← RecordedFormula.encode_eq_code]
  simp only [decodeFormula, Encodable.encodek, Option.getD_some]

def check (key query certificate : Nat) : Bool :=
  let p := decodeParameters key
  (query == (decodeFormula query).code RecordedHead.code) &&
    (labelCheck (decodeFormula query) &&
      condition p (mainRequirementsCode p.1.1 query) (decodeWitness certificate))

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Nat × Nat) × Nat => decodeParameters p.1.1) :=
    decodeParameters_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hφ := decodeFormula_primrec.comp hq
  have result := Primrec.and.comp (Primrec.beq.comp hq (code_primrec.comp hφ))
    (Primrec.and.comp (labelCheck_primrec.comp hφ)
      (condition_primrec.comp
        ((hp.pair (mainRequirementsCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp hp)) hq)).pair
          (decodeWitness_primrec.comp Primrec.snd))))
  exact result.of_eq (fun _ => by simp only [check, Bool.beq_eq_decide_eq])

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ certificate, check key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

def Target (p : Parameters) (φ : Syntax) : Prop :=
  Supported φ ∧ unionCheck p.1.2 = true ∧
    (letI : LT Nat := Program.orderLT ordinalOrder
     GuardRequirements.Bounded (fun μ ν => p.2.1.domain (Nat.pair μ ν))
       (fun μ ν => p.2.2.domain (Nat.pair μ ν)) p.1.2 (φ.mainGuardRequirements p.1.1.toFinset))

theorem evaluation_correct (p : Parameters) (φ : Syntax) :
    (evaluation (Encodable.encode p) (φ.code RecordedHead.code)).Dom ↔ Target p φ := by
  rw [evaluation_domain]
  constructor
  · rintro ⟨certificate, hc⟩
    have h : labelCheck φ = true ∧
        condition p (φ.mainGuardRequirements p.1.1.toFinset) (decodeWitness certificate) = true := by
      simpa [check, mainRequirementsCode_code] using hc
    exact ⟨(labelCheck_exact φ).mp h.1, (condition_correct _ _).mp ⟨_, h.2⟩⟩
  · rintro ⟨supported, hδ, bounded⟩
    obtain ⟨w, hw⟩ := (condition_correct _ _).mpr ⟨hδ, bounded⟩
    exact ⟨Encodable.encode w, by simp [check, mainRequirementsCode_code,
      (labelCheck_exact φ).mpr supported, hw]⟩

theorem evaluation_raw_exact (key query : Nat) : (evaluation key query).Dom ↔
    ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ Target (decodeParameters key) φ := by
  constructor
  · intro h
    obtain ⟨certificate, hc⟩ := (evaluation_domain _ _).mp h
    have he : query = (decodeFormula query).code RecordedHead.code :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).1
    refine ⟨decodeFormula query, he, ?_⟩
    have hp := (Bool.and_eq_true_iff.mp hc).2
    refine ⟨(labelCheck_exact _).mp (Bool.and_eq_true_iff.mp hp).1, ?_⟩
    apply (condition_correct _ _).mp
    refine ⟨decodeWitness certificate, ?_⟩
    rw [← mainRequirementsCode_code (decodeParameters key).1.1 (decodeFormula query), ← he]
    exact (Bool.and_eq_true_iff.mp hp).2
  · rintro ⟨φ, rfl, hs, hδ, hb⟩
    obtain ⟨w, hw⟩ := (condition_correct _ _).mpr ⟨hδ, hb⟩
    exact (evaluation_domain _ _).mpr ⟨Encodable.encode w, by
      simp [check, mainRequirementsCode_code, (labelCheck_exact φ).mpr hs, hw]⟩

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p φ, (compiler p).domain (φ.code RecordedHead.code) ↔ Target p φ) ∧
    (∀ p query, (compiler p).domain query ↔
      ∃ φ : Syntax, query = φ.code RecordedHead.code ∧ Target p φ) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Parameters → Program := fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : Parameters) (query : Nat) :
      (compiler p).eval query = evaluation (Encodable.encode p) query := by
    change (Nat.Partrec.Code.curry kernel (Encodable.encode p)).eval query = _
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
    simpa only [decodeParameters_encode] using evaluation_raw_exact (Encodable.encode p) query

end Alexander313.RecordedBoundedGuardProgram
