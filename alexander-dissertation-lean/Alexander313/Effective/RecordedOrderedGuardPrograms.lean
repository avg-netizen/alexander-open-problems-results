import Alexander313.Effective.RecordedGuardPrograms
import Alexander313.Effective.RecordedOrder

/-!
# Positive guard certificates for an executing label-order Program

Every strict comparison of labels is a positive computation of the supplied
order Program. Chains still have exactly k+1 points in the actual marker set,
and every forward pair requires both order and R₂ computations. Each whole
support R₁ requirement also requires its own order computation. One cutoff
per certificate suffices by taking the finite maximum of the two runtimes.

The semantic targets are the existing `GuardChainIn`, `GuardRequirements.Holds`
and `Formula.MainGuarded` under `Program.orderLT order`. No numerical ordering
of label codes, order law, ordinal interpretation or guard-effectivity premise
is used. Open recorded syntax remains allowed in this guard subchecker.
-/

noncomputable section

namespace Alexander313.OrderedRecordedGuardProgram

open RecordedFormula
open RecordedBackgroundProgram (positive positive_primrec positive_iff)
open RecordedGuardProgram (allCheck allCheck_iff allCheck_primrec anyCheck anyCheck_iff
  anyCheck_primrec forwardPairs forwardPairs_primrec forwardPairs_exact positive_mono
  finite_positive finite_cover)

def edgeRunCheck (order edge : Program) (cutoff : Nat) (q : Nat × Nat) : Bool :=
  positive cutoff order (Nat.pair q.1 q.2) && positive cutoff edge (Nat.pair q.1 q.2)

theorem edgeRunCheck_primrec :
    Primrec (fun p : ((Program × Program) × Nat) × (Nat × Nat) =>
      edgeRunCheck p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hp : Primrec (fun p : ((Program × Program) × Nat) × (Nat × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun p : ((Program × Program) × Nat) × (Nat × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hq : Primrec (fun p : ((Program × Program) × Nat) × (Nat × Nat) =>
      Nat.pair p.2.1 p.2.2) := Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp
    (positive_primrec.comp ((hk.pair (Primrec.fst.comp hp)).pair hq))
    (positive_primrec.comp ((hk.pair (Primrec.snd.comp hp)).pair hq))

@[simp] theorem edgeRunCheck_iff (order edge : Program) (cutoff : Nat) (q : Nat × Nat) :
    edgeRunCheck order edge cutoff q = true ↔
      positive cutoff order (Nat.pair q.1 q.2) = true ∧
        positive cutoff edge (Nat.pair q.1 q.2) = true := by
  simp only [edgeRunCheck, Bool.and_eq_true]

theorem edgeRunCheck_sound {order edge : Program} {cutoff : Nat} {q : Nat × Nat}
    (h : edgeRunCheck order edge cutoff q = true) :
    order.domain (Nat.pair q.1 q.2) ∧ edge.domain (Nat.pair q.1 q.2) := by
  obtain ⟨ho, he⟩ := (edgeRunCheck_iff _ _ _ _).mp h
  exact ⟨(positive_iff _ _).mp ⟨cutoff, ho⟩, (positive_iff _ _).mp ⟨cutoff, he⟩⟩

theorem edgeRunCheck_complete {order edge : Program} {q : Nat × Nat}
    (h : order.domain (Nat.pair q.1 q.2) ∧ edge.domain (Nat.pair q.1 q.2)) :
    ∃ cutoff, edgeRunCheck order edge cutoff q = true := by
  obtain ⟨k, hk⟩ := (positive_iff _ _).mpr h.1
  obtain ⟨l, hl⟩ := (positive_iff _ _).mpr h.2
  exact ⟨max k l, (edgeRunCheck_iff _ _ _ _).mpr
    ⟨positive_mono (Nat.le_max_left _ _) hk, positive_mono (Nat.le_max_right _ _) hl⟩⟩

theorem finite_edgeRunCheck (order edge : Program) (L : List (Nat × Nat)) :
    (∃ cutoff, ∀ q ∈ L, edgeRunCheck order edge cutoff q = true) ↔
      ∀ q ∈ L, order.domain (Nat.pair q.1 q.2) ∧ edge.domain (Nat.pair q.1 q.2) := by
  constructor
  · rintro ⟨cutoff, h⟩ q hq
    exact edgeRunCheck_sound (h q hq)
  · intro h
    have ho : ∀ n ∈ L.map (fun q => Nat.pair q.1 q.2), order.domain n := by
      intro n hn
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
      exact (h q hq).1
    have he : ∀ n ∈ L.map (fun q => Nat.pair q.1 q.2), edge.domain n := by
      intro n hn
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
      exact (h q hq).2
    obtain ⟨k, hk⟩ := (finite_positive order _).mpr ho
    obtain ⟨l, hl⟩ := (finite_positive edge _).mpr he
    refine ⟨max k l, ?_⟩
    intro q hq
    have hm : Nat.pair q.1 q.2 ∈ L.map (fun p => Nat.pair p.1 p.2) :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    exact (edgeRunCheck_iff _ _ _ _).mpr
      ⟨positive_mono (Nat.le_max_left _ _) (hk _ hm),
        positive_mono (Nat.le_max_right _ _) (hl _ hm)⟩

def chainCheck (order edge : Program) (cutoff : Nat) (B : List Nat)
    (k ν : Nat) (tail : List Nat) : Bool :=
  decide (tail.length = k) &&
    (allCheck (listMember B) (ν :: tail) &&
      allCheck (edgeRunCheck order edge cutoff) (forwardPairs (ν :: tail)))

theorem chainCheck_primrec :
    Primrec (fun p : (((Program × Program) × Nat) × List Nat) × ((Nat × Nat) × List Nat) =>
      chainCheck p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2) := by
  have hp : Primrec (fun p : (((Program × Program) × Nat) × List Nat) × ((Nat × Nat) × List Nat) =>
      p.1.1) := Primrec.fst.comp Primrec.fst
  have hB : Primrec (fun p : (((Program × Program) × Nat) × List Nat) × ((Nat × Nat) × List Nat) =>
      p.1.2) := Primrec.snd.comp Primrec.fst
  have hq : Primrec (fun p : (((Program × Program) × Nat) × List Nat) × ((Nat × Nat) × List Nat) =>
      p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : (((Program × Program) × Nat) × List Nat) × ((Nat × Nat) × List Nat) =>
      p.2.2) := Primrec.snd.comp Primrec.snd
  have hL := Primrec.list_cons.comp (Primrec.snd.comp hq) ht
  have hedges := forwardPairs_primrec.comp hL
  exact Primrec.and.comp
    (Primrec.eq.comp (Primrec.list_length.comp ht) (Primrec.fst.comp hq)).decide
    (Primrec.and.comp ((allCheck_primrec _ listMember_primrec).comp hB hL)
      ((allCheck_primrec _ edgeRunCheck_primrec.to₂).comp hp hedges))

theorem chainCheck_iff (order edge : Program) (cutoff : Nat) (B : List Nat)
    (k ν : Nat) (tail : List Nat) :
    chainCheck order edge cutoff B k ν tail = true ↔
      tail.length = k ∧ (∀ μ ∈ ν :: tail, μ ∈ B) ∧
        ∀ q ∈ forwardPairs (ν :: tail), edgeRunCheck order edge cutoff q = true := by
  simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq, allCheck_iff, listMember]

theorem chainCheck_sound {order edge : Program} {cutoff : Nat} {B : List Nat}
    {k ν : Nat} {tail : List Nat} (h : chainCheck order edge cutoff B k ν tail = true) :
    letI : LT Nat := Program.orderLT order
    GuardChainIn (fun μ η => edge.domain (Nat.pair μ η)) B.toFinset k ν := by
  letI : LT Nat := Program.orderLT order
  obtain ⟨hl, hb, hr⟩ := (chainCheck_iff _ _ _ _ _ _ _).mp h
  refine ⟨tail, hl, ?_, ?_, ?_⟩
  · change (ν :: tail).Pairwise (fun μ η => order.domain (Nat.pair μ η))
    apply (forwardPairs_exact _ _).mp
    intro q hq
    exact (edgeRunCheck_sound (hr q hq)).1
  · apply (forwardPairs_exact _ _).mp
    intro q hq
    exact (edgeRunCheck_sound (hr q hq)).2
  · intro μ hμ
    exact List.mem_toFinset.mpr (hb μ hμ)

theorem chainCheck_complete {order edge : Program} {B : List Nat} {k ν : Nat}
    (h : letI : LT Nat := Program.orderLT order
      GuardChainIn (fun μ η => edge.domain (Nat.pair μ η)) B.toFinset k ν) :
    ∃ tail cutoff, chainCheck order edge cutoff B k ν tail = true := by
  letI : LT Nat := Program.orderLT order
  obtain ⟨tail, hl, ho, he, hb⟩ := h
  change (ν :: tail).Pairwise (fun μ η => order.domain (Nat.pair μ η)) at ho
  have hdom : ∀ q ∈ forwardPairs (ν :: tail),
      order.domain (Nat.pair q.1 q.2) ∧ edge.domain (Nat.pair q.1 q.2) := by
    intro q hq
    exact ⟨(forwardPairs_exact _ _).mpr ho q hq, (forwardPairs_exact _ _).mpr he q hq⟩
  obtain ⟨cutoff, hc⟩ := (finite_edgeRunCheck order edge _).mpr hdom
  refine ⟨tail, cutoff, (chainCheck_iff _ _ _ _ _ _ _).mpr ⟨hl, ?_, hc⟩⟩
  intro μ hμ
  exact List.mem_toFinset.mp (hb μ hμ)

abbrev ChainWitness := RecordedGuardProgram.ChainWitness
abbrev EdgeWitness := RecordedGuardProgram.EdgeWitness
abbrev Witness := RecordedGuardProgram.Witness
abbrev Parameters := (List Nat × List Nat) × (Program × (Program × Program))

def chainWitnessCheck (p : Parameters) (q : Nat × Nat) (w : ChainWitness) : Bool :=
  decide (w.1 = q) && chainCheck p.2.1 p.2.2.2 w.2.2 p.1.2 q.1 q.2 w.2.1

def edgeWitnessCheck (programs : Program × Program) (q : Nat × Nat) (w : EdgeWitness) : Bool :=
  decide (w.1 = q) && edgeRunCheck programs.1 programs.2 w.2 q

theorem chainWitnessCheck_primrec :
    Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness =>
      chainWitnessCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness => p.2) := Primrec.snd
  have ho := Primrec.fst.comp (Primrec.snd.comp hp)
  have he := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have hB := Primrec.snd.comp (Primrec.fst.comp hp)
  have ht := Primrec.fst.comp (Primrec.snd.comp hw)
  have hk := Primrec.snd.comp (Primrec.snd.comp hw)
  exact Primrec.and.comp (Primrec.eq.comp (Primrec.fst.comp hw) hq).decide
    (chainCheck_primrec.comp ((((ho.pair he).pair hk).pair hB).pair (hq.pair ht)))

theorem edgeWitnessCheck_primrec :
    Primrec (fun p : ((Program × Program) × (Nat × Nat)) × EdgeWitness =>
      edgeWitnessCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : ((Program × Program) × (Nat × Nat)) × EdgeWitness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : ((Program × Program) × (Nat × Nat)) × EdgeWitness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : ((Program × Program) × (Nat × Nat)) × EdgeWitness => p.2) := Primrec.snd
  exact Primrec.and.comp (Primrec.eq.comp (Primrec.fst.comp hw) hq).decide
    (edgeRunCheck_primrec.comp ((hp.pair (Primrec.snd.comp hw)).pair hq))

def condition (p : Parameters) (r : GuardRequirements Nat) (w : Witness) : Bool :=
  allCheck (fun q => anyCheck (chainWitnessCheck p q) w.1) r.1 &&
    allCheck (fun q => anyCheck (edgeWitnessCheck (p.2.1, p.2.2.1) q) w.2) r.2

theorem condition_primrec :
    Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness =>
      condition p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness => p.2) := Primrec.snd
  have hchain := anyCheck_primrec _ chainWitnessCheck_primrec.to₂
  have hedge := anyCheck_primrec _ edgeWitnessCheck_primrec.to₂
  have hct : Primrec₂ (fun (s : Parameters × List ChainWitness) (q : Nat × Nat) =>
      anyCheck (chainWitnessCheck s.1 q) s.2) :=
    (hchain.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have het : Primrec₂ (fun (s : (Program × Program) × List EdgeWitness) (q : Nat × Nat) =>
      anyCheck (edgeWitnessCheck s.1 q) s.2) :=
    (hedge.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have ho := Primrec.fst.comp (Primrec.snd.comp hp)
  have he := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have result := Primrec.and.comp
    ((allCheck_primrec _ hct).comp (hp.pair (Primrec.fst.comp hw)) (Primrec.fst.comp hr))
    ((allCheck_primrec _ het).comp ((ho.pair he).pair (Primrec.snd.comp hw))
      (Primrec.snd.comp hr))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : Parameters) (r : GuardRequirements Nat) :
    (∃ w, condition p r w = true) ↔
      (letI : LT Nat := Program.orderLT p.2.1
       GuardRequirements.Holds (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.2.toFinset r) := by
  letI : LT Nat := Program.orderLT p.2.1
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hc, he⟩ := Bool.and_eq_true_iff.mp hw
    constructor
    · intro q hq
      obtain ⟨v, _, hv⟩ := (anyCheck_iff _ _).mp ((allCheck_iff _ _).mp hc q hq)
      exact chainCheck_sound (Bool.and_eq_true_iff.mp hv).2
    · intro q hq
      obtain ⟨v, _, hv⟩ := (anyCheck_iff _ _).mp ((allCheck_iff _ _).mp he q hq)
      exact edgeRunCheck_sound (Bool.and_eq_true_iff.mp hv).2
  · intro h
    have hc : ∀ q ∈ r.1, ∃ v, chainWitnessCheck p q v = true := by
      intro q hq
      obtain ⟨tail, cutoff, ht⟩ :=
        chainCheck_complete (order := p.2.1) (edge := p.2.2.2) (h.1 q hq)
      exact ⟨(q, (tail, cutoff)), by simp [chainWitnessCheck, ht]⟩
    have he : ∀ q ∈ r.2, ∃ v, edgeWitnessCheck (p.2.1, p.2.2.1) q v = true := by
      intro q hq
      obtain ⟨cutoff, ht⟩ := edgeRunCheck_complete (order := p.2.1) (edge := p.2.2.1) (h.2 q hq)
      exact ⟨(q, cutoff), by simp [edgeWitnessCheck, ht]⟩
    obtain ⟨C, hC⟩ := finite_cover r.1 _ hc
    obtain ⟨D, hD⟩ := finite_cover r.2 _ he
    refine ⟨(C, D), ?_⟩
    simpa only [condition, Bool.and_eq_true, allCheck_iff, anyCheck_iff]
      using And.intro hC hD

theorem mainRequirementsCode_exact (p : Parameters) (φ : Syntax) :
    letI : LT Nat := Program.orderLT p.2.1
    GuardRequirements.Holds (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
      (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.2.toFinset
        (mainRequirementsCode p.1.1 (φ.code RecordedHead.code)) ↔
      φ.MainGuarded (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset := by
  letI : LT Nat := Program.orderLT p.2.1
  rw [RecordedFormula.mainRequirementsCode_code]
  exact Formula.mainGuardRequirements_exact _ _ _ _ _

def defaultParameters : Parameters :=
  (([], []), (Nat.Partrec.Code.zero, (Nat.Partrec.Code.zero, Nat.Partrec.Code.zero)))
def decodeParameters (n : Nat) : Parameters := (Encodable.decode (α := Parameters) n).getD defaultParameters
def decodeWitness (n : Nat) : Witness := (Encodable.decode (α := Witness) n).getD ([], [])
def decodeFormula (n : Nat) : Syntax := (Encodable.decode (α := Syntax) n).getD .falsum

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (([], []) : Witness))

theorem decodeFormula_primrec : Primrec decodeFormula :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (.falsum : Syntax))

@[simp] theorem decodeParameters_encode (p : Parameters) :
    decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp only [decodeWitness, Encodable.encodek, Option.getD_some]

@[simp] theorem decodeFormula_code (φ : Syntax) :
    decodeFormula (φ.code RecordedHead.code) = φ := by
  rw [← RecordedFormula.encode_eq_code]
  simp only [decodeFormula, Encodable.encodek, Option.getD_some]

def check (key query certificate : Nat) : Bool :=
  let p := decodeParameters key
  (query == (decodeFormula query).code RecordedHead.code) &&
    condition p (mainRequirementsCode p.1.1 query) (decodeWitness certificate)

theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Nat × Nat) × Nat => decodeParameters p.1.1) :=
    decodeParameters_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have result := Primrec.and.comp (Primrec.beq.comp hq (code_primrec.comp (decodeFormula_primrec.comp hq)))
    (condition_primrec.comp
      ((hp.pair (mainRequirementsCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp hp)) hq)).pair
        (decodeWitness_primrec.comp Primrec.snd)))
  exact result.of_eq (fun _ => by simp only [check, Bool.beq_eq_decide_eq])

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ certificate, check key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (p : Parameters) (φ : Syntax) :
    (evaluation (Encodable.encode p) (φ.code RecordedHead.code)).Dom ↔
      (letI : LT Nat := Program.orderLT p.2.1
       φ.MainGuarded (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset) := by
  letI : LT Nat := Program.orderLT p.2.1
  rw [evaluation_domain, ← mainRequirementsCode_exact p φ, ← condition_correct]
  constructor
  · rintro ⟨certificate, hc⟩
    exact ⟨decodeWitness certificate, by
      simpa only [check, decodeParameters_encode, decodeFormula_code,
        beq_self_eq_true, Bool.true_and] using hc⟩
  · rintro ⟨w, hw⟩
    exact ⟨Encodable.encode w, by
      simp only [check, decodeParameters_encode, decodeFormula_code,
        decodeWitness_encode, beq_self_eq_true, Bool.true_and, hw]⟩

theorem evaluation_only_formulas (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
      (letI : LT Nat := Program.orderLT (decodeParameters key).2.1
       φ.MainGuarded (fun μ ν => (decodeParameters key).2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => (decodeParameters key).2.2.2.domain (Nat.pair μ ν))
         (decodeParameters key).1.1.toFinset (decodeParameters key).1.2.toFinset) := by
  letI : LT Nat := Program.orderLT (decodeParameters key).2.1
  obtain ⟨certificate, hc⟩ := (evaluation_domain _ _).mp h
  have he : query = (decodeFormula query).code RecordedHead.code :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).1
  refine ⟨decodeFormula query, he, ?_⟩
  rw [← mainRequirementsCode_exact (decodeParameters key) (decodeFormula query), ← he]
  exact (condition_correct _ _).mp ⟨decodeWitness certificate, (Bool.and_eq_true_iff.mp hc).2⟩

theorem evaluation_raw_exact (key query : Nat) :
    (evaluation key query).Dom ↔
      ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
        (letI : LT Nat := Program.orderLT (decodeParameters key).2.1
         φ.MainGuarded (fun μ ν => (decodeParameters key).2.2.1.domain (Nat.pair μ ν))
           (fun μ ν => (decodeParameters key).2.2.2.domain (Nat.pair μ ν))
           (decodeParameters key).1.1.toFinset (decodeParameters key).1.2.toFinset) := by
  constructor
  · exact evaluation_only_formulas key query
  · rintro ⟨φ, rfl, hφ⟩
    have hr := (mainRequirementsCode_exact (decodeParameters key) φ).mpr hφ
    obtain ⟨w, hw⟩ := (condition_correct _ _).mpr hr
    exact (evaluation_domain _ _).mpr ⟨Encodable.encode w, by
      simp only [check, decodeFormula_code, decodeWitness_encode,
        beq_self_eq_true, Bool.true_and, hw]⟩

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p, ∀ φ : Syntax, (compiler p).domain (φ.code RecordedHead.code) ↔
      (letI : LT Nat := Program.orderLT p.2.1
       φ.MainGuarded (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
         (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset)) ∧
    (∀ p query, (compiler p).domain query ↔
      ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
        (letI : LT Nat := Program.orderLT p.2.1
         φ.MainGuarded (fun μ ν => p.2.2.1.domain (Nat.pair μ ν))
           (fun μ ν => p.2.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset)) := by
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
    have h := evaluation_raw_exact (Encodable.encode p) query
    rw [decodeParameters_encode] at h
    exact h

theorem semantic_compiler_exists (O R₁ R₂ : Nat → Nat → Prop) (E B : List Nat)
    (order c₁ c₂ : Program) (ho : ∀ μ ν, order.domain (Nat.pair μ ν) ↔ O μ ν)
    (h₁ : ∀ μ ν, c₁.domain (Nat.pair μ ν) ↔ R₁ μ ν)
    (h₂ : ∀ μ ν, c₂.domain (Nat.pair μ ν) ↔ R₂ μ ν) :
    ∃ c : Program, (letI : LT Nat := ⟨O⟩
      ∀ φ : Syntax, c.domain (φ.code RecordedHead.code) ↔ φ.MainGuarded R₁ R₂ E.toFinset B.toFinset) := by
  obtain ⟨compiler, _, hc, _⟩ := compiler_exists
  have heO : (fun μ ν => order.domain (Nat.pair μ ν)) = O :=
    funext (fun μ => funext (fun ν => propext (ho μ ν)))
  have he₁ : (fun μ ν => c₁.domain (Nat.pair μ ν)) = R₁ :=
    funext (fun μ => funext (fun ν => propext (h₁ μ ν)))
  have he₂ : (fun μ ν => c₂.domain (Nat.pair μ ν)) = R₂ :=
    funext (fun μ => funext (fun ν => propext (h₂ μ ν)))
  subst O R₁ R₂
  exact ⟨compiler ((E, B), (order, (c₁, c₂))), hc ((E, B), (order, (c₁, c₂)))⟩

end Alexander313.OrderedRecordedGuardProgram
