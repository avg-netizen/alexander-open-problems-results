import Alexander313.Effective.RecordedGuardFormation
import Alexander313.Effective.RecordedBackgroundPrograms

/-!
# Positive finite guard certificates and their executing Program

Each required chain names an actual tail of length k, with all k+1 points
in B, all forward order/edge pairs checked and a positive bounded R₂
computation. Every R₁ requirement has its own positive computation. The
whole extracted requirement lists are checked: omitted witnesses do not
truncate the test. This subchecker accepts literal recorded syntax, which
may be open; closedness is a separate full-generator test.

Nat labels use ordinary Nat order. Semantic edge relations are the domains
of the two supplied executing Programs; identifying them with Wilken's
relations still requires the unconstructed actual ordinal procedures.
-/

noncomputable section

namespace Alexander313.RecordedGuardProgram

open RecordedFormula
open RecordedBackgroundProgram (positive positive_primrec positive_iff)

def allCheck {α : Type} (test : α → Bool) (L : List α) : Bool :=
  L.foldr (fun x value => test x && value) true

def anyCheck {α : Type} (test : α → Bool) (L : List α) : Bool :=
  L.foldr (fun x value => test x || value) false

@[simp] theorem allCheck_iff {α : Type} (test : α → Bool) (L : List α) :
    allCheck test L = true ↔ ∀ x ∈ L, test x = true := by
  induction L <;> simp_all [allCheck]

@[simp] theorem anyCheck_iff {α : Type} (test : α → Bool) (L : List α) :
    anyCheck test L = true ↔ ∃ x ∈ L, test x = true := by
  induction L <;> simp_all [anyCheck]

theorem allCheck_primrec {α β : Type} [Primcodable α] [Primcodable β]
    (test : α → β → Bool) (ht : Primrec₂ test) :
    Primrec₂ (fun a L => allCheck (test a) L) :=
  (Primrec.list_foldr Primrec.snd (Primrec.const true)
    ((Primrec.and.comp
      (ht.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)).to₂

theorem anyCheck_primrec {α β : Type} [Primcodable α] [Primcodable β]
    (test : α → β → Bool) (ht : Primrec₂ test) :
    Primrec₂ (fun a L => anyCheck (test a) L) :=
  (Primrec.list_foldr Primrec.snd (Primrec.const false)
    ((Primrec.or.comp
      (ht.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)).to₂

def outgoing (x : Nat) (L : List Nat) : List (Nat × Nat) := L.map (fun y => (x, y))

theorem outgoing_primrec : Primrec₂ outgoing :=
  (Primrec.list_map Primrec.snd
    (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂)).to₂

def forwardPairsState (L : List Nat) : List Nat × List (Nat × Nat) :=
  L.foldr (fun x s => (x :: s.1, outgoing x s.1 ++ s.2)) ([], [])

@[simp] theorem forwardPairsState_first (L : List Nat) : (forwardPairsState L).1 = L := by
  induction L <;> simp_all [forwardPairsState]

def forwardPairs (L : List Nat) : List (Nat × Nat) := (forwardPairsState L).2

theorem forwardPairs_primrec : Primrec forwardPairs := by
  have hs : Primrec₂ (fun (_ : List Nat) (p : Nat × (List Nat × List (Nat × Nat))) =>
      (p.1 :: p.2.1, outgoing p.1 p.2.1 ++ p.2.2)) := by
    have hx : Primrec (fun p : List Nat × (Nat × (List Nat × List (Nat × Nat))) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have htail : Primrec (fun p : List Nat × (Nat × (List Nat × List (Nat × Nat))) => p.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hpairs : Primrec (fun p : List Nat × (Nat × (List Nat × List (Nat × Nat))) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact ((Primrec.list_cons.comp hx htail).pair
      (Primrec.list_append.comp (outgoing_primrec.comp hx htail) hpairs)).to₂
  exact Primrec.snd.comp (Primrec.list_foldr Primrec.id (Primrec.const ([], [])) hs)

@[simp] theorem forwardPairs_nil : forwardPairs [] = [] := rfl

@[simp] theorem forwardPairs_cons (x : Nat) (L : List Nat) :
    forwardPairs (x :: L) = outgoing x L ++ forwardPairs L := by
  change outgoing x (forwardPairsState L).1 ++ (forwardPairsState L).2 = _
  rw [forwardPairsState_first]
  rfl

theorem outgoing_exact (R : Nat → Nat → Prop) (x : Nat) (L : List Nat) :
    (∀ p ∈ outgoing x L, R p.1 p.2) ↔ ∀ y ∈ L, R x y := by
  constructor
  · intro h y hy
    exact h (x, y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
  · intro h p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    exact h y hy

theorem forwardPairs_exact (R : Nat → Nat → Prop) (L : List Nat) :
    (∀ p ∈ forwardPairs L, R p.1 p.2) ↔ L.Pairwise R := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [forwardPairs_cons, List.pairwise_cons]
    constructor
    · intro h
      exact ⟨(outgoing_exact R x L).mp (fun p hp => h p (List.mem_append_left _ hp)),
        ih.mp (fun p hp => h p (List.mem_append_right _ hp))⟩
    · rintro ⟨hx, ht⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (outgoing_exact R x L).mpr hx p hp
      · exact ih.mpr ht p hp

theorem positive_mono {c : Program} {n k l : Nat} (hkl : k ≤ l)
    (h : positive k c n = true) : positive l c n = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨y,
    Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hkl (Option.mem_def.mpr hy))⟩

theorem finite_positive (c : Program) (L : List Nat) :
    (∃ k, ∀ n ∈ L, positive k c n = true) ↔ ∀ n ∈ L, c.domain n := by
  constructor
  · rintro ⟨k, h⟩ n hn
    exact (positive_iff c n).mp ⟨k, h n hn⟩
  · induction L with
    | nil => intro _; exact ⟨0, by simp⟩
    | cons n L ih =>
      intro h
      obtain ⟨k, hk⟩ := (positive_iff c n).mpr (h n List.mem_cons_self)
      obtain ⟨l, hl⟩ := ih (fun m hm => h m (List.mem_cons_of_mem _ hm))
      refine ⟨max k l, ?_⟩
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact positive_mono (Nat.le_max_left _ _) hk
      · exact positive_mono (Nat.le_max_right _ _) (hl m hm)

def chainCheck (c : Program) (cutoff : Nat) (B : List Nat) (k ν : Nat) (tail : List Nat) : Bool :=
  decide (tail.length = k) &&
    (allCheck (listMember B) (ν :: tail) &&
      (allCheck (fun p => decide (p.1 < p.2)) (forwardPairs (ν :: tail)) &&
        allCheck (fun p => positive cutoff c (Nat.pair p.1 p.2)) (forwardPairs (ν :: tail))))

theorem chainCheck_primrec :
    Primrec (fun p : ((Program × Nat) × List Nat) × ((Nat × Nat) × List Nat) =>
      chainCheck p.1.1.1 p.1.1.2 p.1.2 p.2.1.1 p.2.1.2 p.2.2) := by
  have hp : Primrec (fun p : ((Program × Nat) × List Nat) × ((Nat × Nat) × List Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hB : Primrec (fun p : ((Program × Nat) × List Nat) × ((Nat × Nat) × List Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hq : Primrec (fun p : ((Program × Nat) × List Nat) × ((Nat × Nat) × List Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : ((Program × Nat) × List Nat) × ((Nat × Nat) × List Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hL := Primrec.list_cons.comp (Primrec.snd.comp hq) ht
  have hedges := forwardPairs_primrec.comp hL
  have horder : Primrec₂ (fun (_ : Unit) (q : Nat × Nat) => decide (q.1 < q.2)) :=
    (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide.to₂
  have hpositive : Primrec₂ (fun (p : Program × Nat) (q : Nat × Nat) =>
      positive p.2 p.1 (Nat.pair q.1 q.2)) :=
    (positive_primrec.comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂
  exact Primrec.and.comp
    (Primrec.eq.comp (Primrec.list_length.comp ht) (Primrec.fst.comp hq)).decide
    (Primrec.and.comp ((allCheck_primrec _ listMember_primrec).comp hB hL)
      (Primrec.and.comp ((allCheck_primrec _ horder).comp (Primrec.const ()) hedges)
        ((allCheck_primrec _ hpositive).comp hp hedges)))

theorem chainCheck_iff (c : Program) (cutoff : Nat) (B : List Nat) (k ν : Nat) (tail : List Nat) :
    chainCheck c cutoff B k ν tail = true ↔
      tail.length = k ∧ (∀ μ ∈ ν :: tail, μ ∈ B) ∧ (ν :: tail).Pairwise (· < ·) ∧
        ∀ p ∈ forwardPairs (ν :: tail), positive cutoff c (Nat.pair p.1 p.2) = true := by
  simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq, allCheck_iff,
    listMember, forwardPairs_exact]

theorem chainCheck_sound {c : Program} {cutoff : Nat} {B : List Nat} {k ν : Nat} {tail : List Nat}
    (h : chainCheck c cutoff B k ν tail = true) :
    GuardChainIn (fun μ η => c.domain (Nat.pair μ η)) B.toFinset k ν := by
  obtain ⟨hl, hb, ho, hp⟩ := (chainCheck_iff _ _ _ _ _ _).mp h
  refine ⟨tail, hl, ho, (forwardPairs_exact _ _).mp ?_, ?_⟩
  · intro p hm
    exact (positive_iff c _).mp ⟨cutoff, hp p hm⟩
  · intro μ hμ
    exact List.mem_toFinset.mpr (hb μ hμ)

theorem chainCheck_complete {c : Program} {B : List Nat} {k ν : Nat}
    (h : GuardChainIn (fun μ η => c.domain (Nat.pair μ η)) B.toFinset k ν) :
    ∃ tail cutoff, chainCheck c cutoff B k ν tail = true := by
  obtain ⟨tail, hl, ho, hr, hb⟩ := h
  have hdom : ∀ n ∈ (forwardPairs (ν :: tail)).map (fun p => Nat.pair p.1 p.2), c.domain n := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    exact (forwardPairs_exact _ _).mpr hr p hp
  obtain ⟨cutoff, hc⟩ := (finite_positive c _).mpr hdom
  refine ⟨tail, cutoff, (chainCheck_iff _ _ _ _ _ _).mpr ⟨hl, ?_, ho, ?_⟩⟩
  · intro μ hμ
    exact List.mem_toFinset.mp (hb μ hμ)
  · intro p hp
    exact hc _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

abbrev ChainWitness := (Nat × Nat) × (List Nat × Nat)
abbrev EdgeWitness := (Nat × Nat) × Nat
abbrev Witness := List ChainWitness × List EdgeWitness
abbrev Parameters := (List Nat × List Nat) × (Program × Program)

def chainWitnessCheck (p : Parameters) (q : Nat × Nat) (w : ChainWitness) : Bool :=
  decide (w.1 = q) && chainCheck p.2.2 w.2.2 p.1.2 q.1 q.2 w.2.1

def edgeWitnessCheck (c : Program) (q : Nat × Nat) (w : EdgeWitness) : Bool :=
  decide (w.1 = q) && (decide (q.1 < q.2) && positive w.2 c (Nat.pair q.1 q.2))

theorem chainWitnessCheck_primrec :
    Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness =>
      chainWitnessCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × (Nat × Nat)) × ChainWitness => p.2) := Primrec.snd
  have hc := Primrec.snd.comp (Primrec.snd.comp hp)
  have hB := Primrec.snd.comp (Primrec.fst.comp hp)
  have ht := Primrec.fst.comp (Primrec.snd.comp hw)
  have hk := Primrec.snd.comp (Primrec.snd.comp hw)
  exact Primrec.and.comp (Primrec.eq.comp (Primrec.fst.comp hw) hq).decide
    (chainCheck_primrec.comp (((hc.pair hk).pair hB).pair (hq.pair ht)))

theorem edgeWitnessCheck_primrec :
    Primrec (fun p : (Program × (Nat × Nat)) × EdgeWitness =>
      edgeWitnessCheck p.1.1 p.1.2 p.2) := by
  have hc : Primrec (fun p : (Program × (Nat × Nat)) × EdgeWitness => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : (Program × (Nat × Nat)) × EdgeWitness => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hμ := Primrec.fst.comp hq
  have hν := Primrec.snd.comp hq
  have hw : Primrec (fun p : (Program × (Nat × Nat)) × EdgeWitness => p.2) := Primrec.snd
  exact Primrec.and.comp (Primrec.eq.comp (Primrec.fst.comp hw) hq).decide
    (Primrec.and.comp (Primrec.nat_lt.comp hμ hν).decide
      (positive_primrec.comp (((Primrec.snd.comp hw).pair hc).pair
        (Primrec₂.natPair.comp hμ hν))))

def condition (p : Parameters) (r : GuardRequirements Nat) (w : Witness) : Bool :=
  allCheck (fun q => anyCheck (chainWitnessCheck p q) w.1) r.1 &&
    allCheck (fun q => anyCheck (edgeWitnessCheck p.2.1 q) w.2) r.2

set_option maxHeartbeats 800000 in
theorem condition_primrec :
    Primrec (fun p : (Parameters × GuardRequirements Nat) × Witness => condition p.1.1 p.1.2 p.2) := by
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
  have het : Primrec₂ (fun (s : Program × List EdgeWitness) (q : Nat × Nat) =>
      anyCheck (edgeWitnessCheck s.1 q) s.2) :=
    (hedge.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have result := Primrec.and.comp
    ((allCheck_primrec _ hct).comp (hp.pair (Primrec.fst.comp hw)) (Primrec.fst.comp hr))
    ((allCheck_primrec _ het).comp
      ((Primrec.fst.comp (Primrec.snd.comp hp)).pair (Primrec.snd.comp hw)) (Primrec.snd.comp hr))
  exact result.of_eq (fun _ => rfl)

theorem finite_cover {α β : Type} (L : List α) (T : α → β → Prop)
    (h : ∀ x ∈ L, ∃ w, T x w) : ∃ W : List β, ∀ x ∈ L, ∃ w ∈ W, T x w := by
  revert h
  induction L with
  | nil => intro _; exact ⟨[], by simp⟩
  | cons x L ih =>
    intro h
    obtain ⟨w, hw⟩ := h x List.mem_cons_self
    obtain ⟨W, hW⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨w :: W, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨w, List.mem_cons_self, hw⟩
    · obtain ⟨v, hv, ht⟩ := hW y hy
      exact ⟨v, List.mem_cons_of_mem _ hv, ht⟩

theorem condition_correct (p : Parameters) (r : GuardRequirements Nat) :
    (∃ w, condition p r w = true) ↔
      GuardRequirements.Holds (fun μ ν => p.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.2.2.domain (Nat.pair μ ν)) p.1.2.toFinset r := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hc, he⟩ := Bool.and_eq_true_iff.mp hw
    constructor
    · intro q hq
      obtain ⟨v, _, hv⟩ := (anyCheck_iff _ _).mp ((allCheck_iff _ _).mp hc q hq)
      exact chainCheck_sound (Bool.and_eq_true_iff.mp hv).2
    · intro q hq
      obtain ⟨v, _, hv⟩ := (anyCheck_iff _ _).mp ((allCheck_iff _ _).mp he q hq)
      have ht := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).2
      exact ⟨of_decide_eq_true ht.1, (positive_iff _ _).mp ⟨v.2, ht.2⟩⟩
  · intro h
    have hc : ∀ q ∈ r.1, ∃ v, chainWitnessCheck p q v = true := by
      intro q hq
      obtain ⟨tail, cutoff, ht⟩ := chainCheck_complete (h.1 q hq)
      exact ⟨(q, (tail, cutoff)), by simp [chainWitnessCheck, ht]⟩
    have he : ∀ q ∈ r.2, ∃ v, edgeWitnessCheck p.2.1 q v = true := by
      intro q hq
      obtain ⟨cutoff, ht⟩ := (positive_iff _ _).mpr (h.2 q hq).2
      exact ⟨(q, cutoff), by simp [edgeWitnessCheck, ht, (h.2 q hq).1]⟩
    obtain ⟨C, hC⟩ := finite_cover r.1 _ hc
    obtain ⟨D, hD⟩ := finite_cover r.2 _ he
    exact ⟨(C, D), by
      simpa only [condition, Bool.and_eq_true, allCheck_iff, anyCheck_iff]
        using And.intro hC hD⟩

def defaultParameters : Parameters := (([], []), (Nat.Partrec.Code.zero, Nat.Partrec.Code.zero))
def decodeParameters (n : Nat) : Parameters := (Encodable.decode (α := Parameters) n).getD defaultParameters
def decodeWitness (n : Nat) : Witness := (Encodable.decode (α := Witness) n).getD ([], [])
def decodeFormula (n : Nat) : Syntax := (Encodable.decode (α := Syntax) n).getD .falsum

theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([], []))

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
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff, Part.some_dom,
    implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (p : Parameters) (φ : Syntax) :
    (evaluation (Encodable.encode p) (φ.code RecordedHead.code)).Dom ↔
      φ.MainGuarded (fun μ ν => p.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset := by
  rw [evaluation_domain, ← mainRequirementsCode_exact, ← condition_correct]
  constructor
  · rintro ⟨certificate, hc⟩
    exact ⟨decodeWitness certificate, by simpa [check] using hc⟩
  · rintro ⟨w, hw⟩
    exact ⟨Encodable.encode w, by
      simpa only [check, decodeParameters_encode, decodeFormula_code, decodeWitness_encode,
        beq_self_eq_true, Bool.true_and] using hw⟩

theorem evaluation_only_formulas (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
      φ.MainGuarded (fun μ ν => (decodeParameters key).2.1.domain (Nat.pair μ ν))
        (fun μ ν => (decodeParameters key).2.2.domain (Nat.pair μ ν))
        (decodeParameters key).1.1.toFinset (decodeParameters key).1.2.toFinset := by
  obtain ⟨certificate, hc⟩ := (evaluation_domain _ _).mp h
  have he : query = (decodeFormula query).code RecordedHead.code :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).1
  refine ⟨decodeFormula query, he, ?_⟩
  rw [← mainRequirementsCode_exact, ← he]
  exact (condition_correct _ _).mp ⟨decodeWitness certificate, (Bool.and_eq_true_iff.mp hc).2⟩

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p, ∀ φ : Syntax, (compiler p).domain (φ.code RecordedHead.code) ↔
      φ.MainGuarded (fun μ ν => p.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset) ∧
    (∀ p query, (compiler p).domain query → ∃ φ : Syntax, query = φ.code RecordedHead.code ∧
      φ.MainGuarded (fun μ ν => p.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.2.2.domain (Nat.pair μ ν)) p.1.1.toFinset p.1.2.toFinset) := by
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
  · intro p query h
    change ((compiler p).eval query).Dom at h
    rw [heval] at h
    simpa only [decodeParameters_encode] using evaluation_only_formulas _ _ h

theorem semantic_compiler_exists (R₁ R₂ : Nat → Nat → Prop) (E B : List Nat) (c₁ c₂ : Program)
    (h₁ : ∀ μ ν, c₁.domain (Nat.pair μ ν) ↔ R₁ μ ν)
    (h₂ : ∀ μ ν, c₂.domain (Nat.pair μ ν) ↔ R₂ μ ν) :
    ∃ c : Program, ∀ φ : Syntax, c.domain (φ.code RecordedHead.code) ↔
      φ.MainGuarded R₁ R₂ E.toFinset B.toFinset := by
  obtain ⟨compiler, _, hc, _⟩ := compiler_exists
  have he₁ : (fun μ ν => c₁.domain (Nat.pair μ ν)) = R₁ :=
    funext (fun μ => funext (fun ν => propext (h₁ μ ν)))
  have he₂ : (fun μ ν => c₂.domain (Nat.pair μ ν)) = R₂ :=
    funext (fun μ => funext (fun ν => propext (h₂ μ ν)))
  refine ⟨compiler ((E, B), (c₁, c₂)), ?_⟩
  intro φ
  simpa only [he₁, he₂] using hc ((E, B), (c₁, c₂)) φ

end Alexander313.RecordedGuardProgram
