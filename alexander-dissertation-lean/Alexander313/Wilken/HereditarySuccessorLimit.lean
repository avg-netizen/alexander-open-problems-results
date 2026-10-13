import Alexander313.Wilken.HereditaryExponentDecomposition

/-!
# Executing original successor/zero/limit decisions and canonical predecessors

The genuine omega-left decomposition writes every original value as
omega*delta+n. Its natural remainder is positive exactly at successors;
remainder zero gives an actual successor prelimit, and delta distinguishes
zero from a nonzero limit. Guarded decisions reject malformed raw inputs and
are total Computable functions, without a primitive-recursive execution claim.

On exactly the original successor domain the predecessor routine constructs
the canonical sum of the actual omega-prefix and the numeral n-1. Real ordinal
successor arithmetic proves its value is Ordinal.pred of the input, its sum
with one is the input, and its complete canonical output is unique and invariant.
No successor, predecessor, decomposition or effectivity oracle is supplied.
All proofs remain uncompiled source candidates; no tracking claim is made.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SuccessorLimit

open ExponentDecomposition (delta offset «prefix» DataSpec)

theorem omega_add_nat_prelimit (δ : Ordinal.{0}) (n : Nat) :
    Order.IsSuccPrelimit (Ordinal.omega0 * δ + (n : Ordinal.{0})) ↔ n = 0 := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, iff_true]
    exact Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr ⟨δ, rfl⟩
  | succ n =>
    rw [Nat.cast_succ, ← add_assoc, ← Order.succ_eq_add_one]
    simp only [Order.not_isSuccPrelimit_succ, Nat.succ_ne_zero, iff_false, not_false_eq_true]

theorem data_prelimit_iff (q data : Nat) (hd : DataSpec q data) :
    Order.IsSuccPrelimit (unionInterpretation q) ↔ offset data = 0 := by
  rw [hd.2.2.2.2, hd.2.2.2.1]
  exact omega_add_nat_prelimit _ _

theorem data_zero_iff (q data : Nat) (hd : DataSpec q data) :
    unionInterpretation q = 0 ↔ offset data = 0 ∧ unionInterpretation (delta data) = 0 := by
  rw [hd.2.2.2.2, hd.2.2.2.1]
  simp only [Ordinal.add_eq_zero_iff, mul_eq_zero, Ordinal.omega0_ne_zero, false_or,
    Nat.cast_eq_zero, and_comm]

theorem data_limit_iff (q data : Nat) (hd : DataSpec q data) :
    Order.IsSuccLimit (unionInterpretation q) ↔
      offset data = 0 ∧ unionInterpretation (delta data) ≠ 0 := by
  rw [Ordinal.isSuccLimit_iff, data_zero_iff q data hd, data_prelimit_iff q data hd]
  tauto

theorem data_successor_iff (q data : Nat) (hd : DataSpec q data) :
    ¬ Order.IsSuccPrelimit (unionInterpretation q) ↔ 0 < offset data := by
  rw [data_prelimit_iff q data hd, Nat.pos_iff_ne_zero]

theorem successor_iff_exists (α : Ordinal.{0}) :
    ¬ Order.IsSuccPrelimit α ↔ ∃ β : Ordinal.{0}, β + 1 = α := by
  constructor
  · intro h
    obtain ⟨β, _, he⟩ := Order.not_isSuccPrelimit_iff_succ_eq.mp h
    exact ⟨β, by simpa only [Order.succ_eq_add_one] using he⟩
  · rintro ⟨β, rfl⟩
    simpa only [Order.succ_eq_add_one] using Order.not_isSuccPrelimit_succ β

/-- Tags 0,1,2 select actual zero, nonzero limit, and successor respectively. -/
def Meaning (tag : Nat) (α : Ordinal.{0}) : Prop :=
  if tag = 0 then α = 0 else if tag = 1 then Order.IsSuccLimit α
    else if tag = 2 then ¬ Order.IsSuccPrelimit α else False

def dataCheck (tag data : Nat) : Bool :=
  cond (tag == 0) ((offset data == 0) && OmegaPowers.zeroCheck (delta data))
    (cond (tag == 1) ((offset data == 0) && !OmegaPowers.zeroCheck (delta data))
      (cond (tag == 2) (!(offset data == 0)) false))

theorem dataCheck_primrec : Primrec₂ dataCheck := by
  have hn := Primrec.beq.comp (ExponentDecomposition.offset_primrec.comp Primrec.snd) (Primrec.const 0)
  have hz := OmegaPowers.zeroCheck_primrec.comp (ExponentDecomposition.delta_primrec.comp Primrec.snd)
  exact ((Primrec.beq.comp Primrec.fst (Primrec.const 0)).cond (Primrec.and.comp hn hz)
    ((Primrec.beq.comp Primrec.fst (Primrec.const 1)).cond (Primrec.and.comp hn (Primrec.not.comp hz))
      ((Primrec.beq.comp Primrec.fst (Primrec.const 2)).cond (Primrec.not.comp hn) (Primrec.const false)))).to₂

theorem dataCheck_exact (tag q data : Nat) (hd : DataSpec q data) :
    dataCheck tag data = true ↔ Meaning tag (unionInterpretation q) := by
  have hz : OmegaPowers.zeroCheck (delta data) = true ↔ unionInterpretation (delta data) = 0 := by
    simp only [OmegaPowers.zeroCheck_exact, Canonical.check_original hd.2.1, true_and]
  have hzn : (!OmegaPowers.zeroCheck (delta data)) = true ↔ unionInterpretation (delta data) ≠ 0 := by
    rw [Bool.not_eq_true_eq_eq_false, ← Bool.eq_false_eq_not_eq_true, hz]
  by_cases h0 : tag = 0
  · simp only [dataCheck, Meaning, h0, beq_self_eq_true, Bool.cond_true, if_true,
      Bool.and_eq_true, beq_iff_eq, hz]
    exact (data_zero_iff q data hd).symm
  · by_cases h1 : tag = 1
    · simp [dataCheck, Meaning, h0, h1, hzn, ← data_limit_iff q data hd]
    · by_cases h2 : tag = 2
      · simp [dataCheck, Meaning, h0, h1, h2, ← data_prelimit_iff q data hd]
      · simp [dataCheck, Meaning, h0, h1, h2]

def decision (tag q : Nat) : Part Bool :=
  cond (unionCheck q) ((ExponentDecomposition.decompose q).map (dataCheck tag)) (Part.some false)

theorem decision_partrec : Partrec₂ decision := by
  have hm := (ExponentDecomposition.decompose_partrec.comp Computable.snd).map
    (dataCheck_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact (Partrec.cond (Uniform.unionCheck_primrec.comp Primrec.snd).to_comp hm
    (Computable.const false).partrec).to₂

theorem decision_total (tag q : Nat) : (decision tag q).Dom := by
  cases hq : unionCheck q with
  | false => simpa only [decision, hq, Bool.cond_false] using Part.some_dom false
  | true =>
    rw [decision, hq]
    change (ExponentDecomposition.decompose q).Dom
    exact (ExponentDecomposition.decompose_domain q).mpr hq

theorem decision_true_iff (tag q : Nat) : true ∈ decision tag q ↔
    unionCheck q = true ∧ Meaning tag (unionInterpretation q) := by
  cases hq : unionCheck q with
  | false => simp [decision, hq]
  | true =>
    constructor
    · intro h
      have hm : true ∈ (ExponentDecomposition.decompose q).map (dataCheck tag) := by
        simpa only [decision, hq, Bool.cond_true] using h
      obtain ⟨data, hd, he⟩ := (Part.mem_map_iff (dataCheck tag)).mp hm
      exact ⟨hq, (dataCheck_exact tag q data (ExponentDecomposition.decompose_value q data hd)).mp he⟩
    · rintro ⟨_, hs⟩
      obtain ⟨data, hd, hds⟩ := ExponentDecomposition.decompose_returns q hq
      have he := (dataCheck_exact tag q data hds).mpr hs
      have hm := Part.mem_map (dataCheck tag) hd
      rw [he] at hm
      simpa only [decision, hq, Bool.cond_true] using hm

def check (tag q : Nat) : Bool := (decision tag q).get (decision_total tag q)

theorem check_mem (tag q : Nat) : check tag q ∈ decision tag q := ⟨decision_total tag q, rfl⟩

theorem decision_eq_some (tag q : Nat) : decision tag q = Part.some (check tag q) :=
  Part.eq_some_iff.mpr (check_mem tag q)

theorem check_computable : Computable₂ check :=
  (decision_partrec.of_eq_tot (fun p => check_mem p.1 p.2)).to₂

theorem check_exact (tag q : Nat) : check tag q = true ↔
    unionCheck q = true ∧ Meaning tag (unionInterpretation q) := by
  simpa only [decision_eq_some, Part.mem_some_iff, eq_comm] using decision_true_iff tag q

def zeroCheck (q : Nat) : Bool := check 0 q
def limitCheck (q : Nat) : Bool := check 1 q
def successorCheck (q : Nat) : Bool := check 2 q
def prelimitCheck (q : Nat) : Bool := zeroCheck q || limitCheck q

theorem zeroCheck_computable : Computable zeroCheck := check_computable.comp (Computable.const 0) Computable.id
theorem limitCheck_computable : Computable limitCheck := check_computable.comp (Computable.const 1) Computable.id
theorem successorCheck_computable : Computable successorCheck := check_computable.comp (Computable.const 2) Computable.id
theorem prelimitCheck_computable : Computable prelimitCheck :=
  Primrec.or.to_comp.comp zeroCheck_computable limitCheck_computable

theorem zeroCheck_exact (q : Nat) : zeroCheck q = true ↔ unionCheck q = true ∧ unionInterpretation q = 0 := by
  simpa only [zeroCheck, Meaning, if_pos rfl] using check_exact 0 q

theorem limitCheck_exact (q : Nat) : limitCheck q = true ↔ unionCheck q = true ∧ Order.IsSuccLimit (unionInterpretation q) := by
  simpa [limitCheck, Meaning] using check_exact 1 q

theorem successorCheck_exact (q : Nat) : successorCheck q = true ↔
    unionCheck q = true ∧ ¬ Order.IsSuccPrelimit (unionInterpretation q) := by
  simpa [successorCheck, Meaning] using check_exact 2 q

theorem successorCheck_exists (q : Nat) : successorCheck q = true ↔
    unionCheck q = true ∧ ∃ β : Ordinal.{0}, β + 1 = unionInterpretation q := by
  rw [successorCheck_exact, successor_iff_exists]

theorem prelimitCheck_exact (q : Nat) : prelimitCheck q = true ↔
    unionCheck q = true ∧ Order.IsSuccPrelimit (unionInterpretation q) := by
  simp only [prelimitCheck, Bool.or_eq_true, zeroCheck_exact, limitCheck_exact, Ordinal.isSuccLimit_iff]
  have hz := Ordinal.isSuccPrelimit_zero
  by_cases he : unionInterpretation q = 0 <;> simp [he, hz]

theorem check_rejected (tag q : Nat) (hq : unionCheck q = false) : check tag q = false := by
  cases hc : check tag q with
  | false => rfl
  | true => have ht := ((check_exact tag q).mp hc).1; rw [hq] at ht; cases ht

theorem check_invariant (tag q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : check tag q = check tag v := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_exact, hq, hv, true_and, he]

def predecessorCode (data : Nat) : Nat := CanonicalArithmetic.canonicalSum («prefix» data)
  (CanonicalArithmetic.numeralCode (offset data - 1))

theorem predecessorCode_primrec : Primrec predecessorCode :=
  CanonicalArithmetic.canonicalSum_primrec.comp ExponentDecomposition.prefix_primrec
    (CanonicalArithmetic.numeralCode_primrec.comp
      (Primrec.nat_sub.comp ExponentDecomposition.offset_primrec (Primrec.const 1)))

theorem predecessorCode_checked (q data : Nat) (hd : DataSpec q data) :
    Canonical.check (predecessorCode data) = true :=
  CanonicalArithmetic.canonicalSum_checked _ _ (Canonical.check_original hd.2.2.1)
    (Canonical.check_original (CanonicalArithmetic.numeralCode_checked _))

theorem predecessorCode_add_one (q data : Nat) (hd : DataSpec q data) (hn : 0 < offset data) :
    unionInterpretation (predecessorCode data) + 1 = unionInterpretation q := by
  have hnat : ((offset data - 1 : Nat) : Ordinal.{0}) + 1 = (offset data : Ordinal.{0}) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)
  rw [predecessorCode, CanonicalArithmetic.canonicalSum_value _ _ (Canonical.check_original hd.2.2.1)
    (Canonical.check_original (CanonicalArithmetic.numeralCode_checked _)), CanonicalArithmetic.numeralCode_value,
    add_assoc, hnat]
  exact hd.2.2.2.2.symm

def predecessorStep (data : Nat) : Part Nat :=
  cond (offset data == 0) Part.none (Part.some (predecessorCode data))

theorem predecessorStep_partrec : Partrec predecessorStep :=
  Partrec.cond (Primrec.beq.comp ExponentDecomposition.offset_primrec (Primrec.const 0)).to_comp
    Partrec.none predecessorCode_primrec.to_comp.partrec

def predecessor (q : Nat) : Part Nat := (ExponentDecomposition.decompose q).bind predecessorStep

theorem predecessor_partrec : Partrec predecessor :=
  ExponentDecomposition.decompose_partrec.bind (predecessorStep_partrec.comp Computable.snd).to₂

theorem predecessor_value (q c : Nat) (hc : c ∈ predecessor q) :
    unionCheck q = true ∧ Canonical.check c = true ∧
      unionInterpretation c + 1 = unionInterpretation q ∧ unionInterpretation c = Ordinal.pred (unionInterpretation q) := by
  obtain ⟨data, hd, hs⟩ := Part.mem_bind_iff.mp hc
  have hds := ExponentDecomposition.decompose_value q data hd
  cases hn : offset data == 0 with
  | true => have hf : False := by simpa [predecessorStep, hn] using hs; exact hf.elim
  | false =>
    have he : c = predecessorCode data := by simpa [predecessorStep, hn] using hs
    have hp : 0 < offset data := Nat.pos_iff_ne_zero.mpr (by simpa using hn)
    subst c
    have hv := predecessorCode_add_one q data hds hp
    exact ⟨hds.1, predecessorCode_checked q data hds, hv, by rw [← hv, Ordinal.pred_add_one]⟩

theorem predecessor_domain (q : Nat) : (predecessor q).Dom ↔
    unionCheck q = true ∧ ¬ Order.IsSuccPrelimit (unionInterpretation q) := by
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := Part.dom_iff_mem.mp hd
    have hs := predecessor_value q c hc
    exact ⟨hs.1, (successor_iff_exists _).mpr ⟨unionInterpretation c, hs.2.2.1⟩⟩
  · rintro ⟨hq, hp⟩
    obtain ⟨data, hd, hs⟩ := ExponentDecomposition.decompose_returns q hq
    have hn := (data_successor_iff q data hs).mp hp
    apply Part.dom_iff_mem.mpr
    refine ⟨predecessorCode data, Part.mem_bind hd ?_⟩
    simp [predecessorStep, ne_of_gt hn]

theorem predecessor_returns (q : Nat) (hq : successorCheck q = true) :
    ∃ c : Nat, c ∈ predecessor q ∧ Canonical.check c = true ∧
      unionInterpretation c + 1 = unionInterpretation q ∧ unionInterpretation c = Ordinal.pred (unionInterpretation q) := by
  have hd := (predecessor_domain q).mpr ((successorCheck_exact q).mp hq)
  have hc : (predecessor q).get hd ∈ predecessor q := ⟨hd, rfl⟩
  exact ⟨_, hc, (predecessor_value q _ hc).2⟩

theorem predecessor_graph_iff (q c : Nat) : c ∈ predecessor q ↔
    unionCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c + 1 = unionInterpretation q := by
  constructor
  · intro hc; have hs := predecessor_value q c hc; exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  · rintro ⟨hq, hc, he⟩
    have hp := (successorCheck_exists q).mpr ⟨hq, unionInterpretation c, he⟩
    obtain ⟨d, hd, hdc, hde, _⟩ := predecessor_returns q hp
    have hv : unionInterpretation c = unionInterpretation d := by
      simpa only [Nat.cast_one] using (Ordinal.add_right_cancel 1).mp (he.trans hde.symm)
    rw [Canonical.check_value_injective c d hc hdc hv]
    exact hd

theorem predecessor_pred_graph_iff (q c : Nat) : c ∈ predecessor q ↔
    successorCheck q = true ∧ Canonical.check c = true ∧ unionInterpretation c = Ordinal.pred (unionInterpretation q) := by
  constructor
  · intro hc
    have hs := predecessor_value q c hc
    exact ⟨(successorCheck_exists q).mpr ⟨hs.1, unionInterpretation c, hs.2.2.1⟩, hs.2.1, hs.2.2.2⟩
  · rintro ⟨hq, hc, he⟩
    obtain ⟨d, hd, hdc, _, hde⟩ := predecessor_returns q hq
    rw [Canonical.check_value_injective c d hc hdc (he.trans hde.symm)]
    exact hd

theorem predecessor_original (q c : Nat) (hc : c ∈ predecessor q) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := (predecessor_value q c hc).2.1
  exact ⟨Canonical.check_original hs, Canonical.check_normal hs⟩

theorem predecessor_unique (q c d : Nat) (hc : c ∈ predecessor q) (hd : d ∈ predecessor q) : c = d := by
  have hs := predecessor_value q c hc
  have ht := predecessor_value q d hd
  exact Canonical.check_value_injective c d hs.2.1 ht.2.1 (hs.2.2.2.trans ht.2.2.2.symm)

theorem predecessor_invariant (q v c d : Nat) (hc : c ∈ predecessor q) (hd : d ∈ predecessor v)
    (he : unionInterpretation q = unionInterpretation v) : c = d := by
  have hs := predecessor_value q c hc
  have ht := predecessor_value v d hd
  exact Canonical.check_value_injective c d hs.2.1 ht.2.1
    (hs.2.2.2.trans (by rw [he]; exact ht.2.2.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.SuccessorLimit
