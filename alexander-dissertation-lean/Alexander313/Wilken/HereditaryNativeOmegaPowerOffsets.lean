import Alexander313.Wilken.HereditaryNativeOmegaPowersSupport

/-!
# Actual epsilon-finite recognition on original native LOW words

The genuinely normalized native principal word supplies one checked epsilon
head and a finite tail of original unit atoms. The actual epsilon atom test
uses public epsilon classification for parameters and the proved source
high/zero criterion for low theta atoms. Complete ANF uniqueness supplies
completeness; the finite offset is the actual tail length. No epsilon, offset,
negative class or parser oracle is supplied. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers.Offsets

open ThetaCourse

def baseCode : Nat := SourceChi.Powers.baseTree.code

theorem baseCode_spec (q : Nat) (hq : baseCheck q = true) :
    Comparison.acceptedCode q baseCode = true ∧ interpretation q baseCode = base q := by
  exact ⟨(Comparison.acceptedCode_exact q _).mpr ⟨by
    simpa only [baseCode, checkCode_code] using SourceChi.Powers.baseTree_checked q hq, by
    simpa only [baseCode, rawTree_code] using SourceChi.Powers.baseTree_normal q⟩,
    by simpa only [baseCode, interpretation_code] using SourceChi.Powers.baseTree_value q hq⟩

def epsilonAtomCheck (q c : Nat) : Bool :=
  let tag := c.pred.unpair.1
  let p := c.pred.unpair.2
  cond (tag == 0) (Epsilon.unionEpsilonCheck p)
    (cond (tag == 2) ((p.unpair.1 == 0) &&
      (Comparison.equalCode q c baseCode || Decomposition.above 0 (rawTree p.unpair.2))) false)

theorem epsilonAtomCheck_primrec : Primrec₂ epsilonAtomCheck := by
  have hp := Primrec.snd.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.snd))
  have ht := Primrec.fst.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.snd))
  have he := Comparison.equalCode_primrec.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const baseCode)))
  have hh := Decomposition.above_primrec.comp (Primrec.const 0)
    (rawTree_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp hp)))
  exact ((Primrec.beq.comp ht (Primrec.const 0)).cond (Epsilon.unionEpsilonCheck_primrec.comp hp)
    ((Primrec.beq.comp ht (Primrec.const 2)).cond
      (Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp hp)) (Primrec.const 0))
        (Primrec.or.comp he hh)) (Primrec.const false))).to₂

@[simp] theorem epsilonAtomCheck_parameter (q p : Nat) :
    epsilonAtomCheck q (.parameter p : RelativeTerm Nat).code = Epsilon.unionEpsilonCheck p := by
  simp only [epsilonAtomCheck, code_parameter, Nat.pred_succ, Nat.unpair_pair,
    beq_self_eq_true, Bool.cond_true]

@[simp] theorem epsilonAtomCheck_theta_zero (q : Nat) (a : RelativeTerm Nat) :
    epsilonAtomCheck q (.theta 0 a).code =
      (Comparison.equalCode q (.theta 0 a).code baseCode || Decomposition.above 0 a) := by
  simp only [epsilonAtomCheck, code_theta, Nat.pred_succ, Nat.unpair_pair,
    rawTree_code, beq_self_eq_true, Bool.cond_true, Bool.cond_false, Bool.true_and]

private theorem atom_shape (t a : RelativeTerm Nat) (ha : a ∈ Comparison.atoms t) :
    (∃ p, a = .parameter p) ∨ (∃ k b, a = .theta k b) := by
  revert ha
  induction t with
  | parameter p =>
    intro ha
    obtain ⟨v, hv, he⟩ := List.mem_map.mp ha
    exact Or.inl ⟨v, he.symm⟩
  | sum s t ihs iht =>
    intro ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ihs ha
    · exact iht ha
  | theta k b ih =>
    intro ha
    exact Or.inr ⟨k, b, (List.mem_singleton.mp ha)⟩

private theorem above_zero_iff (q : Nat) (a : RelativeTerm Nat) (ha : check q a = true) :
    Decomposition.above 0 a = true ↔ omegaSequence (base q) 1 ≤ denote q a := by
  simpa only [Nat.zero_add] using Decomposition.above_exact q 0 a ha

/-- The epsilon decision is proved only on genuine LOW ANF atoms, the
exact original domain of its callers. Higher theta atoms are never coerced. -/
theorem epsilonAtomCheck_correct (q c : Nat) (hc : lowCheckCode q c = true)
    (hn : Comparison.acceptedCode q c = true)
    (shape : (∃ p, rawTree c = .parameter p) ∨ (∃ k a, rawTree c = .theta k a)) :
    epsilonAtomCheck q c = true ↔ Ordinal.omega0 ^ interpretation q c = interpretation q c := by
  have hi := HeightBoundary.input_spec q c hc
  have hq := hi.2.1
  have hecode : (rawTree c).code = c := by
    obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hi.1
    simp only [← he, rawTree_code]
  rcases shape with ⟨p, hp⟩ | ⟨k, a, ha⟩
  · have hpc : (.parameter p : RelativeTerm Nat).code = c := by rw [← hp]; exact hecode
    rw [← hpc, epsilonAtomCheck_parameter, interpretation_code]
    have htp : check q (.parameter p) = true := by
      simpa only [hp] using Arithmetic.raw_checked q c hi.1
    have ht : parameterCheck q p = true := (checked_admissible q _ htp).1
    have hu := ((parameterCheck_exact q p).mp ht).1
    simpa only [denote, RelativeTerm.eval, parameters, hu, true_and] using Epsilon.unionEpsilonCheck_exact p
  · have hkc : (.theta k a : RelativeTerm Nat).code = c := by rw [← ha]; exact hecode
    have hs : k + 1 ≤ 1 := by
      have hlow := (lowCheckCode_exact q c).mp hc
      have hs' : (rawTree c).outerSort ≤ 1 :=
        (denote_lt_iff_outerSort_le q _ (Arithmetic.raw_checked q c hi.1) 1 (by omega)).mp
          (by simpa only [Arithmetic.raw_value q c hi.1] using hi.2.2)
      simpa only [ha, RelativeTerm.outerSort] using hs'
    have hk : k = 0 := by omega
    subst k
    have ht : check q (.theta 0 a) = true := by simpa only [ha] using Arithmetic.raw_checked q c hi.1
    have hnormal : Comparison.Normal q (.theta 0 a) := by simpa only [ha] using ((Comparison.acceptedCode_exact q c).mp hn).2
    have hab := (Comparison.acceptedCode_exact q _).mp (baseCode_spec q hq).1
    have hself : checkCode q (.theta 0 a).code = true := by simpa only [← hkc] using hi.1
    have hsum : Comparison.Normal q (rawTree (.theta 0 a).code) := by simpa only [rawTree_code] using hnormal
    have he : Comparison.equalCode q (.theta 0 a).code baseCode = true ↔
        denote q (.theta 0 a) = base q := by
      rw [Comparison.equalCode_exact]
      simp only [hself, hsum, hab.1, hab.2, true_and]
      rw [interpretation_code, (baseCode_spec q hq).2]
    rw [← hkc, epsilonAtomCheck_theta_zero, Bool.or_eq_true,
      interpretation_code, theta_epsilon_iff q a ht]
    exact or_congr he (above_zero_iff q a (FixedPoint.checked_theta_argument q 0 a ht))

def word (q c : Nat) : List (RelativeTerm Nat) := Arithmetic.normalizedWord q c

theorem word_primrec : Primrec₂ word := Arithmetic.normalizedWord_primrec

def headTree (q c : Nat) : RelativeTerm Nat := (word q c).head?.getD Normalization.zeroTree

theorem headTree_primrec : Primrec₂ headTree :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp word_primrec) (Primrec.const Normalization.zeroTree)).to₂

def headCode (q c : Nat) : Nat := (headTree q c).code

theorem headCode_primrec : Primrec₂ headCode := (code_primrec.comp headTree_primrec).to₂

def offset (q c : Nat) : Nat := (word q c).tail.length

theorem offset_primrec : Primrec₂ offset := (Primrec.list_length.comp (Primrec.list_tail.comp word_primrec)).to₂

def tailCheck (q c : Nat) : Bool :=
  (word q c).tail.all (fun a => Comparison.equalCode q a.code LogEndZero.unitCode)

theorem tailCheck_primrec : Primrec₂ tailCheck := by
  have he : Primrec₂ (fun p : Nat × Nat => fun a : RelativeTerm Nat =>
      Comparison.equalCode p.1 a.code LogEndZero.unitCode) :=
    (Comparison.equalCode_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((code_primrec.comp Primrec.snd).pair (Primrec.const LogEndZero.unitCode)))).to₂
  exact ((SourceOne.Comparison.Effective.listAll_primrec _ he).comp Primrec.id
    (Primrec.list_tail.comp word_primrec)).to₂

def check (q c : Nat) : Bool := (lowCheckCode q c && decide (0 < (word q c).length)) &&
  (epsilonAtomCheck q (headCode q c) && tailCheck q c)

theorem check_primrec : Primrec₂ check :=
  (Primrec.and.comp
    (Primrec.and.comp lowCheckCode_primrec
      ((Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp word_primrec)).decide))
    (Primrec.and.comp (epsilonAtomCheck_primrec.comp Primrec.fst headCode_primrec) tailCheck_primrec)).to₂

private theorem word_atom (q c : Nat) (hc : lowCheckCode q c = true)
    (a : RelativeTerm Nat) (ha : a ∈ word q c) :
    lowCheckCode q a.code = true ∧ Comparison.acceptedCode q a.code = true ∧
      ((∃ p, rawTree a.code = .parameter p) ∨ (∃ k b, rawTree a.code = .theta k b)) := by
  have hi := HeightBoundary.input_spec q c hc
  have hs := Arithmetic.normalizedWord_spec q c hi.1
  have ht := hs.1 a ha
  have ham : denote q a ∈ canonicalANF (interpretation q c) := by
    rw [← hs.2]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hbound := (canonicalANF_mem_le ham).trans_lt hi.2.2
  have hcode : checkCode q a.code = true := by simpa only [checkCode_code] using ht.1
  refine ⟨low_of_bound q a.code hcode (by simpa only [interpretation_code] using hbound),
    (Comparison.acceptedCode_exact q _).mpr ⟨hcode, by simpa only [rawTree_code] using ht.2.1⟩, ?_⟩
  simpa only [rawTree_code] using atom_shape _ a ha

private theorem head_mem (q c : Nat) (hn : 0 < (word q c).length) : headTree q c ∈ word q c := by
  cases hw : word q c with
  | nil => simp only [hw, List.length_nil, Nat.lt_irrefl] at hn
  | cons a as => simp only [headTree, hw, List.head?_cons, Option.getD_some]; exact List.mem_cons_self

private theorem tail_mem {a : RelativeTerm Nat} (as : List (RelativeTerm Nat)) (ha : a ∈ as.tail) : a ∈ as := by
  cases as with
  | nil => simp only [List.tail_nil, List.not_mem_nil] at ha
  | cons b bs => exact List.mem_cons_of_mem _ ha

private theorem tailCheck_iff (q c : Nat) (hc : lowCheckCode q c = true) :
    tailCheck q c = true ↔ ∀ a ∈ (word q c).tail, denote q a = 1 := by
  have hq := (HeightBoundary.input_spec q c hc).2.1
  have hu := (Comparison.acceptedCode_exact q _).mp (LogEndZero.unitCode_accepted q hq)
  rw [tailCheck, List.all_eq_true]
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro ha
  have hs := word_atom q c hc a (tail_mem _ ha)
  have hn := (Comparison.acceptedCode_exact q _).mp hs.2.1
  simpa only [hn.1, hn.2, hu.1, hu.2, true_and, interpretation_code,
    LogEndZero.unitCode_value] using Comparison.equalCode_exact q a.code LogEndZero.unitCode

private theorem finite_tail_value (as : List (RelativeTerm Nat)) (q : Nat)
    (h : ∀ a ∈ as, denote q a = 1) : principalSum (as.map (denote q)) = (as.length : Ordinal.{0}) := by
  have he : as.map (denote q) = List.replicate as.length (1 : Ordinal.{0}) := by
    have hm : ∀ b ∈ as.map (denote q), b = 1 := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact h a ha
    simpa only [List.length_map] using (List.eq_replicate_length).mpr hm
  rw [he, principalSum_replicate, one_mul]

/-- Every successful original native offset parser returns the actual admitted
Normal epsilon head, original finite offset, and exact original value. -/
theorem decomposition_spec (q c : Nat) (hc : check q c = true) :
    lowCheckCode q c = true ∧ lowCheckCode q (headCode q c) = true ∧
      Comparison.acceptedCode q (headCode q c) = true ∧
      Ordinal.omega0 ^ interpretation q (headCode q c) = interpretation q (headCode q c) ∧
      interpretation q c = interpretation q (headCode q c) + (offset q c : Ordinal.{0}) := by
  obtain ⟨hg, he⟩ := Bool.and_eq_true.mp hc
  obtain ⟨hi, hn⟩ := Bool.and_eq_true.mp hg
  have hpos := decide_eq_true_eq.mp hn
  have hs := word_atom q c hi _ (head_mem q c hpos)
  have hε := (epsilonAtomCheck_correct q _ hs.1 hs.2.1 hs.2.2).mp (Bool.and_eq_true.mp he).1
  have ht := (tailCheck_iff q c hi).mp (Bool.and_eq_true.mp he).2
  have hv := (Arithmetic.normalizedWord_spec q c (HeightBoundary.input_spec q c hi).1).2
  have hsplit : interpretation q c = denote q (headTree q c) +
      principalSum ((word q c).tail.map (denote q)) := by
    rw [← principalSum_canonicalANF (interpretation q c), ← hv]
    cases hw : word q c with
    | nil => simp only [hw, List.length_nil, Nat.lt_irrefl] at hpos
    | cons a as => simp only [hw, headTree, List.head?_cons, Option.getD_some, List.tail_cons, List.map_cons, principalSum]
  refine ⟨hi, hs.1, hs.2.1, hε, ?_⟩
  simpa only [headCode, interpretation_code, offset, finite_tail_value _ q ht] using hsplit

/-- Real complete ANF uniqueness proves the parser's full original domain. -/
theorem check_exact (q c : Nat) : check q c = true ↔ lowCheckCode q c = true ∧
    ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧ interpretation q c = ε + (n : Ordinal.{0}) := by
  constructor
  · intro h
    have hs := decomposition_spec q c h
    exact ⟨hs.1, interpretation q (headCode q c), offset q c, hs.2.2.2.1, hs.2.2.2.2⟩
  · rintro ⟨hi, ε, n, hε, hv⟩
    have hw := (Arithmetic.normalizedWord_spec q c (HeightBoundary.input_spec q c hi).1).2
    change (word q c).map (denote q) = canonicalANF (interpretation q c) at hw
    rw [hv, EpsilonOffsets.canonicalANF_epsilon_add_nat hε n] at hw
    have hn : 0 < (word q c).length := by
      have h := congrArg List.length hw
      simp only [List.length_map, List.length_cons, List.length_replicate] at h
      omega
    have hh : denote q (headTree q c) = ε := by
      cases hs : word q c with
      | nil => simp only [hs, List.map_nil, List.nil_eq_cons] at hw
      | cons a as =>
        have he := List.cons.inj (by simpa only [hs, List.map_cons] using hw)
        simpa only [headTree, hs, List.head?_cons, Option.getD_some] using he.1
    have hs := word_atom q c hi _ (head_mem q c hn)
    have ht : ∀ a ∈ (word q c).tail, denote q a = 1 := by
      intro a ha
      have hm : denote q a ∈ List.replicate n (1 : Ordinal.{0}) := by
        cases hs : word q c with
        | nil => simp only [hs, List.tail_nil, List.not_mem_nil] at ha
        | cons b bs =>
          have he := List.cons.inj (by simpa only [hs, List.map_cons] using hw)
          rw [← he.2]
          exact List.mem_map.mpr ⟨a, by simpa only [hs, List.tail_cons] using ha, rfl⟩
      exact List.eq_of_mem_replicate hm
    apply Bool.and_eq_true.mpr
    refine ⟨Bool.and_eq_true.mpr ⟨hi, decide_eq_true_eq.mpr hn⟩, Bool.and_eq_true.mpr ⟨?_, (tailCheck_iff q c hi).mpr ht⟩⟩
    apply (epsilonAtomCheck_correct q _ hs.1 hs.2.1 hs.2.2).mpr
    simpa only [headCode, interpretation_code, hh] using hε

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.OmegaPowers.Offsets
