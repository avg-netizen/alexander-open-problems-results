import Alexander313.Wilken.PublicEpsilonNativeRootBelowHeadCollapseSupport

/-!
# Actual finite dispatcher for the established relative-collapse branches

The genuine original high root and checked Normal sorted argument supply
every scalar caller. Positive indices retain the original node. Index zero
dispatches actual LOW arguments, above-head calls, below-head calls and the
original divided head. The exact remaining exception is a head strictly
larger than the original divided head whose source collapse is at most the
root. That localized branch is rejected explicitly. No selected endpoint,
supplied beta code, scalar value or target admission oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootScalarCollapse

open ThetaCourse

abbrev Query := RootPositiveCollapse.Query

def headLarger (q b c : Nat) : Bool := Normalization.lessRawCode q
  (RootEndpointCollapse.deltaCode b) (RootAboveHeadCollapse.headCode c)

theorem headLarger_primrec : Primrec
    (fun p : RootAboveHeadCollapse.Query => headLarger p.1 p.2.1 p.2.2) :=
  Normalization.Effective.lessRawCode_primrec.comp (Primrec.fst.pair
    ((RootEndpointCollapse.deltaCode_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
      (RootAboveHeadCollapse.headCode_primrec.comp (Primrec.snd.comp Primrec.snd))))

theorem headLarger_exact (q b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : RootAboveHeadCollapse.argumentCheck q c = true) : headLarger q b c = true ↔
    interpretation q (RootEndpointCollapse.deltaCode b) <
      interpretation q (RootAboveHeadCollapse.headCode c) := by
  simpa only [headLarger, ((Comparison.acceptedCode_exact q _).mp
    (RootBelowHeadCollapse.delta_accepted q b hb)).1,
    ((Comparison.acceptedCode_exact q _).mp (RootBelowHeadCollapse.parts_accepted q c hc).1).1,
    true_and] using Normalization.lessRawCode_exact q
      (RootEndpointCollapse.deltaCode b) (RootAboveHeadCollapse.headCode c)

def coveredCheck (q b c : Nat) : Bool := !headLarger q b c ||
  RootAboveHeadCollapse.headAbove q b c

theorem coveredCheck_primrec : Primrec
    (fun p : RootAboveHeadCollapse.Query => coveredCheck p.1 p.2.1 p.2.2) :=
  Primrec.or.comp (Primrec.not.comp headLarger_primrec) RootAboveHeadCollapse.headAbove_primrec

/-- The true computed domain exposes exactly the larger-head localization
exception, rather than hiding it in a supplied output or notation premise. -/
theorem coveredCheck_exact (q b c : Nat) (hb : RootLowCollapse.rootCheck q b = true)
    (hc : RootAboveHeadCollapse.argumentCheck q c = true) : coveredCheck q b c = true ↔
    ¬ (interpretation q (RootEndpointCollapse.deltaCode b) <
        interpretation q (RootAboveHeadCollapse.headCode c) ∧
      globalCollapse (base q) 0 (interpretation q (RootAboveHeadCollapse.headCode c)) ≤
        interpretation q b) := by
  have hl := headLarger_exact q b c hb hc
  have ha := RootAboveHeadCollapse.headAbove_exact q b c hb hc
  simp only [coveredCheck, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro (hnot | habove) ⟨hlt, hle⟩
    · have hh := hl.mpr hlt
      simp only [hnot, Bool.false_eq_true] at hh
    · exact (not_lt_of_ge hle) (ha.mp habove)
  · intro hn
    cases hlarge : headLarger q b c with
    | false => exact Or.inl rfl
    | true =>
      apply Or.inr
      apply ha.mpr
      apply lt_of_not_ge
      intro hle
      exact hn ⟨hl.mp hlarge, hle⟩

def zeroInput (q b c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (RootAboveHeadCollapse.argumentCheck q c && coveredCheck q b c)

theorem zeroInput_primrec : Primrec
    (fun p : RootAboveHeadCollapse.Query => zeroInput p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (RootLowCollapse.rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.and.comp (RootAboveHeadCollapse.argumentCheck_primrec.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd)) coveredCheck_primrec)

theorem zeroInput_guards (q b c : Nat) (hi : zeroInput q b c = true) :
    RootLowCollapse.rootCheck q b = true ∧ RootAboveHeadCollapse.argumentCheck q c = true ∧
      coveredCheck q b c = true := by
  simpa only [zeroInput, Bool.and_eq_true, and_assoc] using hi

theorem zeroInput_exact (q b c : Nat) : zeroInput q b c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ Comparison.acceptedCode q c = true ∧
      (rawTree c).outerSort ≤ 2 ∧
      ¬ (interpretation q (RootEndpointCollapse.deltaCode b) <
          interpretation q (RootAboveHeadCollapse.headCode c) ∧
        globalCollapse (base q) 0 (interpretation q (RootAboveHeadCollapse.headCode c)) ≤
          interpretation q b) := by
  constructor
  · intro hi
    have hs := zeroInput_guards q b c hi
    have hc := (RootAboveHeadCollapse.argumentCheck_exact q c).mp hs.2.1
    exact ⟨hs.1, hc.1, hc.2, (coveredCheck_exact q b c hs.1 hs.2.1).mp hs.2.2⟩
  · rintro ⟨hb, hc, hs, he⟩
    have ha := (RootAboveHeadCollapse.argumentCheck_exact q c).mpr ⟨hc, hs⟩
    exact Bool.and_eq_true.mpr ⟨hb, Bool.and_eq_true.mpr
      ⟨ha, (coveredCheck_exact q b c hb ha).mpr he⟩⟩

theorem low_caller (q b c : Nat) (hi : zeroInput q b c = true)
    (hl : (rawTree c).outerSort ≤ 1) : RootLowCollapse.inputCheck q b c = true := by
  have hs := zeroInput_guards q b c hi
  have hc := (RootAboveHeadCollapse.argumentCheck_exact q c).mp hs.2.1
  have ht := ((Comparison.acceptedCode_exact q c).mp hc.1).1
  have he : (rawTree c).code = c := by
    obtain ⟨t, ht', hchecked⟩ := (checkCode_exact q c).mp ht
    rw [← ht', rawTree_code]
  have hlo : lowCheckCode q c = true := (lowCheckCode_exact q c).mpr
    ⟨rawTree c, he, Bool.and_eq_true.mpr
      ⟨Arithmetic.raw_checked q c ht, decide_eq_true hl⟩⟩
  exact (RootLowCollapse.inputCheck_exact q b c).mpr ⟨hs.1, hlo⟩

theorem above_caller (q b c : Nat) (hi : zeroInput q b c = true)
    (ha : RootAboveHeadCollapse.headAbove q b c = true) :
    RootAboveHeadCollapse.inputCheck q b c = true := by
  have hs := zeroInput_guards q b c hi
  exact Bool.and_eq_true.mpr ⟨hs.1, Bool.and_eq_true.mpr ⟨hs.2.1, ha⟩⟩

theorem head_positive_of_high (q c : Nat)
    (hc : RootAboveHeadCollapse.argumentCheck q c = true) (hh : 1 < (rawTree c).outerSort) :
    0 < interpretation q (RootAboveHeadCollapse.headCode c) := by
  have ha := (RootAboveHeadCollapse.argumentCheck_exact q c).mp hc
  have ht := ((Comparison.acceptedCode_exact q c).mp ha.1).1
  apply pos_iff_ne_zero.mpr
  intro hz
  have he := (RootAboveHeadCollapse.head_spec q c hc).2.2.2.2
  have hl := (RootAboveHeadCollapse.head_spec q c hc).2.2.2.1
  rw [hz, zero_add] at he
  have hv : interpretation q c < omegaSequence (base q) 1 := he ▸ hl
  rw [← Arithmetic.raw_value q c ht] at hv
  exact (not_le_of_gt hh) ((denote_lt_iff_outerSort_le q _
    (Arithmetic.raw_checked q c ht) 1 (by omega)).mp hv)

theorem below_caller (q b c : Nat) (hi : zeroInput q b c = true)
    (hh : 1 < (rawTree c).outerSort)
    (ha : RootAboveHeadCollapse.headAbove q b c = false)
    (hl : RootBelowHeadCollapse.headBelow q b c = true) :
    RootBelowHeadCollapse.inputCheck q b c = true := by
  have hs := zeroInput_guards q b c hi
  apply (RootBelowHeadCollapse.inputCheck_exact q b c).mpr
  refine ⟨hs.1, hs.2.1, head_positive_of_high q c hs.2.1 hh,
    (RootBelowHeadCollapse.headBelow_exact q b c hs.1 hs.2.1).mp hl, le_of_not_gt ?_⟩
  intro habove
  have ht := (RootAboveHeadCollapse.headAbove_exact q b c hs.1 hs.2.1).mpr habove
  simp only [ha, Bool.false_eq_true] at ht

theorem endpoint_caller (q b c : Nat) (hi : zeroInput q b c = true) :
    RootEndpointCollapse.inputCheck q b (RootBelowHeadCollapse.tailCode c) = true := by
  have hs := zeroInput_guards q b c hi
  have ht := ((Comparison.acceptedCode_exact q _).mp
    (RootBelowHeadCollapse.parts_accepted q c hs.2.1).2).1
  exact (RootLowCollapse.inputCheck_exact q b _).mpr
    ⟨hs.1, OmegaPowers.low_of_bound q _ ht (RootAboveHeadCollapse.head_spec q c hs.2.1).2.2.2.1⟩

/-- Actual failed strict tests and the actual covered guard force equality
with the original divided head; no head-equality oracle is supplied. -/
theorem endpoint_head_eq (q b c : Nat) (hi : zeroInput q b c = true)
    (ha : RootAboveHeadCollapse.headAbove q b c = false)
    (hl : RootBelowHeadCollapse.headBelow q b c = false) :
    interpretation q (RootAboveHeadCollapse.headCode c) =
      interpretation q (RootEndpointCollapse.deltaCode b) := by
  have hs := zeroInput_guards q b c hi
  apply le_antisymm
  · apply le_of_not_gt
    intro hlarge
    have hn := (coveredCheck_exact q b c hs.1 hs.2.1).mp hs.2.2
    apply hn
    refine ⟨hlarge, le_of_not_gt ?_⟩
    intro habove
    have ht := (RootAboveHeadCollapse.headAbove_exact q b c hs.1 hs.2.1).mpr habove
    simp only [ha, Bool.false_eq_true] at ht
  · apply le_of_not_gt
    intro hsmall
    have ht := (RootBelowHeadCollapse.headBelow_exact q b c hs.1 hs.2.1).mpr hsmall
    simp only [hl, Bool.false_eq_true] at ht

def zeroCode (q b c : Nat) : Nat := cond (decide ((rawTree c).outerSort ≤ 1))
  (RootLowCollapse.collapseCode q b c)
  (cond (RootAboveHeadCollapse.headAbove q b c) (RootAboveHeadCollapse.collapseCode q b c)
    (cond (RootBelowHeadCollapse.headBelow q b c) (RootBelowHeadCollapse.collapseCode q b c)
      (RootEndpointCollapse.collapseCode q b (RootBelowHeadCollapse.tailCode c))))

theorem zeroCode_primrec : Primrec
    (fun p : RootAboveHeadCollapse.Query => zeroCode p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : RootAboveHeadCollapse.Query => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlo := (Primrec.nat_le.comp (outerSort_primrec.comp (rawTree_primrec.comp hc))
    (Primrec.const 1)).decide
  have he := RootEndpointCollapse.collapseCode_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (RootBelowHeadCollapse.tailCode_primrec.comp hc)))
  exact hlo.cond RootLowCollapse.collapseCode_primrec
    (RootAboveHeadCollapse.headAbove_primrec.cond RootAboveHeadCollapse.collapseCode_primrec
      (RootBelowHeadCollapse.headBelow_primrec.cond RootBelowHeadCollapse.collapseCode_primrec he))

theorem zeroCode_spec (q b c : Nat) (hi : zeroInput q b c = true) :
    lowCheckCode q (zeroCode q b c) = true ∧ Comparison.acceptedCode q (zeroCode q b c) = true ∧
      interpretation q (zeroCode q b c) = globalCollapse (interpretation q b) 0 (interpretation q c) := by
  by_cases hl : (rawTree c).outerSort ≤ 1
  · simpa only [zeroCode, decide_eq_true hl, Bool.cond_true] using
      RootLowCollapse.collapseCode_spec q b c (low_caller q b c hi hl)
  · have hh : 1 < (rawTree c).outerSort := lt_of_not_ge hl
    cases ha : RootAboveHeadCollapse.headAbove q b c with
    | true =>
      simpa only [zeroCode, decide_eq_false hl, ha, Bool.cond_true, Bool.cond_false] using
        RootAboveHeadCollapse.collapseCode_spec q b c (above_caller q b c hi ha)
    | false =>
      cases hb : RootBelowHeadCollapse.headBelow q b c with
      | true =>
        simpa only [zeroCode, decide_eq_false hl, ha, hb, Bool.cond_true, Bool.cond_false] using
          RootBelowHeadCollapse.collapseCode_spec q b c (below_caller q b c hi hh ha hb)
      | false =>
        have he := endpoint_head_eq q b c hi ha hb
        have hc := RootEndpointCollapse.collapseCode_spec q b (RootBelowHeadCollapse.tailCode c)
          (endpoint_caller q b c hi)
        have hparts := (RootAboveHeadCollapse.head_spec q c (zeroInput_guards q b c hi).2.1).2.2.2.2
        have hv : interpretation q (RootEndpointCollapse.deltaCode b) +
            interpretation q (RootBelowHeadCollapse.tailCode c) = interpretation q c := by
          rw [← he]; exact hparts
        simpa only [zeroCode, decide_eq_false hl, ha, hb, Bool.cond_false, hv] using hc

def inputCheck (q b k c : Nat) : Bool := cond (decide (0 < k))
  (RootPositiveCollapse.inputCheck q b k c) (zeroInput q b c)

theorem inputCheck_primrec : Primrec (fun p : Query => inputCheck p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hk : Primrec (fun p : Query => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hzero := zeroInput_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact ((Primrec.nat_lt.comp (Primrec.const 0) hk).decide).cond
    RootPositiveCollapse.inputCheck_primrec hzero

/-- EVERY original positive-index call is accepted. At index zero ONLY
the genuine larger-head/source-collapse-at-most-beta branch is excluded. -/
theorem inputCheck_exact (q b k c : Nat) : inputCheck q b k c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ Comparison.acceptedCode q c = true ∧
      (rawTree c).outerSort ≤ k + 2 ∧
      (0 < k ∨ ¬ (interpretation q (RootEndpointCollapse.deltaCode b) <
          interpretation q (RootAboveHeadCollapse.headCode c) ∧
        globalCollapse (base q) 0 (interpretation q (RootAboveHeadCollapse.headCode c)) ≤
          interpretation q b)) := by
  by_cases hk : 0 < k
  · simp only [inputCheck, decide_eq_true hk, Bool.cond_true, RootPositiveCollapse.inputCheck_exact,
      hk, true_or, and_true, true_and]
  · have he : k = 0 := by omega
    subst k
    simpa only [inputCheck, decide_eq_false hk, Bool.cond_false, Nat.zero_add,
      hk, false_or] using zeroInput_exact q b c

def collapseCode (q b k c : Nat) : Nat := cond (inputCheck q b k c)
  (cond (decide (0 < k)) (RootPositiveCollapse.collapseCode q b k c) (zeroCode q b c)) 0

theorem collapseCode_primrec : Primrec (fun p : Query => collapseCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hk : Primrec (fun p : Query => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hz := zeroCode_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact inputCheck_primrec.cond (((Primrec.nat_lt.comp (Primrec.const 0) hk).decide).cond
    RootPositiveCollapse.collapseCode_primrec hz) (Primrec.const 0)

theorem collapseCode_spec (q b k c : Nat) (hi : inputCheck q b k c = true) :
    Comparison.acceptedCode q (collapseCode q b k c) = true ∧
      interpretation q (collapseCode q b k c) = globalCollapse (interpretation q b) k (interpretation q c) := by
  by_cases hk : 0 < k
  · have hp : RootPositiveCollapse.inputCheck q b k c = true := by
      simpa only [inputCheck, decide_eq_true hk, Bool.cond_true] using hi
    simpa only [collapseCode, hi, decide_eq_true hk, Bool.cond_true] using
      RootPositiveCollapse.collapseCode_spec q b k c hp
  · have he : k = 0 := by omega
    subst k
    have hz : zeroInput q b c = true := by
      simpa only [inputCheck, decide_eq_false hk, Bool.cond_false] using hi
    simpa only [collapseCode, hi, decide_eq_false hk, Bool.cond_true, Bool.cond_false] using
      (zeroCode_spec q b c hz).2

theorem collapseCode_zero_low (q b c : Nat) (hi : inputCheck q b 0 c = true) :
    lowCheckCode q (collapseCode q b 0 c) = true := by
  have hk : ¬ (0 < (0 : Nat)) := Nat.lt_irrefl _
  have hz : zeroInput q b c = true := by
    simpa only [inputCheck, decide_eq_false hk, Bool.cond_false] using hi
  simpa only [collapseCode, hi, decide_eq_false hk, Bool.cond_true, Bool.cond_false] using
    (zeroCode_spec q b c hz).1

theorem collapseCode_rejected (q b k c : Nat) (hi : inputCheck q b k c = false) :
    collapseCode q b k c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootScalarCollapse
