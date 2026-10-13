import Alexander313.Wilken.PublicEpsilonNativeRootLocalizedCollapseSupport

/-!
# Complete finite scalar collapse at the ORIGINAL coded context

Every original checked Normal high root and every original checked Normal
argument of the actual theta sort are accepted. The established branches
and the genuine selected-support localized branch supply every caller.
The executing finite producer proves the relative scalar value and original
Normal admission without an endpoint, cutoff or representative oracle.
This is scalar construction, not a full term recoder. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootCompleteScalarCollapse

open ThetaCourse

abbrev Query := RootPositiveCollapse.Query

def inputCheck (q b k c : Nat) : Bool := RootLowCollapse.rootCheck q b &&
  (Comparison.acceptedCode q c && decide ((rawTree c).outerSort ≤ k + 2))

theorem inputCheck_primrec : Primrec
    (fun p : Query => inputCheck p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hk : Primrec (fun p : Query => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Query => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp
    (RootLowCollapse.rootCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.and.comp (Comparison.acceptedCode_primrec.comp Primrec.fst hc)
      ((Primrec.nat_le.comp (outerSort_primrec.comp (rawTree_primrec.comp hc))
        (Primrec.nat_add.comp hk (Primrec.const 2))).decide))

/-- The exact ORIGINAL domain has no omitted scalar branch. -/
theorem inputCheck_exact (q b k c : Nat) : inputCheck q b k c = true ↔
    RootLowCollapse.rootCheck q b = true ∧ Comparison.acceptedCode q c = true ∧
      (rawTree c).outerSort ≤ k + 2 := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def knownBranch (q b k c : Nat) : Bool := decide (0 < k) || RootScalarCollapse.coveredCheck q b c

theorem knownBranch_primrec : Primrec
    (fun p : Query => knownBranch p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hk : Primrec (fun p : Query => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcovered := RootScalarCollapse.coveredCheck_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.or.comp ((Primrec.nat_lt.comp (Primrec.const 0) hk).decide) hcovered

theorem zero_argument (q b c : Nat) (hi : inputCheck q b 0 c = true) :
    RootAboveHeadCollapse.argumentCheck q c = true :=
  (RootAboveHeadCollapse.argumentCheck_exact q c).mpr
    ⟨((inputCheck_exact q b 0 c).mp hi).2.1,
      by simpa only [Nat.zero_add] using ((inputCheck_exact q b 0 c).mp hi).2.2⟩

theorem scalar_caller (q b k c : Nat) (hi : inputCheck q b k c = true)
    (hb : knownBranch q b k c = true) : RootScalarCollapse.inputCheck q b k c = true := by
  have h := (inputCheck_exact q b k c).mp hi
  apply (RootScalarCollapse.inputCheck_exact q b k c).mpr
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  by_cases hk : 0 < k
  · exact Or.inl hk
  · have he : k = 0 := by omega
    subst k
    have hz : RootScalarCollapse.coveredCheck q b c = true := by
      simpa only [knownBranch, decide_eq_false hk, Bool.false_or] using hb
    exact Or.inr ((RootScalarCollapse.coveredCheck_exact q b c h.1
      (zero_argument q b c hi)).mp hz)

theorem localized_index (q b k c : Nat) (hb : knownBranch q b k c = false) : k = 0 := by
  by_contra hn
  have hk : 0 < k := Nat.pos_of_ne_zero hn
  simp only [knownBranch, decide_eq_true hk, Bool.true_or, Bool.true_eq_false] at hb

theorem localized_caller (q b k c : Nat) (hi : inputCheck q b k c = true)
    (hb : knownBranch q b k c = false) : RootLocalizedCollapse.inputCheck q b c = true := by
  have he := localized_index q b k c hb
  subst k
  have h := (inputCheck_exact q b 0 c).mp hi
  have hz : RootScalarCollapse.coveredCheck q b c = false := by
    simpa only [knownBranch, decide_eq_false (Nat.lt_irrefl 0), Bool.false_or] using hb
  have hg : RootScalarCollapse.headLarger q b c = true ∧
      RootAboveHeadCollapse.headAbove q b c = false := by
    simpa only [RootScalarCollapse.coveredCheck, Bool.or_eq_false_iff, Bool.not_eq_false'] using hz
  exact Bool.and_eq_true.mpr ⟨h.1, Bool.and_eq_true.mpr
    ⟨zero_argument q b c hi, Bool.and_eq_true.mpr ⟨hg.1,
      by simpa only [hg.2, Bool.not_false]⟩⟩⟩

def collapseCode (q b k c : Nat) : Nat := cond (inputCheck q b k c)
  (cond (knownBranch q b k c) (RootScalarCollapse.collapseCode q b k c)
    (RootLocalizedCollapse.collapseCode q b c)) 0

theorem collapseCode_primrec : Primrec
    (fun p : Query => collapseCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hl := RootLocalizedCollapse.collapseCode_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact inputCheck_primrec.cond
    (knownBranch_primrec.cond RootScalarCollapse.collapseCode_primrec hl) (Primrec.const 0)

/-- Every genuine relative scalar value has an executing original-q
checked Normal representation, at the same positive index or at zero. -/
theorem collapseCode_spec (q b k c : Nat) (hi : inputCheck q b k c = true) :
    Comparison.acceptedCode q (collapseCode q b k c) = true ∧
      interpretation q (collapseCode q b k c) = globalCollapse (interpretation q b) k (interpretation q c) := by
  cases hb : knownBranch q b k c with
  | true =>
    simpa only [collapseCode, hi, hb, Bool.cond_true] using
      RootScalarCollapse.collapseCode_spec q b k c (scalar_caller q b k c hi hb)
  | false =>
    have he := localized_index q b k c hb
    simpa only [collapseCode, hi, hb, Bool.cond_true, Bool.cond_false, he] using
      (RootLocalizedCollapse.collapseCode_spec q b c (localized_caller q b k c hi hb)).2

theorem collapseCode_zero_low (q b c : Nat) (hi : inputCheck q b 0 c = true) :
    lowCheckCode q (collapseCode q b 0 c) = true := by
  cases hb : knownBranch q b 0 c with
  | true =>
    simpa only [collapseCode, hi, hb, Bool.cond_true] using
      RootScalarCollapse.collapseCode_zero_low q b c (scalar_caller q b 0 c hi hb)
  | false =>
    simpa only [collapseCode, hi, hb, Bool.cond_true, Bool.cond_false] using
      (RootLocalizedCollapse.collapseCode_spec q b c (localized_caller q b 0 c hi hb)).1

theorem collapseCode_rejected (q b k c : Nat) (hi : inputCheck q b k c = false) :
    collapseCode q b k c = 0 := by simp only [collapseCode, hi, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.RootCompleteScalarCollapse
