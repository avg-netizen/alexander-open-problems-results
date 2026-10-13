import Alexander313.Wilken.HereditaryNativeElementaryPublicReturnSupport
import Alexander313.Wilken.HereditaryNativeLambdaSourceReturn

/-!
# A genuine PR same-value public return on the elementary native fragment

The original native parser and a literal finite syntax test admit exactly the
checked trees containing only zero-index theta calls, including their hidden
arguments. A finite fold replaces parameters by actual canonical public
payloads, sums by public addition, and each low-argument zero-index call by
the actual corrected public collapse value proved in the support module.
Every local cardinal bound is derived from this original checked syntax.

This is a partial term translator at ANY original coded epsilon, with genuine
public canonical output and SAME ordinal value. The omitted branch is a
zero-index call with a hidden positive-index argument; no full bounded [55]
translator or full lambda/public tracking return is asserted. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ElementaryPublicReturn

open ThetaCourse
open Alexander313.HereditaryOrdinalLabels (zeroCode)

def elementaryTheta (_ : Unit) (k : Nat) (b : Bool) : Bool := (k == 0) && b

theorem elementaryTheta_primrec : Primrec
    (fun p : Unit × (Nat × Bool) => elementaryTheta p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (Primrec.snd.comp Primrec.snd)

/-- A finite original-syntax test; hidden theta arguments are fully inspected. -/
def elementaryCheck (t : RelativeTerm Nat) : Bool :=
  ValueFold.term (fun (_ : Unit) (_ : Nat) => true) (fun a b => a && b) elementaryTheta () t

theorem elementaryCheck_primrec : Primrec elementaryCheck :=
  (ValueFold.term_primrec (fun (_ : Unit) (_ : Nat) => true) (fun a b => a && b)
    elementaryTheta false (Primrec.const true).to₂ Primrec.and.to₂ elementaryTheta_primrec).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem elementaryCheck_parameter (p : Nat) : elementaryCheck (.parameter p) = true := rfl
@[simp] theorem elementaryCheck_sum (t u : RelativeTerm Nat) :
    elementaryCheck (.sum t u) = (elementaryCheck t && elementaryCheck u) := rfl
@[simp] theorem elementaryCheck_theta (k : Nat) (t : RelativeTerm Nat) :
    elementaryCheck (.theta k t) = ((k == 0) && elementaryCheck t) := rfl

/-- The admitted fragment itself derives the sort of EVERY recursive argument. -/
theorem elementary_outerSort (t : RelativeTerm Nat) (ht : elementaryCheck t = true) :
    t.outerSort ≤ 1 := by
  induction t with
  | parameter p => exact Nat.zero_le _
  | sum t u iht ihu =>
    have hs := Bool.and_eq_true.mp ht
    have ha := iht hs.1
    have hb := ihu hs.2
    simpa only [RelativeTerm.outerSort, max_le_iff] using And.intro ha hb
  | theta k t ih =>
    have hs := Bool.and_eq_true.mp ht
    have hk : k = 0 := beq_iff_eq.mp hs.1
    simp only [hk, RelativeTerm.outerSort, Nat.zero_add, le_refl]

def publicTheta (q k w : Nat) : Nat := cond (k == 0) (collapseCode q w) zeroCode

theorem publicTheta_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => publicTheta p.1 p.2.1 p.2.2) :=
  (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).cond
    (collapseCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)) (Primrec.const zeroCode)

/-- The entire actual public-value producer is a finite primitive-recursive fold. -/
def publicTerm (q : Nat) (t : RelativeTerm Nat) : Nat :=
  ValueFold.term (fun (_ : Nat) p => Canonical.canonicalize p)
    CanonicalArithmetic.canonicalSum publicTheta q t

theorem publicTerm_primrec : Primrec₂ publicTerm :=
  ValueFold.term_primrec (fun (_ : Nat) p => Canonical.canonicalize p)
    CanonicalArithmetic.canonicalSum publicTheta zeroCode
    (Canonical.Effective.canonicalize_primrec.comp Primrec.snd).to₂
    CanonicalArithmetic.canonicalSum_primrec publicTheta_primrec

@[simp] theorem publicTerm_parameter (q p : Nat) :
    publicTerm q (.parameter p) = Canonical.canonicalize p := rfl
@[simp] theorem publicTerm_sum (q : Nat) (t u : RelativeTerm Nat) :
    publicTerm q (.sum t u) = CanonicalArithmetic.canonicalSum (publicTerm q t) (publicTerm q u) := rfl
@[simp] theorem publicTerm_theta_zero (q : Nat) (t : RelativeTerm Nat) :
    publicTerm q (.theta 0 t) = collapseCode q (publicTerm q t) := rfl

private theorem sum_checks (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q (.sum t u) = true) : check q t = true ∧ check q u = true := by
  have hq := (Bool.and_eq_true.mp ht).1
  have had := checked_admissible q (.sum t u) ht
  cases had.2 with
  | sum ht hu =>
    exact ⟨Comparison.admitted_checked q _ hq t ⟨had.1.1, ht⟩,
      Comparison.admitted_checked q _ hq u ⟨had.1.2, hu⟩⟩

/-- Original check and the literal fragment test alone construct a canonical
public value. No supplied public representative or semantic caller is needed. -/
theorem publicTerm_spec (q : Nat) (t : RelativeTerm Nat) (ht : check q t = true)
    (he : elementaryCheck t = true) :
    Canonical.check (publicTerm q t) = true ∧ unionInterpretation (publicTerm q t) = denote q t := by
  revert ht he
  induction t with
  | parameter p =>
    intro ht he
    have hp := ((parameterCheck_exact q p).mp (checked_admissible q _ ht).1).1
    exact ⟨Canonical.canonicalize_check p hp, Canonical.canonicalize_value p hp⟩
  | sum t u iht ihu =>
    intro ht he
    have hs := sum_checks q t u ht
    have hfrag := Bool.and_eq_true.mp he
    have ha := iht hs.1 hfrag.1
    have hb := ihu hs.2 hfrag.2
    exact ⟨CanonicalArithmetic.canonicalSum_checked _ _ (Canonical.check_original ha.1)
      (Canonical.check_original hb.1),
      (CanonicalArithmetic.canonicalSum_value _ _ (Canonical.check_original ha.1)
        (Canonical.check_original hb.1)).trans (by rw [ha.2, hb.2]; rfl)⟩
  | theta k t ih =>
    intro ht he
    have hfrag := Bool.and_eq_true.mp he
    have hk : k = 0 := beq_iff_eq.mp hfrag.1
    subst k
    have hq := (Bool.and_eq_true.mp ht).1
    have hc := FixedPoint.checked_theta_argument q 0 t ht
    have ha := ih hc hfrag.2
    have hb : unionInterpretation (publicTerm q t) < omegaSequence (base q) 1 := by
      rw [ha.2]
      exact (denote_lt_iff_outerSort_le q t hc 1 (by omega)).mpr (elementary_outerSort t hfrag.2)
    have hs := collapseCode_spec q _ hq (Canonical.check_original ha.1) hb
    exact ⟨hs.1, hs.2.trans (congrArg (globalCollapse (base q) 0) ha.2)⟩

/-- EXACT original fragment guard, including original native admission. -/
def inputCheck (q c : Nat) : Bool := checkCode q c && elementaryCheck (rawTree c)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp checkCode_primrec
    (elementaryCheck_primrec.comp (rawTree_primrec.comp Primrec.snd))).to₂

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    checkCode q c = true ∧ elementaryCheck (rawTree c) = true := Bool.and_eq_true

def returnCode (q c : Nat) : Nat := cond (inputCheck q c) (publicTerm q (rawTree c)) 0

theorem returnCode_primrec : Primrec₂ returnCode :=
  (inputCheck_primrec.cond (publicTerm_primrec.comp Primrec.fst
    (rawTree_primrec.comp Primrec.snd)) (Primrec.const 0)).to₂

theorem returnCode_spec (q c : Nat) (hc : inputCheck q c = true) :
    Canonical.check (returnCode q c) = true ∧ unionInterpretation (returnCode q c) = interpretation q c := by
  have hs := (inputCheck_exact q c).mp hc
  have hr := publicTerm_spec q (rawTree c) (Arithmetic.raw_checked q c hs.1) hs.2
  simpa only [returnCode, hc, Bool.cond_true, Arithmetic.raw_value q c hs.1] using hr

theorem returnCode_rejected (q c : Nat) (hc : inputCheck q c = false) : returnCode q c = 0 := by
  simp only [returnCode, hc, Bool.cond_false]

/-- The derived SAME value has an actual original canonical public code;
the public endpoint bound follows from that produced code, not a room oracle. -/
theorem returnCode_lt_public_limit (q c : Nat) (hc : inputCheck q c = true) :
    interpretation q c < finiteBaseLimit := by
  have hs := returnCode_spec q c hc
  exact hs.2 ▸ (lt_finiteBaseLimit_iff_code _).mpr
    ⟨returnCode q c, Canonical.check_original hs.1, rfl⟩

theorem returnCode_invariant (q c r d : Nat) (hc : inputCheck q c = true)
    (hd : inputCheck r d = true) (he : interpretation q c = interpretation r d) :
    returnCode q c = returnCode r d := by
  have hs := returnCode_spec q c hc
  have ht := returnCode_spec r d hd
  exact Canonical.check_value_injective _ _ hs.1 ht.1 (hs.2.trans (he.trans ht.2.symm))

/-- Actual normal lambda callers derive native admission. The explicit
fragment hypothesis honestly marks the partial translator's remaining scope. -/
theorem lambda_return_spec (s a out : Nat) (ho : out ∈ Lambda.Branches.execute s a)
    (he : elementaryCheck (rawTree out) = true) :
    Canonical.check (returnCode (Lambda.Branches.outputContext s a) out) = true ∧
      unionInterpretation (returnCode (Lambda.Branches.outputContext s a) out) =
        interpretation (Lambda.Branches.outputContext s a) out := by
  have hs := Lambda.Branches.execute_spec s a out ho
  exact returnCode_spec _ _ ((inputCheck_exact _ _).mpr
    ⟨((Comparison.acceptedCode_exact _ _).mp hs.2.1).1, he⟩)

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ElementaryPublicReturn
