import Alexander313.Wilken.HereditaryNativeLowArithmetic
import Alexander313.Wilken.HereditaryNativeRightSubtraction
import Alexander313.Wilken.HereditaryNativeSourceChiArithmetic
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance
import Alexander313.Wilken.HereditaryExponentDecomposition

/-!
# Executing source rho at the same positive public epsilon

Every original native LOW input returns to the public level s+1. The actual
canonical logend search and omega-left finite decomposition produce lambda+k,
with lambda zero or a genuine limit. The canonical prefix returns to the SAME
native context as an originally admitted weak-normal expression. Its actual
chi is encoded as the admitted numeral zero or one. Genuine dotted RIGHT
subtraction acts on the ENTIRE logend, and the existing low multiplication
search executes the product with the actual base. All caller bounds are derived.

The constructed lambda expression is explicit. The derived same-context chi
value-invariance theorem also proves the formula for ANY original normal
expression of that lambda value. Source3.12's canonical height inequality
is a separate, unproved claim.
Search execution and its literal numerical graph are Partrec, with no global
PR search bound or arbitrary-epsilon/full-sort arithmetic claim. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho

open NativePublicBridge (contextCode contextCode_value contextCode_checked)

def inputCheck (s c : Nat) : Bool := LowArithmetic.lowInput s c

theorem inputCheck_primrec : Primrec₂ inputCheck := LowArithmetic.lowInput_primrec

def logCode (p : Nat) : Nat := p.unpair.1
def decomposition (p : Nat) : Nat := p.unpair.2

theorem logCode_primrec : Primrec logCode := Primrec.fst.comp Primrec.unpair
theorem decomposition_primrec : Primrec decomposition := Primrec.snd.comp Primrec.unpair

/-- The packed data is an ACTUAL canonical log output and an ACTUAL
executing finite-tail decomposition, not a supplied semantic witness. -/
def prepare (s c : Nat) : Part Nat := cond (inputCheck s c)
  ((LogEnd.logend (LowArithmetic.publicCode s c)).bind (fun l =>
    (ExponentDecomposition.decompose l).map (Nat.pair l))) Part.none

theorem prepare_partrec : Partrec₂ prepare := by
  have hd : Partrec (fun p : (Nat × Nat) × Nat => ExponentDecomposition.decompose p.2) :=
    ExponentDecomposition.decompose_partrec.comp Computable.snd
  have hp := hd.map (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp.to₂
  exact (Partrec.cond inputCheck_primrec.to_comp
    ((LogEnd.logend_partrec.comp LowArithmetic.publicCode_primrec.to_comp).bind hp.to₂)
    Partrec.none).to₂

structure Prepared (s c p : Nat) : Prop where
  input : inputCheck s c = true
  logarithm : logCode p ∈ LogEnd.logend (LowArithmetic.publicCode s c)
  data : decomposition p ∈ ExponentDecomposition.decompose (logCode p)

theorem prepare_exact (s c p : Nat) : p ∈ prepare s c ↔ Prepared s c p := by
  cases hi : inputCheck s c with
  | false =>
    simp only [prepare, hi, Bool.cond_false, Part.notMem_none]
    exact ⟨False.elim, fun h => Bool.noConfusion (hi.symm.trans h.input)⟩
  | true =>
    simp only [prepare, hi, Bool.cond_true]
    constructor
    · intro h
      obtain ⟨l, hl, hm⟩ := Part.mem_bind_iff.mp h
      obtain ⟨d, hd, he⟩ := (Part.mem_map_iff (Nat.pair l)).mp hm
      subst p
      exact ⟨hi, by simpa only [logCode, Nat.unpair_pair] using hl,
        by simpa only [logCode, decomposition, Nat.unpair_pair] using hd⟩
    · intro h
      apply Part.mem_bind_iff.mpr
      refine ⟨logCode p, h.logarithm, ?_⟩
      apply (Part.mem_map_iff (Nat.pair (logCode p))).mpr
      exact ⟨decomposition p, h.data, Nat.pair_unpair p⟩

theorem prepare_returns (s c : Nat) (hc : inputCheck s c = true) :
    ∃ p, p ∈ prepare s c := by
  have hu := LowArithmetic.publicCode_spec s c hc
  obtain ⟨l, hl, hcanon, _⟩ := LogEnd.componentLog_returns true _ hu.1
  obtain ⟨d, hd, _⟩ := ExponentDecomposition.decompose_returns l (Canonical.check_original hcanon)
  refine ⟨Nat.pair l d, (prepare_exact s c _).mpr ?_⟩
  exact ⟨hc, by simpa only [logCode, Nat.unpair_pair, LogEnd.logend] using hl,
    by simpa only [logCode, decomposition, Nat.unpair_pair] using hd⟩

theorem prepare_domain (s c : Nat) : (prepare s c).Dom ↔ inputCheck s c = true := by
  rw [Part.dom_iff_mem]
  exact ⟨fun ⟨p, hp⟩ => ((prepare_exact s c p).mp hp).input, prepare_returns s c⟩

def lambdaCode (s p : Nat) : Nat := LowArithmetic.returnCode s
  (ExponentDecomposition.«prefix» (decomposition p))
def logNativeCode (s p : Nat) : Nat := LowArithmetic.returnCode s (logCode p)
def remainder (p : Nat) : Nat := ExponentDecomposition.offset (decomposition p)
def chi (s p : Nat) : Bool := SourceChi.chiCode (contextCode s) (lambdaCode s p)
def chiNat (s p : Nat) : Nat := cond (chi s p) 1 0
def chiCode (s p : Nat) : Nat := LowArithmetic.returnCode s
  (CanonicalArithmetic.numeralCode (chiNat s p))

theorem lambdaCode_primrec : Primrec₂ lambdaCode :=
  (LowArithmetic.returnCode_primrec.comp Primrec.fst
    (ExponentDecomposition.prefix_primrec.comp (decomposition_primrec.comp Primrec.snd))).to₂
theorem logNativeCode_primrec : Primrec₂ logNativeCode :=
  (LowArithmetic.returnCode_primrec.comp Primrec.fst (logCode_primrec.comp Primrec.snd)).to₂
theorem remainder_primrec : Primrec remainder := ExponentDecomposition.offset_primrec.comp decomposition_primrec
theorem chi_primrec : Primrec₂ chi :=
  (SourceChi.chiCode_primrec.comp (NativePublicBridge.contextCode_primrec.comp Primrec.fst) lambdaCode_primrec).to₂
theorem chiNat_primrec : Primrec₂ chiNat := (chi_primrec.cond (Primrec.const 1) (Primrec.const 0)).to₂
theorem chiCode_primrec : Primrec₂ chiCode :=
  (LowArithmetic.returnCode_primrec.comp Primrec.fst
    (CanonicalArithmetic.numeralCode_primrec.comp chiNat_primrec)).to₂

theorem chiNat_le_one (s p : Nat) : chiNat s p ≤ 1 := by
  cases h : chi s p <;> simp only [chiNat, h, Bool.cond_false, Bool.cond_true] <;> omega

theorem prepared_log_bound (s c p : Nat) (hp : Prepared s c p) :
    unionInterpretation (logCode p) ≤ interpretation (contextCode s) c := by
  have hu := LowArithmetic.publicCode_spec s c hp.input
  exact (LogEnd.componentLog_bound true _ _ hp.logarithm).trans_eq hu.2

theorem prepared_prefix_bound (s c p : Nat) (hp : Prepared s c p) :
    unionInterpretation (ExponentDecomposition.«prefix» (decomposition p)) ≤ unionInterpretation (logCode p) := by
  have hd := ExponentDecomposition.decompose_value _ _ hp.data
  exact le_self_add.trans_eq hd.2.2.2.2.symm

theorem prepared_returns (s c p : Nat) (hp : Prepared s c p) :
    (LowArithmetic.lowInput s (logNativeCode s p) = true ∧
      Comparison.acceptedCode (contextCode s) (logNativeCode s p) = true ∧
      interpretation (contextCode s) (logNativeCode s p) = unionInterpretation (logCode p)) ∧
    (LowArithmetic.lowInput s (lambdaCode s p) = true ∧
      Comparison.acceptedCode (contextCode s) (lambdaCode s p) = true ∧
      interpretation (contextCode s) (lambdaCode s p) =
        unionInterpretation (ExponentDecomposition.«prefix» (decomposition p))) := by
  have hl := LogEnd.logend_value _ _ hp.logarithm
  have hd := ExponentDecomposition.decompose_value _ _ hp.data
  have hb := (prepared_log_bound s c p hp).trans_lt (LowArithmetic.lowInput_bound s c hp.input)
  exact ⟨LowArithmetic.returnCode_spec s _ hl.2.1 hb,
    LowArithmetic.returnCode_spec s _ hd.2.2.1 ((prepared_prefix_bound s c p hp).trans_lt hb)⟩

theorem lambda_zero_or_limit (s c p : Nat) (hp : Prepared s c p) :
    interpretation (contextCode s) (lambdaCode s p) = 0 ∨
      _root_.Order.IsSuccLimit (interpretation (contextCode s) (lambdaCode s p)) := by
  have hd := ExponentDecomposition.decompose_value _ _ hp.data
  rw [(prepared_returns s c p hp).2.2.2, hd.2.2.2.1]
  exact OrdinalPowerArithmetic.omega_finite_prefix_zero_or_limit _

theorem log_split (s c p : Nat) (hp : Prepared s c p) :
    interpretation (contextCode s) (logNativeCode s p) =
      interpretation (contextCode s) (lambdaCode s p) + (remainder p : Ordinal.{0}) := by
  have hd := ExponentDecomposition.decompose_value _ _ hp.data
  rw [(prepared_returns s c p hp).1.2.2, (prepared_returns s c p hp).2.2.2]
  exact hd.2.2.2.2

theorem chiCode_spec (s p : Nat) : LowArithmetic.lowInput s (chiCode s p) = true ∧
    Comparison.acceptedCode (contextCode s) (chiCode s p) = true ∧
      interpretation (contextCode s) (chiCode s p) = (chiNat s p : Ordinal.{0}) := by
  have hbase : (1 : Ordinal.{0}) < finiteBase ((s + 1) + 1) := by
    have h : (1 : Ordinal.{0}) < finiteBase 1 := by
      simpa only [finiteBase_zero] using finiteBase_step 0
    exact h.trans_le (finiteBase_strictMono.monotone (by omega : 1 ≤ (s + 1) + 1))
  have hn : (chiNat s p : Ordinal.{0}) ≤ 1 := by exact_mod_cast chiNat_le_one s p
  have hr := LowArithmetic.returnCode_spec s _ (CanonicalArithmetic.numeralCode_checked _)
    (by rw [CanonicalArithmetic.numeralCode_value]; exact hn.trans_lt hbase)
  exact ⟨hr.1, hr.2.1, hr.2.2.trans (CanonicalArithmetic.numeralCode_value _)⟩

/-- The base is returned as a genuine theta expression; it is NOT inserted
as a native parameter, which would fail the strict parameter bound. -/
def baseCode (s : Nat) : Nat := LowArithmetic.returnCode s (Canonical.canonicalize (contextCode s))

theorem baseCode_primrec : Primrec baseCode :=
  LowArithmetic.returnCode_primrec.comp Primrec.id
    (Canonical.Effective.canonicalize_primrec.comp NativePublicBridge.contextCode_primrec)

theorem baseCode_spec (s : Nat) : LowArithmetic.lowInput s (baseCode s) = true ∧
    Comparison.acceptedCode (contextCode s) (baseCode s) = true ∧
      interpretation (contextCode s) (baseCode s) = base (contextCode s) := by
  have hu := NativePublicBridge.baseCode_original (s + 1)
  have hv := Canonical.canonicalize_value (contextCode s) hu
  have hb : unionInterpretation (Canonical.canonicalize (contextCode s)) < finiteBase ((s + 1) + 1) := by
    rw [hv]
    change base (contextCode s) < _
    rw [contextCode_value]
    exact finiteBase_step (s + 1)
  have hr := LowArithmetic.returnCode_spec s _ (Canonical.canonicalize_check _ hu) hb
  exact ⟨hr.1, hr.2.1, hr.2.2.trans hv⟩

private theorem checked_low_of_bound (s out : Nat) (hc : checkCode (contextCode s) out = true)
    (hb : interpretation (contextCode s) out < finiteBase ((s + 1) + 1)) :
    LowArithmetic.lowInput s out = true := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_exact (contextCode s) out).mp hc
  have hsort : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le (contextCode s) t ht 1 (by omega)).mp (by
    rw [contextCode_value]
    exact (by simpa only [interpretation_code] using hb).trans_lt (finiteBase_lt_cardinal (s + 1)))
  simpa only [LowArithmetic.lowInput, lowCheckCode_code, lowCheck, ht, hsort, decide_true, Bool.true_and]

def subtractCode (s p : Nat) : Nat := RightSubtraction.rightCode (contextCode s)
  (logNativeCode s p) (chiCode s p)

theorem subtractCode_primrec : Primrec₂ subtractCode :=
  (RightSubtraction.rightCode_primrec.comp
    ((NativePublicBridge.contextCode_primrec.comp Primrec.fst).pair
      (logNativeCode_primrec.pair chiCode_primrec))).to₂

theorem subtractCode_spec (s c p : Nat) (hp : Prepared s c p) :
    LowArithmetic.lowInput s (subtractCode s p) = true ∧
      Comparison.acceptedCode (contextCode s) (subtractCode s p) = true ∧
      interpretation (contextCode s) (subtractCode s p) = OrdinalRightSubtraction.rightSubtract
        (unionInterpretation (logCode p)) (chiNat s p : Ordinal.{0}) := by
  have hl := (prepared_returns s c p hp).1
  have hb := chiCode_spec s p
  have hc := (Comparison.acceptedCode_exact _ _).mp hl.2.1
  have hd := (Comparison.acceptedCode_exact _ _).mp hb.2.1
  have hs := RightSubtraction.rightCode_spec _ _ _ hc.1 hd.1
  have he : interpretation (contextCode s) (subtractCode s p) =
      OrdinalRightSubtraction.rightSubtract (unionInterpretation (logCode p)) (chiNat s p : Ordinal.{0}) := by
    simpa only [subtractCode, hl.2.2, hb.2.2] using hs.2.1
  have hsmall : interpretation (contextCode s) (subtractCode s p) < finiteBase ((s + 1) + 1) := by
    rw [he]
    exact ((OrdinalRightSubtraction.rightSubtract_le _ _).trans (prepared_log_bound s c p hp)).trans_lt
      (LowArithmetic.lowInput_bound s c hp.input)
  exact ⟨checked_low_of_bound s _ ((Comparison.acceptedCode_exact _ _).mp hs.1).1 hsmall, hs.1, he⟩

def step (s p : Nat) : Part Nat := LowArithmetic.operation 0 s (baseCode s) (subtractCode s p)

theorem step_partrec : Partrec₂ step :=
  (LowArithmetic.operation_partrec.comp
    (((Primrec.const 0).pair Primrec.fst).pair ((baseCode_primrec.comp Primrec.fst).pair subtractCode_primrec)).to_comp).to₂

def rho (s c : Nat) : Part Nat := (prepare s c).bind (step s)

theorem rho_partrec : Partrec₂ rho :=
  (prepare_partrec.bind (step_partrec.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).to₂

theorem rho_spec (s c out : Nat) (ho : out ∈ rho s c) :
    inputCheck s c = true ∧ LowArithmetic.lowInput s out = true ∧
      Comparison.acceptedCode (contextCode s) out = true ∧
      ∃ p, Prepared s c p ∧ interpretation (contextCode s) out =
        base (contextCode s) * OrdinalRightSubtraction.rightSubtract
          (unionInterpretation (logCode p)) (chiNat s p : Ordinal.{0}) := by
  obtain ⟨p, hp, hout⟩ := Part.mem_bind_iff.mp ho
  have hd := (prepare_exact s c p).mp hp
  have hs := LowArithmetic.operation_spec 0 s _ _ out hout
  have hm : interpretation (contextCode s) out =
      interpretation (contextCode s) (baseCode s) * interpretation (contextCode s) (subtractCode s p) :=
    by simpa only [LowArithmetic.ResultSpec, if_pos rfl] using hs.2.2.2.2
  exact ⟨hd.input, hs.2.1, hs.2.2.1, p, hd, by
    rw [hm, (baseCode_spec s).2.2, (subtractCode_spec s c p hd).2.2]⟩

theorem rho_returns (s c : Nat) (hc : inputCheck s c = true) : ∃ out, out ∈ rho s c := by
  obtain ⟨p, hp⟩ := prepare_returns s c hc
  have hd := (prepare_exact s c p).mp hp
  have hi : LowArithmetic.input 0 s (baseCode s) (subtractCode s p) = true := by
    simp only [LowArithmetic.input, beq_self_eq_true, Bool.true_or, Bool.cond_true]
    exact Bool.and_eq_true.mpr ⟨(baseCode_spec s).1, (subtractCode_spec s c p hd).1⟩
  obtain ⟨out, ho, _, _⟩ := LowArithmetic.operation_returns 0 s _ _ hi
  exact ⟨out, Part.mem_bind_iff.mpr ⟨p, hp, ho⟩⟩

theorem rho_domain (s c : Nat) : (rho s c).Dom ↔ inputCheck s c = true := by
  rw [Part.dom_iff_mem]
  exact ⟨fun ⟨out, ho⟩ => (rho_spec s c out ho).1, rho_returns s c⟩

/-- Literal Definition3.11 on the chosen original admitted normal lambda.
The real zero-or-limit condition, finite tail, actual chi and original LOW
output all appear in the conclusion, with no decomposition oracle premise. -/
theorem source_definition_3_11 (s c out : Nat) (ho : out ∈ rho s c) :
    inputCheck s c = true ∧ LowArithmetic.lowInput s out = true ∧
    Comparison.acceptedCode (contextCode s) out = true ∧ ∃ p,
      Prepared s c p ∧
      LogEnd.SourceLogSpec true (interpretation (contextCode s) c) (unionInterpretation (logCode p)) ∧
      LowArithmetic.lowInput s (lambdaCode s p) = true ∧
      Comparison.acceptedCode (contextCode s) (lambdaCode s p) = true ∧
      (interpretation (contextCode s) (lambdaCode s p) = 0 ∨
        _root_.Order.IsSuccLimit (interpretation (contextCode s) (lambdaCode s p))) ∧
      unionInterpretation (logCode p) = interpretation (contextCode s) (lambdaCode s p) + (remainder p : Ordinal.{0}) ∧
      interpretation (contextCode s) out = base (contextCode s) *
        OrdinalRightSubtraction.rightSubtract (unionInterpretation (logCode p)) (chiNat s p : Ordinal.{0}) := by
  obtain ⟨hc, hlo, hno, p, hp, he⟩ := rho_spec s c out ho
  have hl := LogEnd.logend_value _ _ hp.logarithm
  have hu := LowArithmetic.publicCode_spec s c hp.input
  have hr := (prepared_returns s c p hp).2
  refine ⟨hc, hlo, hno, p, hp, ?_, hr.1, hr.2.1, lambda_zero_or_limit s c p hp, ?_, he⟩
  · simpa only [hu.2] using hl.2.2
  · exact (prepared_returns s c p hp).1.2.2.symm.trans (log_split s c p hp)

theorem source_lemma_3_12_bound (s c out : Nat) (ho : out ∈ rho s c) :
    ∃ p, Prepared s c p ∧ interpretation (contextCode s) out ≤
      base (contextCode s) * unionInterpretation (logCode p) := by
  obtain ⟨_, _, _, p, hp, he⟩ := rho_spec s c out ho
  exact ⟨p, hp, he.le.trans (mul_le_mul_right (OrdinalRightSubtraction.rightSubtract_le _ _) _)⟩

theorem subtract_source (s c p : Nat) (hp : Prepared s c p) :
    OrdinalRightSubtraction.SourceSpec (unionInterpretation (logCode p))
      (chiNat s p : Ordinal.{0}) (interpretation (contextCode s) (subtractCode s p)) := by
  rw [(subtractCode_spec s c p hp).2.2]
  exact OrdinalRightSubtraction.rightSubtract_spec _ _

theorem rho_chi_false (s c out p : Nat) (ho : out ∈ rho s c)
    (hp : Prepared s c p) (hchi : chi s p = false) :
    interpretation (contextCode s) out = base (contextCode s) * unionInterpretation (logCode p) := by
  obtain ⟨_, _, _, t, ht, he⟩ := rho_spec s c out ho
  have hpt : p = t := Part.mem_unique ((prepare_exact s c p).mpr hp) ((prepare_exact s c t).mpr ht)
  subst t
  simpa only [chiNat, hchi, Bool.cond_false, Nat.cast_zero, OrdinalRightSubtraction.rightSubtract_zero_right] using he

theorem prepare_value_invariant (s c d p t : Nat)
    (hp : Prepared s c p) (ht : Prepared s d t)
    (hv : interpretation (contextCode s) c = interpretation (contextCode s) d) : p = t := by
  have hc := LowArithmetic.publicCode_spec s c hp.input
  have hd := LowArithmetic.publicCode_spec s d ht.input
  have hl : logCode p = logCode t := LogEnd.componentLog_output_invariant true _ _ _ _
    hp.logarithm ht.logarithm (hc.2.trans (hv.trans hd.2.symm))
  have he : decomposition p = decomposition t :=
    Part.mem_unique hp.data (by rw [hl]; exact ht.data)
  exact Nat.unpair_injective (Prod.ext hl he)

/-- Literal chosen outputs agree for equal input VALUES. Canonical log and
finite-decomposition uniqueness fixes the actual lambda spelling BEFORE chi
is evaluated; no arbitrary chi spelling invariance is used. -/
theorem rho_output_invariant (s c d out out' : Nat)
    (ho : out ∈ rho s c) (ho' : out' ∈ rho s d)
    (hv : interpretation (contextCode s) c = interpretation (contextCode s) d) : out = out' := by
  obtain ⟨p, hp, hs⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨t, ht, hs'⟩ := Part.mem_bind_iff.mp ho'
  have he := prepare_value_invariant s c d p t
    ((prepare_exact s c p).mp hp) ((prepare_exact s d t).mp ht) hv
  subst t
  exact Part.mem_unique hs hs'

private theorem chi_false_of_lambda_zero (s c p : Nat) (hp : Prepared s c p)
    (hz : interpretation (contextCode s) (lambdaCode s p) = 0) : chi s p = false := by
  have hs := (Comparison.acceptedCode_exact _ _).mp (prepared_returns s c p hp).2.2.1
  obtain ⟨t, he, ht⟩ := (checkCode_exact _ _).mp hs.1
  have hn : Comparison.Normal (contextCode s) t := by
    simpa only [← he, ThetaCourse.rawTree_code] using hs.2
  have hv : denote (contextCode s) t = 0 := by simpa only [← he, interpretation_code] using hz
  change SourceChi.chiCode (contextCode s) (lambdaCode s p) = false
  rw [← he]
  exact SourceChi.chiCode_below_base _ t ht hn (by rw [hv]; exact base_pos _ (contextCode_checked s))

theorem rho_zero (s c out : Nat) (ho : out ∈ rho s c)
    (hz : interpretation (contextCode s) c = 0) : interpretation (contextCode s) out = 0 := by
  obtain ⟨_, _, _, p, hp, _⟩ := rho_spec s c out ho
  have hu := LowArithmetic.publicCode_spec s c hp.input
  have hlog : unionInterpretation (logCode p) = 0 := by
    have hl := (LogEnd.logend_value _ _ hp.logarithm).2.2
    simpa only [LogEnd.SourceLogSpec, hu.2, hz, if_pos rfl] using hl
  have hlam : interpretation (contextCode s) (lambdaCode s p) = 0 := by
    rw [(prepared_returns s c p hp).2.2.2]
    exact le_zero_iff.mp (hlog ▸ prepared_prefix_bound s c p hp)
  rw [rho_chi_false s c out p ho hp (chi_false_of_lambda_zero s c p hp hlam), hlog, mul_zero]

private theorem rightSubtract_add_one (g : Ordinal.{0}) :
    OrdinalRightSubtraction.rightSubtract (g + 1) 1 = g := by
  by_cases h : g + 1 ≤ 1
  · have hg : g = 0 := le_zero_iff.mp ((Ordinal.add_le_add_iff_right 1).mp (by simpa only [zero_add, Nat.cast_one] using h))
    rw [OrdinalRightSubtraction.rightSubtract_of_le _ _ h, hg]
  · have hs := OrdinalRightSubtraction.rightSubtract_minimum (g + 1) 1 (lt_of_not_ge h) ⟨g, rfl⟩
    exact ((Ordinal.add_right_cancel 1).mp (by simpa only [Nat.cast_one] using hs.1)).symm

/-- Positive finite remainder: dotted subtraction by chi=1 removes its LAST
successor. The entire lambda+k is passed to dotted subtraction. -/
theorem rho_chi_true_successor (s c out p n : Nat) (ho : out ∈ rho s c)
    (hp : Prepared s c p) (hchi : chi s p = true) (hk : remainder p = n + 1) :
    interpretation (contextCode s) out = base (contextCode s) *
      (interpretation (contextCode s) (lambdaCode s p) + (n : Ordinal.{0})) := by
  obtain ⟨_, _, _, t, ht, he⟩ := rho_spec s c out ho
  have hpt := Part.mem_unique ((prepare_exact s c p).mpr hp) ((prepare_exact s c t).mpr ht)
  subst t
  have hl := (prepared_returns s c p hp).1.2.2.symm.trans (log_split s c p hp)
  rw [he, hl, hk]
  simp only [chiNat, hchi, Bool.cond_true, Nat.cast_one]
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc, rightSubtract_add_one]

/-- If chi=1 and the natural remainder is zero, lambda is a genuine
NONZERO limit. No ordinal g satisfies lambda=g+1, so the dotted source
operation returns the entire limit rather than a fictitious predecessor. -/
theorem rho_chi_true_limit (s c out p : Nat) (ho : out ∈ rho s c)
    (hp : Prepared s c p) (hchi : chi s p = true) (hk : remainder p = 0) :
    _root_.Order.IsSuccLimit (interpretation (contextCode s) (lambdaCode s p)) ∧
      interpretation (contextCode s) out = base (contextCode s) *
        interpretation (contextCode s) (lambdaCode s p) := by
  have hlim : _root_.Order.IsSuccLimit (interpretation (contextCode s) (lambdaCode s p)) := by
    rcases lambda_zero_or_limit s c p hp with hz | hl
    · exact False.elim (Bool.noConfusion ((chi_false_of_lambda_zero s c p hp hz).symm.trans hchi))
    · exact hl
  obtain ⟨_, _, _, t, ht, he⟩ := rho_spec s c out ho
  have hpt := Part.mem_unique ((prepare_exact s c p).mpr hp) ((prepare_exact s c t).mpr ht)
  subst t
  have hl : unionInterpretation (logCode p) = interpretation (contextCode s) (lambdaCode s p) := by
    simpa only [hk, Nat.cast_zero, add_zero] using
      (prepared_returns s c p hp).1.2.2.symm.trans (log_split s c p hp)
  refine ⟨hlim, ?_⟩
  rw [he, hl]
  simp only [chiNat, hchi, Bool.cond_true, Nat.cast_one]
  rw [OrdinalRightSubtraction.rightSubtract_no_solution _ _ (Ordinal.one_lt_of_isSuccLimit hlim)
    (fun g heq => hlim.succ_ne g (by simpa only [Ordinal.succ_eq_add_one] using heq.symm))]

/-- Actual same-context chi value invariance makes the selected lambda
representative interchangeable with EVERY original admitted normal expression
of its value. This uses the derived source theorem, not a spelling oracle. -/
theorem chiNat_any_lambda (s c p ell : Nat) (hp : Prepared s c p)
    (hell : SourceChi.inputCheck (contextCode s) ell = true)
    (hv : interpretation (contextCode s) ell = interpretation (contextCode s) (lambdaCode s p)) :
    chiNat s p = cond (SourceChi.chiCode (contextCode s) ell) 1 0 := by
  have hs := (Comparison.acceptedCode_exact _ _).mp (prepared_returns s c p hp).2.2.1
  have hsel := (SourceChi.inputCheck_exact _ _).mpr hs
  have he := SourceChi.Invariance.chiCode_invariant (contextCode s) (lambdaCode s p) ell hsel hell hv.symm
  simp only [chiNat, chi, he]

theorem rho_formula_any_lambda (s c out p ell : Nat) (ho : out ∈ rho s c)
    (hp : Prepared s c p) (hell : SourceChi.inputCheck (contextCode s) ell = true)
    (hv : interpretation (contextCode s) ell = interpretation (contextCode s) (lambdaCode s p)) :
    interpretation (contextCode s) out = base (contextCode s) * OrdinalRightSubtraction.rightSubtract
      (interpretation (contextCode s) ell + (remainder p : Ordinal.{0}))
      ((cond (SourceChi.chiCode (contextCode s) ell) 1 0 : Nat) : Ordinal.{0}) := by
  obtain ⟨_, _, _, t, ht, he⟩ := rho_spec s c out ho
  have hpt := Part.mem_unique ((prepare_exact s c p).mpr hp) ((prepare_exact s c t).mpr ht)
  subst t
  have hl := (prepared_returns s c p hp).1.2.2.symm.trans (log_split s c p hp)
  rw [he, hl, ← hv, chiNat_any_lambda s c p ell hp hell hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho
