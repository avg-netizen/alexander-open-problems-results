import Alexander313.Wilken.HereditaryNativeFiniteTailDecomposition
import Alexander313.Wilken.HereditaryNativeBaseLeftMultiplication
import Alexander313.Wilken.HereditaryNativeRightSubtraction
import Alexander313.Wilken.HereditaryNativeSourceRhoHeight

/-!
# Actual source rho at every coded epsilon base

The genuine native last-log routine acts on every original RAW LOW input.
Its actual normalized principal word computes lambda+k with lambda zero or
proper limit. Source chi is evaluated on that genuinely admitted lambda;
dotted RIGHT subtraction acts on the entire last logarithm. Genuine base-left
multiplication constructs the result. Original source3.11, zero, source3.12
bound and written/canonical heights are derived without an output, height,
logarithm, finite-decomposition or arithmetic oracle. The old positive-public
rho execution is proved to have the SAME value using actual source lambda
and last-log uniqueness. The printed domain is epsilon bases, excluding one.
Source-only uncompiled candidates; source3.10 is not proved here.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform

open ThetaCourse

def chiNat (q ell : Nat) : Nat :=
  cond (SourceChi.chiCode q (FiniteTailDecomposition.lambdaCode q ell)) 1 0

def chiCode (q ell : Nat) : Nat := OmegaPowerHeight.numeralCode (chiNat q ell)

def reducedCode (q ell : Nat) : Nat := RightSubtraction.rightCode q ell (chiCode q ell)

theorem chiNat_primrec : Primrec₂ chiNat :=
  ((SourceChi.chiCode_primrec.comp Primrec.fst FiniteTailDecomposition.lambdaCode_primrec).cond
    (Primrec.const 1) (Primrec.const 0)).to₂

theorem chiCode_primrec : Primrec₂ chiCode := OmegaPowerHeight.numeralCode_primrec.comp₂ chiNat_primrec

theorem reducedCode_primrec : Primrec₂ reducedCode :=
  (RightSubtraction.rightCode_primrec.comp (Primrec.fst.pair (Primrec.snd.pair chiCode_primrec))).to₂

theorem chiCode_spec (q ell : Nat) (hell : lowCheckCode q ell = true) :
    lowCheckCode q (chiCode q ell) = true ∧ Comparison.acceptedCode q (chiCode q ell) = true ∧
      interpretation q (chiCode q ell) = (chiNat q ell : Ordinal.{0}) := by
  have hs := OmegaPowerHeight.numeralCode_spec q (chiNat q ell)
    (HeightBoundary.input_spec q ell hell).2.1
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-- The selected lambda uses the actual original source indicator,
with both its checker and its Normal caller constructed from the input. -/
theorem lambda_chi_correct (q ell : Nat) (hell : lowCheckCode q ell = true) :
    SourceChi.chiCode q (FiniteTailDecomposition.lambdaCode q ell) =
      SourceChi.indicator q (FiniteTailDecomposition.limitTerm q ell) := by
  have hs := (FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp hell).1).1
  have ht := (Comparison.acceptedCode_exact q _).mp hs
  apply SourceChi.chiCode_correct q _
  · simpa only [FiniteTailDecomposition.lambdaCode, checkCode_code] using ht.1
  · simpa only [FiniteTailDecomposition.lambdaCode, ThetaCourse.rawTree_code] using ht.2

theorem reducedCode_spec (q ell : Nat) (hell : lowCheckCode q ell = true) :
    lowCheckCode q (reducedCode q ell) = true ∧
      Comparison.acceptedCode q (reducedCode q ell) = true ∧
      interpretation q (reducedCode q ell) =
        OrdinalRightSubtraction.rightSubtract (interpretation q ell) (chiNat q ell : Ordinal.{0}) := by
  have hi := HeightBoundary.input_spec q ell hell
  have hc := chiCode_spec q ell hell
  have hchi := ((Comparison.acceptedCode_exact q _).mp hc.2.1).1
  have hs := RightSubtraction.rightCode_spec q ell (chiCode q ell) hi.1 hchi
  have hb := RightSubtraction.rightCode_le q ell (chiCode q ell) hi.1 hchi
  refine ⟨OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp hs.1).1
    (hb.trans_lt hi.2.2), hs.1, ?_⟩
  simpa only [reducedCode, hc.2.2] using hs.2.1

def finish (q ell : Nat) : Part Nat := BaseLeftMultiplication.execute q (reducedCode q ell)

theorem finish_partrec : Partrec₂ finish :=
  (BaseLeftMultiplication.execute_partrec.comp Computable.fst reducedCode_primrec.to_comp).to₂

def execute (q c : Nat) : Part Nat := (LogEnd.execute q c).bind (finish q)

theorem execute_partrec : Partrec₂ execute := by
  have hf : Partrec₂ (fun p : Nat × Nat => fun ell : Nat => finish p.1 ell) :=
    (finish_partrec.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  exact (LogEnd.execute_partrec.bind hf).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ lowCheckCode q c = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨ell, hl, hm⟩ := Part.mem_bind_iff.mp ho
    exact (LogEnd.execute_spec q c ell hl).1
  · intro hc
    obtain ⟨ell, hl⟩ := Part.dom_iff_mem.mp ((LogEnd.execute_domain q c).mpr hc)
    have hell := (LogEnd.execute_spec q c ell hl).2.1
    have hr := (reducedCode_spec q ell hell).1
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((BaseLeftMultiplication.execute_domain q _).mpr hr)
    exact Part.dom_iff_mem.mpr ⟨out, Part.mem_bind_iff.mpr ⟨ell, hl, ho⟩⟩

/-- The actual ANY-epsilon execution constructs the literal original
source Definition3.11 on every ORIGINAL RAW LOW input. -/
theorem source_definition_3_11 (q c out : Nat) (ho : out ∈ execute q c) :
    lowCheckCode q c = true ∧ lowCheckCode q out = true ∧
      Comparison.acceptedCode q out = true ∧ ∃ ell,
      ell ∈ LogEnd.execute q c ∧
      lowCheckCode q (FiniteTailDecomposition.lambdaCode q ell) = true ∧
      Comparison.acceptedCode q (FiniteTailDecomposition.lambdaCode q ell) = true ∧
      (interpretation q (FiniteTailDecomposition.lambdaCode q ell) = 0 ∨
        IsSuccLimit (interpretation q (FiniteTailDecomposition.lambdaCode q ell))) ∧
      interpretation q ell = interpretation q (FiniteTailDecomposition.lambdaCode q ell) +
        (FiniteTailDecomposition.offset q ell : Ordinal.{0}) ∧
      Hereditary.LogEnd.SourceLogSpec true (interpretation q c) (interpretation q ell) ∧
      interpretation q out = base q * OrdinalRightSubtraction.rightSubtract
        (interpretation q ell) (chiNat q ell : Ordinal.{0}) := by
  obtain ⟨ell, hl, hm⟩ := Part.mem_bind_iff.mp ho
  have hs := LogEnd.execute_spec q c ell hl
  have ht := FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp hs.2.1).1
  have hp := BaseLeftMultiplication.execute_spec q _ out hm
  have hr := reducedCode_spec q ell hs.2.1
  refine ⟨hs.1, hp.2.1, hp.2.2.1, ell, hl,
    FiniteTailDecomposition.lambdaCode_low q ell hs.2.1, ht.1, ht.2.1,
    ht.2.2, hs.2.2.2, ?_⟩
  exact hp.2.2.2.trans (congrArg (fun a => base q * a) hr.2.2)

theorem execute_formula (q c out ell : Nat) (ho : out ∈ execute q c)
    (hl : ell ∈ LogEnd.execute q c) :
    interpretation q out = base q * OrdinalRightSubtraction.rightSubtract
      (interpretation q ell) (chiNat q ell : Ordinal.{0}) := by
  obtain ⟨_, _, _, actual, ha, _, _, _, _, _, he⟩ := source_definition_3_11 q c out ho
  have heq := Part.mem_unique hl ha
  subst actual
  exact he

theorem execute_zero (q c out : Nat) (ho : out ∈ execute q c)
    (hz : interpretation q c = 0) : interpretation q out = 0 := by
  obtain ⟨ell, hl, hm⟩ := Part.mem_bind_iff.mp ho
  have hs := LogEnd.execute_spec q c ell hl
  have hzero : interpretation q ell = 0 := by
    simpa only [Hereditary.LogEnd.SourceLogSpec, hz, if_pos rfl] using hs.2.2.2
  rw [execute_formula q c out ell ho hl, hzero,
    OrdinalRightSubtraction.rightSubtract_of_le _ _ bot_le, mul_zero]

/-- The printed rho<=base*logend bound uses the actual executing log
output and genuine dotted RIGHT subtraction. -/
theorem source_lemma_3_12_bound (q c out ell : Nat) (ho : out ∈ execute q c)
    (hl : ell ∈ LogEnd.execute q c) :
    interpretation q out ≤ base q * interpretation q ell := by
  rw [execute_formula q c out ell ho hl]
  exact mul_le_mul_right (OrdinalRightSubtraction.rightSubtract_le _ _) _

/-- The actual written result satisfies the printed height bound on
EVERY original RAW LOW input at every coded epsilon, including input zero. -/
theorem source_lemma_3_12_height (q c out : Nat) (ho : out ∈ execute q c) :
    heightCode out ≤ max 1 (CanonicalHeight.canonicalHeightCode q c) := by
  obtain ⟨hc, hout, hn, ell, hl, _, _, _, _, _, _⟩ := source_definition_3_11 q c out ho
  have hi := HeightBoundary.input_spec q c hc
  let n := max 1 (CanonicalHeight.canonicalHeightCode q c)
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
  have hbase := HeightBoundary.base_lt_endpoint q n hi.2.1 hnpos
  have hinput := (HeightBoundary.canonicalHeightCode_le_iff_endpoint q n c hc).mp (le_max_right _ _)
  have hlog := (LogEnd.execute_bound q c ell hl).trans_lt hinput
  have hmul := HeightBoundary.endpoint_mul_closed q n hi.2.1 hnpos hbase hlog
  have hb := (source_lemma_3_12_bound q c out ell ho hl).trans_lt hmul
  have hh := (HeightBoundary.canonicalHeightCode_le_iff_endpoint q n out hout).mpr hb
  rw [CanonicalHeight.canonicalHeightCode_normal q out hn] at hh
  exact hh

theorem source_lemma_3_12_canonical_height (q c out : Nat) (ho : out ∈ execute q c) :
    CanonicalHeight.canonicalHeightCode q out ≤ max 1 (CanonicalHeight.canonicalHeightCode q c) := by
  obtain ⟨_, _, hn, _⟩ := source_definition_3_11 q c out ho
  rw [CanonicalHeight.canonicalHeightCode_normal q out hn]
  exact source_lemma_3_12_height q c out ho

theorem source_lemma_3_12_normal_height (q c out : Nat) (ho : out ∈ execute q c)
    (hn : Comparison.acceptedCode q c = true) :
    heightCode out ≤ max 1 (heightCode c) := by
  simpa only [CanonicalHeight.canonicalHeightCode_normal q c hn] using
    source_lemma_3_12_height q c out ho

private theorem log_value_unique (alpha x y : Ordinal.{0})
    (hx : Hereditary.LogEnd.SourceLogSpec true alpha x)
    (hy : Hereditary.LogEnd.SourceLogSpec true alpha y) : x = y := by
  by_cases hz : alpha = 0
  · have hx0 : x = 0 := by simpa only [Hereditary.LogEnd.SourceLogSpec, if_pos hz] using hx
    have hy0 : y = 0 := by simpa only [Hereditary.LogEnd.SourceLogSpec, if_pos hz] using hy
    exact hx0.trans hy0.symm
  · apply omegaPower_strictMono.injective
    exact (show Ordinal.omega0 ^ x = Hereditary.LogEnd.componentValue true alpha by
      simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz] using hx).trans
      (show Ordinal.omega0 ^ y = Hereditary.LogEnd.componentValue true alpha by
        simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz] using hy).symm

/-- The uniform native producer agrees in VALUE with the existing real
positive-public source rho execution; finite-tail and chi representatives
are identified by genuine uniqueness and same-base source chi invariance. -/
theorem positive_public_source_fidelity (s c out old : Nat)
    (ho : out ∈ execute (NativePublicBridge.contextCode s) c)
    (hp : old ∈ SourceRho.rho s c) :
    interpretation (NativePublicBridge.contextCode s) out =
      interpretation (NativePublicBridge.contextCode s) old := by
  let q := NativePublicBridge.contextCode s
  obtain ⟨ell, hl, hm⟩ := Part.mem_bind_iff.mp ho
  have hlog := LogEnd.execute_spec q c ell hl
  obtain ⟨_, _, _, p, hprep, hold⟩ := SourceRho.rho_spec s c old hp
  have hpub := Hereditary.LogEnd.logend_value _ _ hprep.logarithm
  have hin := LowArithmetic.publicCode_spec s c hprep.input
  have hlogold : Hereditary.LogEnd.SourceLogSpec true (interpretation q c)
      (unionInterpretation (SourceRho.logCode p)) := by
    simpa only [hin.2] using hpub.2.2
  have he := log_value_unique _ _ _ hlog.2.2.2 hlogold
  have htail := FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp hlog.2.1).1
  have hret := (SourceRho.prepared_returns s c p hprep).2
  have hsplit := (SourceRho.prepared_returns s c p hprep).1.2.2.symm.trans
    (SourceRho.log_split s c p hprep)
  have hu := LimitFiniteDecomposition.coefficient_unique _ _ _ _ htail.2.1
    (SourceRho.lambda_zero_or_limit s c p hprep)
    (htail.2.2.symm.trans (he.trans hsplit))
  have hchi := (SourceChi.inputCheck_exact q _).mpr
    ((Comparison.acceptedCode_exact q _).mp htail.1)
  have hformula := SourceRho.rho_formula_any_lambda s c old p
    (FiniteTailDecomposition.lambdaCode q ell) hp hprep hchi hu.1
  rw [execute_formula q c out ell ho hl, hformula]
  rw [← hu.2, ← htail.2.2]
  rfl

/-- Same-base input value invariance is derived from real last-log,
finite-tail and source chi invariance, without identifying source spellings. -/
theorem execute_value_invariant (q c d out other : Nat) (ho : out ∈ execute q c)
    (hp : other ∈ execute q d) (he : interpretation q c = interpretation q d) :
    interpretation q out = interpretation q other := by
  obtain ⟨ell, hl, _⟩ := Part.mem_bind_iff.mp ho
  obtain ⟨last, ht, _⟩ := Part.mem_bind_iff.mp hp
  have hs := LogEnd.execute_spec q c ell hl
  have hv := LogEnd.execute_spec q d last ht
  have hlog := LogEnd.execute_value_invariant q c q d ell last hl ht he
  have hu := FiniteTailDecomposition.decomposition_value_invariant q ell last
    (Bool.and_eq_true.mp hs.2.1).1 (Bool.and_eq_true.mp hv.2.1).1 hlog
  have hc := FiniteTailDecomposition.lambdaCode_spec q ell (Bool.and_eq_true.mp hs.2.1).1
  have hd := FiniteTailDecomposition.lambdaCode_spec q last (Bool.and_eq_true.mp hv.2.1).1
  have hchi := SourceChi.Invariance.chiCode_invariant q _ _
    ((SourceChi.inputCheck_exact q _).mpr ((Comparison.acceptedCode_exact q _).mp hc.1))
    ((SourceChi.inputCheck_exact q _).mpr ((Comparison.acceptedCode_exact q _).mp hd.1)) hu.1
  rw [execute_formula q c out ell ho hl, execute_formula q d other last hp ht]
  simp only [chiNat, hchi, hlog]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform
